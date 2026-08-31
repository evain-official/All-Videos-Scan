// AllVideosScan — Go media scanner & analyzer
// Original Python tool by 8-Programmers'; Go rewrite, optimized & stabilized.
//
// Build:  go build -o allvideoscan allvideoscan.go
// Run:    ./allvideoscan [flags]
//
// Highlights:
//   • Single-pass ffprobe call per file (duration + video/audio codec) — ~2x fewer exec spawns
//   • Corrupted-file detection (unreadable / unprobeable / zero-duration flagged separately)
//   • Biggest / smallest file by size and by duration (corrupted & 0-dur excluded from "smallest")
//   • Video & audio encoder (codec) breakdown tables
//   • Graceful Ctrl+C handling — prints partial results instead of dying mid-scan
//   • Retry logic for transient ffprobe failures
//   • --exclude glob patterns, --follow-symlinks, --quiet, --no-color, --top N
//   • --dedupe: detect duplicate files by size+partial hash
//   • --log file for a plain-text run log
//   • Panic-safe workers (a single bad file can't crash the whole scan)
//   • Real-time animated progress bar with ETA
//   • JSON / CSV export
//   • Cross-platform (Windows / macOS / Linux), zero external Go dependencies

package main

import (
	"bufio"
	"context"
	"crypto/sha256"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

// ─── Version ────────────────────────────────────────────────────────────────

const version = "2.0.0"

// ─── Media extension sets ────────────────────────────────────────────────────

var videoExtensions = map[string]struct{}{
	".mp4": {}, ".mkv": {}, ".avi": {}, ".mov": {}, ".wmv": {},
	".flv": {}, ".webm": {}, ".3gp": {}, ".m4v": {}, ".mpg": {},
	".mpeg": {}, ".m2v": {}, ".vob": {}, ".ogv": {}, ".f4v": {},
	".rmvb": {}, ".mts": {}, ".m2ts": {}, ".ts": {}, ".divx": {},
}

var audioExtensions = map[string]struct{}{
	".mp3": {}, ".flac": {}, ".wav": {}, ".aac": {}, ".ogg": {},
	".wma": {}, ".m4a": {}, ".opus": {}, ".ape": {}, ".alac": {},
	".aiff": {}, ".au": {}, ".mid": {}, ".midi": {},
}

// Directories to skip during traversal.
var skipDirs = map[string]struct{}{
	"windows": {}, "program files": {}, "program files (x86)": {},
	"$recycle.bin": {}, "appdata": {}, "system volume information": {},
	"recovery": {}, "programdata": {}, "perflogs": {}, "boot": {},
	"msocache": {}, "system32": {}, "syswow64": {}, "winsxs": {},
	"$windows.~bt": {}, "$windows.~ws": {}, "node_modules": {},
	".git": {}, "__pycache__": {}, ".venv": {}, "venv": {}, "env": {},
	".cache": {}, "temp": {}, "tmp": {},
}

// ─── Data types ──────────────────────────────────────────────────────────────

// MediaFile holds metadata for a single discovered media file.
type MediaFile struct {
	Path       string  `json:"path"`
	SizeBytes  int64   `json:"size_bytes"`
	Format     string  `json:"format"`
	Duration   float64 `json:"duration_seconds"` // 0 if probe failed / not attempted
	ProbedOK   bool    `json:"probed_ok"`
	Corrupted  bool    `json:"corrupted"`
	Type       string  `json:"type"` // "video" | "audio"
	VideoCodec string  `json:"video_codec,omitempty"`
	AudioCodec string  `json:"audio_codec,omitempty"`
	PartialSum string  `json:"partial_sha256,omitempty"`
}

// ─── ANSI colours ────────────────────────────────────────────────────────────

var (
	colReset  = "\033[0m"
	colCyan   = "\033[96m"
	colGreen  = "\033[92m"
	colYellow = "\033[93m"
	colRed    = "\033[91m"
	colWhite  = "\033[97m"
	colGray   = "\033[90m"
	colBold   = "\033[1m"
)

func disableColor() {
	colReset, colCyan, colGreen, colYellow = "", "", "", ""
	colRed, colWhite, colGray, colBold = "", "", "", ""
}

func c(col, s string) string { return col + s + colReset }

// ─── Formatting helpers ──────────────────────────────────────────────────────

// fmtFloat comma-formats a float with the given decimal places (Go has no %,).
func fmtFloat(f float64, dec int) string {
	s := strconv.FormatFloat(f, 'f', dec, 64)
	dot := strings.Index(s, ".")
	if dot < 0 {
		dot = len(s)
	}
	intPart := s[:dot]
	fracPart := s[dot:]
	neg := strings.HasPrefix(intPart, "-")
	if neg {
		intPart = intPart[1:]
	}
	var out []byte
	for i, ch := range intPart {
		if i > 0 && (len(intPart)-i)%3 == 0 {
			out = append(out, ',')
		}
		out = append(out, byte(ch))
	}
	res := string(out) + fracPart
	if neg {
		res = "-" + res
	}
	return res
}

func bytesToHuman(n int64) string {
	if n == 0 {
		return "0.00 B"
	}
	units := []string{"B", "KB", "MB", "GB", "TB", "PB"}
	f := float64(n)
	for _, u := range units {
		if math.Abs(f) < 1024 {
			return fmt.Sprintf("%s %s", fmtFloat(f, 2), u)
		}
		f /= 1024
	}
	return fmt.Sprintf("%s EB", fmtFloat(f, 2))
}

func secondsToHMS(sec float64) string {
	if sec <= 0 {
		return "00h 00m 00s"
	}
	h := int(sec) / 3600
	m := (int(sec) % 3600) / 60
	s := int(sec) % 60
	return fmt.Sprintf("%02dh %02dm %02ds", h, m, s)
}

func truncPath(p string, max int) string {
	if len(p) <= max {
		return p
	}
	if max < 4 {
		return p[:max]
	}
	return "…" + p[len(p)-(max-1):]
}

// ─── Drive discovery ─────────────────────────────────────────────────────────

func getAllDrives() []string {
	if runtime.GOOS == "windows" {
		var drives []string
		for ch := 'A'; ch <= 'Z'; ch++ {
			d := string(ch) + `:\`
			if _, err := os.Stat(d); err == nil {
				drives = append(drives, d)
			}
		}
		return drives
	}
	return []string{"/"}
}

// ─── File discovery ──────────────────────────────────────────────────────────

func shouldSkip(name string) bool {
	lower := strings.ToLower(name)
	if _, ok := skipDirs[lower]; ok {
		return true
	}
	return strings.HasPrefix(name, "$") || strings.HasPrefix(name, ".")
}

func matchAny(patterns []string, name, full string) bool {
	for _, p := range patterns {
		if ok, _ := filepath.Match(p, name); ok {
			return true
		}
		if ok, _ := filepath.Match(p, full); ok {
			return true
		}
	}
	return false
}

func discoverFiles(ctx context.Context, roots []string, exts map[string]struct{}, recurse, followSymlinks bool, excludes []string) []string {
	var mu sync.Mutex
	var files []string

	walkFn := func(path string, d os.DirEntry, err error) error {
		select {
		case <-ctx.Done():
			return filepath.SkipAll
		default:
		}
		if err != nil {
			if d != nil && d.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		if d.IsDir() {
			if d.Name() != filepath.Base(path) && shouldSkip(d.Name()) {
				return filepath.SkipDir
			}
			if len(excludes) > 0 && matchAny(excludes, d.Name(), path) {
				return filepath.SkipDir
			}
			return nil
		}
		if d.Type()&os.ModeSymlink != 0 && !followSymlinks {
			return nil
		}
		ext := strings.ToLower(filepath.Ext(d.Name()))
		if _, ok := exts[ext]; !ok {
			return nil
		}
		if len(excludes) > 0 && matchAny(excludes, d.Name(), path) {
			return nil
		}
		mu.Lock()
		files = append(files, path)
		mu.Unlock()
		return nil
	}

	for _, root := range roots {
		if recurse {
			_ = filepath.WalkDir(root, walkFn)
		} else {
			entries, err := os.ReadDir(root)
			if err != nil {
				continue
			}
			for _, e := range entries {
				if e.IsDir() {
					continue
				}
				ext := strings.ToLower(filepath.Ext(e.Name()))
				if _, ok := exts[ext]; !ok {
					continue
				}
				full := filepath.Join(root, e.Name())
				if len(excludes) > 0 && matchAny(excludes, e.Name(), full) {
					continue
				}
				files = append(files, full)
			}
		}
	}
	return files
}

// ─── ffprobe integration ─────────────────────────────────────────────────────

var ffprobeAvailable bool

func checkFFprobe() bool {
	_, err := exec.LookPath("ffprobe")
	return err == nil
}

type ffprobeStream struct {
	CodecType string `json:"codec_type"`
	CodecName string `json:"codec_name"`
}
type ffprobeFormat struct {
	Duration string `json:"duration"`
}
type ffprobeOutput struct {
	Streams []ffprobeStream `json:"streams"`
	Format  ffprobeFormat   `json:"format"`
}

// probeFile does a single ffprobe invocation returning duration + codecs.
func probeFile(ctx context.Context, path string, timeout time.Duration, retries int) (dur float64, vCodec, aCodec string, ok bool) {
	if !ffprobeAvailable {
		return 0, "", "", false
	}
	var lastErr error
	for attempt := 0; attempt <= retries; attempt++ {
		cctx, cancel := context.WithTimeout(ctx, timeout)
		cmd := exec.CommandContext(cctx, "ffprobe",
			"-v", "error",
			"-show_entries", "format=duration:stream=codec_type,codec_name",
			"-of", "json",
			path,
		)
		out, err := cmd.Output()
		cancel()
		if err != nil {
			lastErr = err
			continue
		}
		var parsed ffprobeOutput
		if jerr := json.Unmarshal(out, &parsed); jerr != nil {
			lastErr = jerr
			continue
		}
		if d, perr := strconv.ParseFloat(strings.TrimSpace(parsed.Format.Duration), 64); perr == nil {
			dur = d
		}
		for _, s := range parsed.Streams {
			switch s.CodecType {
			case "video":
				if vCodec == "" {
					vCodec = s.CodecName
				}
			case "audio":
				if aCodec == "" {
					aCodec = s.CodecName
				}
			}
		}
		return dur, vCodec, aCodec, true
	}
	_ = lastErr
	return 0, "", "", false
}

// ─── Hashing (dedupe support) ─────────────────────────────────────────────────

// partialHash hashes up to maxBytes from the start of the file — fast fingerprint,
// not a full checksum, used only to bucket likely duplicates.
func partialHash(path string, maxBytes int64) string {
	f, err := os.Open(path)
	if err != nil {
		return ""
	}
	defer f.Close()
	h := sha256.New()
	_, _ = io.CopyN(h, f, maxBytes)
	return hex.EncodeToString(h.Sum(nil))[:16]
}

// ─── Parallel processing ─────────────────────────────────────────────────────

type scanConfig struct {
	probeEnabled bool
	probeTimeout time.Duration
	probeRetries int
	dedupe       bool
}

func processFile(ctx context.Context, path string, cfg scanConfig) (mf MediaFile) {
	defer func() {
		if r := recover(); r != nil {
			mf = MediaFile{Path: path, Corrupted: true}
		}
	}()

	ext := strings.ToLower(filepath.Ext(path))
	mediaType := "video"
	if _, ok := audioExtensions[ext]; ok {
		mediaType = "audio"
	}

	info, err := os.Stat(path)
	var sizeBytes int64
	statOK := err == nil
	if statOK {
		sizeBytes = info.Size()
	}

	var dur float64
	var vCodec, aCodec string
	var probed bool
	if cfg.probeEnabled {
		dur, vCodec, aCodec, probed = probeFile(ctx, path, cfg.probeTimeout, cfg.probeRetries)
	}

	corrupted := !statOK || (cfg.probeEnabled && !probed)

	var sum string
	if cfg.dedupe && statOK {
		sum = partialHash(path, 1<<16) // first 64KB
	}

	return MediaFile{
		Path:       path,
		SizeBytes:  sizeBytes,
		Format:     ext,
		Duration:   dur,
		ProbedOK:   probed,
		Corrupted:  corrupted,
		Type:       mediaType,
		VideoCodec: vCodec,
		AudioCodec: aCodec,
		PartialSum: sum,
	}
}

// ─── Progress bar ────────────────────────────────────────────────────────────

const barWidth = 36

func renderBar(done, total int64, start time.Time) string {
	if total == 0 {
		return ""
	}
	pct := float64(done) / float64(total)
	filled := int(pct * barWidth)
	if filled > barWidth {
		filled = barWidth
	}
	bar := strings.Repeat("█", filled) + strings.Repeat("░", barWidth-filled)
	elapsed := time.Since(start).Seconds()
	eta := "–"
	if done > 0 && elapsed > 0 {
		rate := float64(done) / elapsed
		if rate > 0 {
			remain := float64(total-done) / rate
			eta = fmt.Sprintf("%.0fs", remain)
		}
	}
	return fmt.Sprintf("[%s] %d/%d (%.1f%%) ETA %s", bar, done, total, pct*100, eta)
}

// ─── Statistics helpers ───────────────────────────────────────────────────────

type formatStat struct {
	Format    string
	Count     int
	TotalSize int64
	TotalDur  float64
}

type codecStat struct {
	Codec string
	Count int
}

func buildStats(files []MediaFile) (formats map[string]*formatStat, videoCodecs, audioCodecs map[string]int, totalSize int64, totalDur float64) {
	formats = make(map[string]*formatStat)
	videoCodecs = make(map[string]int)
	audioCodecs = make(map[string]int)

	for _, f := range files {
		totalSize += f.SizeBytes
		if f.ProbedOK {
			totalDur += f.Duration
		}
		s, ok := formats[f.Format]
		if !ok {
			s = &formatStat{Format: f.Format}
			formats[f.Format] = s
		}
		s.Count++
		s.TotalSize += f.SizeBytes
		if f.ProbedOK {
			s.TotalDur += f.Duration
		}
		if f.VideoCodec != "" {
			videoCodecs[f.VideoCodec]++
		}
		if f.AudioCodec != "" {
			audioCodecs[f.AudioCodec]++
		}
	}
	return
}

func sortedFormatStats(stats map[string]*formatStat) []*formatStat {
	list := make([]*formatStat, 0, len(stats))
	for _, v := range stats {
		list = append(list, v)
	}
	sort.Slice(list, func(i, j int) bool { return list[i].TotalSize > list[j].TotalSize })
	return list
}

func sortedCodecStats(m map[string]int) []codecStat {
	list := make([]codecStat, 0, len(m))
	for k, v := range m {
		list = append(list, codecStat{Codec: k, Count: v})
	}
	sort.Slice(list, func(i, j int) bool { return list[i].Count > list[j].Count })
	return list
}

func mean(files []MediaFile) (sizeMean, durMean float64) {
	if len(files) == 0 {
		return 0, 0
	}
	var sSum, dSum float64
	var dCount int
	for _, f := range files {
		sSum += float64(f.SizeBytes)
		if f.ProbedOK {
			dSum += f.Duration
			dCount++
		}
	}
	if dCount > 0 {
		durMean = dSum / float64(dCount)
	}
	return sSum / float64(len(files)), durMean
}

// biggestSmallest finds extremes by size and duration.
// "Smallest" excludes corrupted files and files with 0 duration, per spec.
func biggestSmallest(files []MediaFile) (biggestSize, smallestSize, biggestDur, smallestDur *MediaFile) {
	for i := range files {
		f := &files[i]
		if biggestSize == nil || f.SizeBytes > biggestSize.SizeBytes {
			biggestSize = f
		}
		if !f.Corrupted && f.Duration > 0 {
			if smallestSize == nil || f.SizeBytes < smallestSize.SizeBytes {
				smallestSize = f
			}
			if smallestDur == nil || f.Duration < smallestDur.Duration {
				smallestDur = f
			}
		}
		if f.ProbedOK && (biggestDur == nil || f.Duration > biggestDur.Duration) {
			biggestDur = f
		}
	}
	return
}

// ─── Export helpers ──────────────────────────────────────────────────────────

func exportJSON(files []MediaFile, outPath string) error {
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	enc := json.NewEncoder(f)
	enc.SetIndent("", "  ")
	return enc.Encode(files)
}

func exportCSV(files []MediaFile, outPath string) error {
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	w := csv.NewWriter(f)
	_ = w.Write([]string{"path", "type", "format", "size_bytes", "duration_seconds", "probed_ok", "corrupted", "video_codec", "audio_codec"})
	for _, mf := range files {
		_ = w.Write([]string{
			mf.Path,
			mf.Type,
			mf.Format,
			strconv.FormatInt(mf.SizeBytes, 10),
			strconv.FormatFloat(mf.Duration, 'f', 3, 64),
			strconv.FormatBool(mf.ProbedOK),
			strconv.FormatBool(mf.Corrupted),
			mf.VideoCodec,
			mf.AudioCodec,
		})
	}
	w.Flush()
	return w.Error()
}

func exportLog(path, content string) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := bufio.NewWriter(f)
	_, _ = w.WriteString(content)
	return w.Flush()
}

// ─── Generics-free min/max helpers ────────────────────────────────────────────

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

// ─── Main ────────────────────────────────────────────────────────────────────

func main() {
	// ── Flags ──────────────────────────────────────────────────────────────
	showVersion := flag.Bool("version", false, "Print version and exit")
	flag.BoolVar(showVersion, "v", false, "Print version and exit (shorthand)")

	scanCWD := flag.Bool("cwd", true, "Scan current working directory (default true)")
	scanAll := flag.Bool("all-drives", false, "Scan all drives / filesystem root")
	scanHome := flag.Bool("home", false, "Scan user home directory subtrees")
	customPath := flag.String("path", "", "Scan a specific directory path")

	includeAudio := flag.Bool("audio", false, "Include audio files in scan")
	noRecurse := flag.Bool("no-recurse", false, "Flat scan — do not descend into subdirectories")
	extraExts := flag.String("ext", "", "Extra extensions to include, comma-separated (e.g. .ts,.m2ts)")
	excludeList := flag.String("exclude", "", "Comma-separated glob patterns to exclude (name or full path)")
	followSymlinks := flag.Bool("follow-symlinks", false, "Follow symlinked files during scan")

	workers := flag.Int("workers", min(16, max(4, runtime.NumCPU()*2)), "Number of parallel workers (1-256)")
	noProbe := flag.Bool("no-probe", false, "Skip ffprobe duration/codec extraction")
	probeTimeout := flag.Duration("probe-timeout", 10*time.Second, "Per-file ffprobe timeout")
	probeRetries := flag.Int("probe-retries", 1, "Retries for transient ffprobe failures")
	dedupe := flag.Bool("dedupe", false, "Detect likely duplicate files (partial hash + size)")

	minSize := flag.Int64("min-size", 0, "Minimum file size in bytes (filter)")
	maxSize := flag.Int64("max-size", 0, "Maximum file size in bytes (0 = no limit)")
	minDur := flag.Float64("min-dur", 0, "Minimum duration in seconds (requires ffprobe)")
	maxDur := flag.Float64("max-dur", 0, "Maximum duration in seconds (0 = no limit)")

	topN := flag.Int("top", 10, "Number of top formats/codecs to display")
	quiet := flag.Bool("quiet", false, "Suppress progress bar and banner (results only)")
	noColor := flag.Bool("no-color", false, "Disable ANSI colour output")

	jsonOut := flag.String("json", "", "Export results to JSON file")
	csvOut := flag.String("csv", "", "Export results to CSV file")
	logOut := flag.String("log", "", "Write a plain-text run log to this file")

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, `
%sAllVideosScan%s v%s — Media file scanner & analyzer
%sOriginal Python tool by 8-Programmers'; Go rewrite, optimized & stabilized.%s

Usage:
  allvideoscan [flags]

Scan Modes (combinable):
  -cwd                 Scan current working directory [default: true]
  -path <dir>          Scan a specific directory
  -home                Scan user home subdirectories (Desktop, Videos, etc.)
  -all-drives          Scan all drives / filesystem root

Filtering:
  -audio               Include audio files
  -no-recurse          Flat scan only
  -ext <list>          Extra comma-separated extensions (e.g. .ts,.m2ts)
  -exclude <patterns>  Comma-separated glob patterns to skip
  -follow-symlinks     Follow symlinked files
  -min-size / -max-size <bytes>
  -min-dur  / -max-dur  <seconds>

Processing:
  -workers <n>         Worker threads 1-256 [default: %d]
  -no-probe            Skip ffprobe (faster, no duration/codec info)
  -probe-timeout <dur> Per-file ffprobe timeout [default: 10s]
  -probe-retries <n>   Retries on transient ffprobe failure [default: 1]
  -dedupe              Flag likely duplicate files

Output:
  -top <n>             Rows to show in format/codec tables [default: 10]
  -quiet               Minimal console output
  -no-color            Disable ANSI colours
  -json <file>         Export results to JSON
  -csv  <file>         Export results to CSV
  -log  <file>         Write a plain-text run log

Other:
  -v / -version        Print version

Examples:
  allvideoscan                          Scan CWD, videos only
  allvideoscan -audio                   Scan CWD, include audio
  allvideoscan -path /data/movies       Scan specific directory
  allvideoscan -all-drives -workers 32  Full system scan
  allvideoscan -csv out.csv -json out.json
  allvideoscan -no-probe -audio -home   Fast home scan with audio
  allvideoscan -dedupe -exclude "*sample*,*trailer*"
`,
			colBold, colReset, version,
			colGray, colReset,
			min(16, max(4, runtime.NumCPU()*2)),
		)
	}

	flag.Parse()

	if *showVersion {
		fmt.Printf("AllVideosScan v%s\n", version)
		os.Exit(0)
	}
	if *noColor {
		disableColor()
	}

	// ── Graceful Ctrl+C handling ──────────────────────────────────────────
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	if !*quiet {
		fmt.Printf("\n%s%s", colCyan, colBold)
		fmt.Println("╔══════════════════════════════════════════════════════════════╗")
		fmt.Printf("║  %sAllVideosScan%s%-36s%s║\n",
			colGreen+colBold, colCyan, fmt.Sprintf("  v%s", version), "")
		fmt.Println("║  Go edition — optimized, stabilized, zero dependencies        ║")
		fmt.Println("╚══════════════════════════════════════════════════════════════╝")
		fmt.Print(colReset)
		fmt.Println()
	}

	// Validate workers
	if *workers < 1 || *workers > 256 {
		fmt.Fprintln(os.Stderr, c(colRed, "❌  --workers must be between 1 and 256"))
		os.Exit(1)
	}

	// ffprobe check
	ffprobeAvailable = checkFFprobe()
	probeEnabled := ffprobeAvailable && !*noProbe
	if !*quiet {
		if probeEnabled {
			fmt.Println(c(colGreen, "✅  ffprobe detected — duration & codec extraction enabled"))
		} else if !*noProbe {
			fmt.Println(c(colYellow, "⚠️   ffprobe not found — skipping duration/codec extraction"))
			fmt.Println(c(colGray, "    Install ffmpeg to enable: https://ffmpeg.org/download.html"))
		}
	}

	// ── Build extension set ────────────────────────────────────────────────
	exts := make(map[string]struct{}, len(videoExtensions)+len(audioExtensions))
	for k, v := range videoExtensions {
		exts[k] = v
	}
	if *includeAudio {
		for k, v := range audioExtensions {
			exts[k] = v
		}
	}
	if *extraExts != "" {
		for _, e := range strings.Split(*extraExts, ",") {
			e = strings.TrimSpace(strings.ToLower(e))
			if e == "" {
				continue
			}
			if !strings.HasPrefix(e, ".") {
				e = "." + e
			}
			exts[e] = struct{}{}
		}
	}

	var excludes []string
	if *excludeList != "" {
		for _, p := range strings.Split(*excludeList, ",") {
			p = strings.TrimSpace(p)
			if p != "" {
				excludes = append(excludes, p)
			}
		}
	}

	// ── Build scan roots ───────────────────────────────────────────────────
	var roots []string
	seen := make(map[string]struct{})
	addRoot := func(p string) {
		p = filepath.Clean(p)
		if _, ok := seen[p]; !ok {
			seen[p] = struct{}{}
			roots = append(roots, p)
		}
	}

	if *customPath != "" {
		addRoot(*customPath)
	}
	if *scanAll {
		for _, d := range getAllDrives() {
			addRoot(d)
		}
	}
	if *scanHome {
		home, err := os.UserHomeDir()
		if err == nil {
			for _, sub := range []string{"Desktop", "Documents", "Downloads", "Videos", "Music", "Pictures"} {
				p := filepath.Join(home, sub)
				if _, err := os.Stat(p); err == nil {
					addRoot(p)
				}
			}
		}
	}
	if len(roots) == 0 || *scanCWD {
		cwd, err := os.Getwd()
		if err == nil {
			addRoot(cwd)
		}
	}

	if len(roots) == 0 {
		fmt.Fprintln(os.Stderr, c(colRed, "❌  No valid scan paths found."))
		os.Exit(1)
	}

	mediaLabel := "Videos"
	if *includeAudio {
		mediaLabel = "Videos + Audio"
	}

	if !*quiet {
		fmt.Println(strings.Repeat("─", 64))
		fmt.Printf("%s Scan paths:\n", c(colCyan, "📂"))
		for _, r := range roots {
			fmt.Printf("    %s\n", r)
		}
		fmt.Printf("%s Mode:    %s\n", c(colCyan, "📁"), mediaLabel)
		fmt.Printf("%s Workers: %d\n", c(colCyan, "⚙️ "), *workers)
		if !*noRecurse {
			fmt.Printf("%s Recurse: yes\n", c(colCyan, "🔁"))
		} else {
			fmt.Printf("%s Recurse: no (flat scan)\n", c(colCyan, "➡️ "))
		}
		fmt.Println(strings.Repeat("─", 64))
	}

	// ── Phase 1: Discovery ─────────────────────────────────────────────────
	if !*quiet {
		fmt.Printf("\n%s Phase 1: Discovery…\n", c(colYellow, "🔍"))
	}
	t0 := time.Now()
	found := discoverFiles(ctx, roots, exts, !*noRecurse, *followSymlinks, excludes)
	discTime := time.Since(t0)

	if len(found) == 0 {
		fmt.Println(c(colYellow, "✅  No media files found."))
		os.Exit(0)
	}
	if !*quiet {
		fmt.Printf("%s Found %s files in %.1fs\n",
			c(colGreen, "✅ "),
			c(colBold, fmt.Sprintf("%d", len(found))),
			discTime.Seconds(),
		)
	}

	// ── Phase 2: Analysis ──────────────────────────────────────────────────
	if !*quiet {
		fmt.Printf("\n%s Phase 2: Analysis…\n", c(colYellow, "📊"))
	}

	total := int64(len(found))
	var done int64
	results := make([]MediaFile, total)

	cfg := scanConfig{
		probeEnabled: probeEnabled,
		probeTimeout: *probeTimeout,
		probeRetries: *probeRetries,
		dedupe:       *dedupe,
	}

	stopProgress := make(chan struct{})
	t1 := time.Now()
	if !*quiet {
		go func() {
			ticker := time.NewTicker(150 * time.Millisecond)
			defer ticker.Stop()
			for {
				select {
				case <-stopProgress:
					fmt.Printf("\r%-100s\r", "")
					return
				case <-ticker.C:
					d := atomic.LoadInt64(&done)
					fmt.Printf("\r  %s", renderBar(d, total, t1))
				}
			}
		}()
	}

	jobs := make(chan int, *workers*2)
	var wg sync.WaitGroup
	for w := 0; w < *workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for idx := range jobs {
				select {
				case <-ctx.Done():
					return
				default:
				}
				results[idx] = processFile(ctx, found[idx], cfg)
				atomic.AddInt64(&done, 1)
			}
		}()
	}

feed:
	for i := range found {
		select {
		case <-ctx.Done():
			break feed
		case jobs <- i:
		}
	}
	close(jobs)
	wg.Wait()
	close(stopProgress)
	if !*quiet {
		time.Sleep(200 * time.Millisecond)
	}

	interrupted := ctx.Err() != nil
	if interrupted {
		fmt.Println(c(colYellow, "\n⚠️   Interrupted — showing partial results for files processed so far."))
		// Trim unprocessed (zero-value) entries from the tail.
		trimmed := results[:0]
		for _, r := range results {
			if r.Path != "" {
				trimmed = append(trimmed, r)
			}
		}
		results = trimmed
	}

	analysisTime := time.Since(t1)
	if !*quiet {
		fmt.Printf("%s Analysis complete in %.1fs\n", c(colGreen, "✅ "), analysisTime.Seconds())
	}

	// ── Apply filters ──────────────────────────────────────────────────────
	filtered := results[:0]
	for _, f := range results {
		if *minSize > 0 && f.SizeBytes < *minSize {
			continue
		}
		if *maxSize > 0 && f.SizeBytes > *maxSize {
			continue
		}
		if probeEnabled && *minDur > 0 && f.Duration < *minDur {
			continue
		}
		if probeEnabled && *maxDur > 0 && f.Duration > *maxDur {
			continue
		}
		filtered = append(filtered, f)
	}
	results = filtered

	if len(results) == 0 {
		fmt.Println(c(colYellow, "⚠️   All files were filtered out — adjust filter flags."))
		os.Exit(0)
	}

	// ── Stats ──────────────────────────────────────────────────────────────
	formats, videoCodecs, audioCodecs, totalSize, totalDur := buildStats(results)
	sortedFormats := sortedFormatStats(formats)
	sortedVideoCodecs := sortedCodecStats(videoCodecs)
	sortedAudioCodecs := sortedCodecStats(audioCodecs)
	sizeMean, durMean := mean(results)
	biggestSize, smallestSize, biggestDur, smallestDur := biggestSmallest(results)

	corruptedCount := 0
	probedCount := 0
	for _, r := range results {
		if r.ProbedOK {
			probedCount++
		}
		if r.Corrupted {
			corruptedCount++
		}
	}

	var dupGroups map[string][]MediaFile
	if *dedupe {
		dupGroups = make(map[string][]MediaFile)
		byKey := make(map[string][]MediaFile)
		for _, r := range results {
			if r.PartialSum == "" {
				continue
			}
			key := fmt.Sprintf("%d-%s", r.SizeBytes, r.PartialSum)
			byKey[key] = append(byKey[key], r)
		}
		for k, v := range byKey {
			if len(v) > 1 {
				dupGroups[k] = v
			}
		}
	}

	totalTime := time.Since(t0)

	// ── Report ─────────────────────────────────────────────────────────────
	var out strings.Builder
	pr := func(format string, a ...interface{}) {
		s := fmt.Sprintf(format, a...)
		fmt.Print(s)
		out.WriteString(s)
	}

	hr := strings.Repeat("═", 64)
	pr("\n" + c(colCyan+colBold, hr) + "\n")
	pr(c(colCyan+colBold, "  📈  RESULTS") + "\n")
	pr(c(colCyan+colBold, hr) + "\n")

	pr("\n%s\n", c(colBold, "📊 SUMMARY"))
	probedPct := 0.0
	if len(results) > 0 {
		probedPct = float64(probedCount) / float64(len(results)) * 100
	}
	pr("  Files    : %s\n", c(colGreen, fmt.Sprintf("%d", len(results))))
	pr("  Analyzed : %d (%.1f%%)  |  Formats: %d\n", probedCount, probedPct, len(formats))
	if corruptedCount > 0 {
		pr("  Corrupted: %s\n", c(colRed, fmt.Sprintf("%d", corruptedCount)))
	}
	if *dedupe {
		pr("  Duplicate groups: %d\n", len(dupGroups))
	}

	pr("\n%s\n", c(colBold, "💾 STORAGE"))
	pr("  Total   : %s\n", c(colGreen, bytesToHuman(totalSize)))
	pr("  Average : %s\n", bytesToHuman(int64(sizeMean)))
	if biggestSize != nil {
		pr("  Biggest : %s — %s\n", bytesToHuman(biggestSize.SizeBytes), truncPath(biggestSize.Path, 70))
	}
	if smallestSize != nil {
		pr("  Smallest: %s — %s\n", bytesToHuman(smallestSize.SizeBytes), truncPath(smallestSize.Path, 70))
	}

	if probedCount > 0 {
		pr("\n%s\n", c(colBold, "⏱️  DURATION"))
		pr("  Total   : %s\n", c(colGreen, secondsToHMS(totalDur)))
		pr("  Average : %s\n", secondsToHMS(durMean))
		if biggestDur != nil {
			pr("  Biggest : %s — %s\n", secondsToHMS(biggestDur.Duration), truncPath(biggestDur.Path, 70))
		}
		if smallestDur != nil {
			pr("  Smallest: %s — %s\n", secondsToHMS(smallestDur.Duration), truncPath(smallestDur.Path, 70))
		}
	}

	pr("\n%s\n", c(colBold, fmt.Sprintf("📁 TOP %d FORMATS", *topN)))
	pr("  %-10s │ %7s │ %17s │ %6s │ %14s\n", "Format", "Count", "Size", "%", "Duration")
	pr("  " + strings.Repeat("─", 66) + "\n")
	top := sortedFormats
	if len(top) > *topN {
		top = top[:*topN]
	}
	for _, s := range top {
		pct := 0.0
		if totalSize > 0 {
			pct = float64(s.TotalSize) / float64(totalSize) * 100
		}
		durStr := "–"
		if probeEnabled {
			durStr = secondsToHMS(s.TotalDur)
		}
		pr("  %-10s │ %7d │ %17s │ %5.1f%% │ %14s\n",
			s.Format, s.Count, bytesToHuman(s.TotalSize), pct, durStr)
	}

	pr("\n%s\n", c(colBold, "🎬 VIDEO ENCODERS"))
	pr("  %-20s │ %7s\n", "Codec", "Count")
	pr("  " + strings.Repeat("─", 32) + "\n")
	vTop := sortedVideoCodecs
	if len(vTop) > *topN {
		vTop = vTop[:*topN]
	}
	if len(vTop) == 0 {
		pr("  %s\n", c(colGray, "(no codec data — enable ffprobe)"))
	}
	for _, s := range vTop {
		pr("  %-20s │ %7d\n", s.Codec, s.Count)
	}

	pr("\n%s\n", c(colBold, "🔊 AUDIO ENCODERS"))
	pr("  %-20s │ %7s\n", "Codec", "Count")
	pr("  " + strings.Repeat("─", 32) + "\n")
	aTop := sortedAudioCodecs
	if len(aTop) > *topN {
		aTop = aTop[:*topN]
	}
	if len(aTop) == 0 {
		pr("  %s\n", c(colGray, "(no codec data — enable ffprobe)"))
	}
	for _, s := range aTop {
		pr("  %-20s │ %7d\n", s.Codec, s.Count)
	}

	if *dedupe && len(dupGroups) > 0 {
		pr("\n%s\n", c(colBold, "🧬 LIKELY DUPLICATES"))
		i := 0
		for _, grp := range dupGroups {
			i++
			if i > *topN {
				pr("  … and %d more group(s)\n", len(dupGroups)-*topN)
				break
			}
			pr("  Group (%s each):\n", bytesToHuman(grp[0].SizeBytes))
			for _, g := range grp {
				pr("    - %s\n", truncPath(g.Path, 70))
			}
		}
	}

	pr("\n%s\n", c(colBold, "⏰  TIMING"))
	fpsStr := "–"
	if totalTime.Seconds() > 0 {
		fpsStr = fmt.Sprintf("%.0f files/s", float64(len(results))/totalTime.Seconds())
	}
	pr("  Total: %.2fs  |  Discovery: %.2fs  |  Analysis: %.2fs  |  Speed: %s\n",
		totalTime.Seconds(), discTime.Seconds(), analysisTime.Seconds(), fpsStr)

	// ── Exports ────────────────────────────────────────────────────────────
	if *jsonOut != "" {
		if err := exportJSON(results, *jsonOut); err != nil {
			fmt.Fprintf(os.Stderr, "%s JSON export failed: %v\n", c(colRed, "❌ "), err)
		} else {
			pr("\n%s JSON → %s\n", c(colGreen, "✅ "), *jsonOut)
		}
	}
	if *csvOut != "" {
		if err := exportCSV(results, *csvOut); err != nil {
			fmt.Fprintf(os.Stderr, "%s CSV export failed: %v\n", c(colRed, "❌ "), err)
		} else {
			pr("%s CSV  → %s\n", c(colGreen, "✅ "), *csvOut)
		}
	}

	pr("\n" + c(colCyan+colBold, hr) + "\n")
	if interrupted {
		pr(c(colYellow+colBold, "⚠️   Partial results (interrupted)") + "\n")
	} else {
		pr(c(colGreen+colBold, "✅  Complete!") + "\n")
	}
	pr(c(colCyan+colBold, hr) + "\n\n")

	if *logOut != "" {
		// Strip ANSI codes for the plain-text log file.
		plain := stripANSI(out.String())
		if err := exportLog(*logOut, plain); err != nil {
			fmt.Fprintf(os.Stderr, "%s Log export failed: %v\n", c(colRed, "❌ "), err)
		} else {
			fmt.Printf("%s Log  → %s\n", c(colGreen, "✅ "), *logOut)
		}
	}

	if interrupted {
		os.Exit(130)
	}
}

// stripANSI removes escape sequences so log files stay clean.
func stripANSI(s string) string {
	var b strings.Builder
	inEsc := false
	for i := 0; i < len(s); i++ {
		ch := s[i]
		if ch == '\033' {
			inEsc = true
			continue
		}
		if inEsc {
			if ch == 'm' {
				inEsc = false
			}
			continue
		}
		b.WriteByte(ch)
	}
	return b.String()
}
