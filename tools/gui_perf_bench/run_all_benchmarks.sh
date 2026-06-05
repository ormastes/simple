#!/usr/bin/env bash
# GUI Perf Benchmark — Run all framework benchmarks at 8K resolution
# Usage: ./run_all_benchmarks.sh [--width 7680 --height 4320 --frames 60]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
BUILD_DIR="$PROJECT_DIR/build/gui_perf_bench"
REPORT="$BUILD_DIR/comparison_report.txt"

WIDTH="${WIDTH:-7680}"
HEIGHT="${HEIGHT:-4320}"
FRAMES="${FRAMES:-60}"

# Parse args
while [[ $# -gt 0 ]]; do
    case "$1" in
        --width) WIDTH="$2"; shift 2 ;;
        --height) HEIGHT="$2"; shift 2 ;;
        --frames) FRAMES="$2"; shift 2 ;;
        *) shift ;;
    esac
done

mkdir -p "$BUILD_DIR"
echo "=== GUI Perf Benchmark Comparison ===" | tee "$REPORT"
echo "Resolution: ${WIDTH}x${HEIGHT}  Frames: ${FRAMES}" | tee -a "$REPORT"
echo "Date: $(date -Iseconds)" | tee -a "$REPORT"
echo "Host: $(hostname)" | tee -a "$REPORT"
echo "GPU: $(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null | head -1 || echo 'none')" | tee -a "$REPORT"
echo "" | tee -a "$REPORT"

run_bench() {
    local name="$1"
    local cmd="$2"
    local out="$BUILD_DIR/${name}.stdout"
    local err="$BUILD_DIR/${name}.stderr"
    local time_out="$BUILD_DIR/${name}.time"

    echo "--- Running: $name ---" | tee -a "$REPORT"
    if /usr/bin/time -v bash -c "$cmd" >"$out" 2>"$err"; then
        cat "$out" | tee -a "$REPORT"
        # Extract RSS from time output (in stderr)
        local rss
        rss=$(grep "Maximum resident" "$err" | awk '{print $NF}' 2>/dev/null || echo "unavailable")
        echo "gui_perf_benchmark_max_rss_kb=$rss" | tee -a "$REPORT"
        echo "gui_perf_benchmark_exit_code=0" | tee -a "$REPORT"
    else
        local rc=$?
        echo "gui_perf_benchmark_backend=$name" | tee -a "$REPORT"
        echo "gui_perf_benchmark_status=failed" | tee -a "$REPORT"
        echo "gui_perf_benchmark_exit_code=$rc" | tee -a "$REPORT"
        echo "gui_perf_benchmark_error=$(head -5 "$err" 2>/dev/null)" | tee -a "$REPORT"
    fi
    echo "" | tee -a "$REPORT"
}

# ── 1. C/GTK3 ──
if pkg-config --exists gtk+-3.0 2>/dev/null; then
    GTK_BIN="$BUILD_DIR/bench_gtk"
    if [[ ! -f "$GTK_BIN" ]] || [[ "$SCRIPT_DIR/bench_gtk.c" -nt "$GTK_BIN" ]]; then
        echo "Building GTK benchmark..."
        gcc -O2 -o "$GTK_BIN" "$SCRIPT_DIR/bench_gtk.c" $(pkg-config --cflags --libs gtk+-3.0) -lm
    fi
    run_bench "gtk3" "GDK_BACKEND=x11 $GTK_BIN --width $WIDTH --height $HEIGHT --frames $FRAMES"
else
    echo "--- gtk3: SKIPPED (gtk+-3.0 not found) ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=gtk3" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "gui_perf_benchmark_reason=pkg-config gtk+-3.0 not found" | tee -a "$REPORT"
    echo "" | tee -a "$REPORT"
fi

# ── 2. Python/tkinter ──
if python3 -c "import tkinter" 2>/dev/null; then
    run_bench "python_tkinter" "python3 $SCRIPT_DIR/bench_python.py --width $WIDTH --height $HEIGHT --frames $FRAMES"
else
    echo "--- python_tkinter: SKIPPED (tkinter not found) ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=python_tkinter" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "gui_perf_benchmark_reason=python3 tkinter not available" | tee -a "$REPORT"
    echo "" | tee -a "$REPORT"
fi

# ── 3. JavaScript/Node canvas ──
if command -v node >/dev/null 2>&1; then
    # Check if canvas module available
    if node -e "require('canvas')" 2>/dev/null; then
        run_bench "javascript_node" "node $SCRIPT_DIR/bench_js_node.js --width $WIDTH --height $HEIGHT --frames $FRAMES"
    else
        echo "--- javascript_node: installing canvas module ---"
        (cd "$SCRIPT_DIR" && npm install canvas 2>/dev/null) || true
        if node -e "require('canvas')" 2>/dev/null; then
            run_bench "javascript_node" "node $SCRIPT_DIR/bench_js_node.js --width $WIDTH --height $HEIGHT --frames $FRAMES"
        else
            echo "--- javascript_node: SKIPPED (canvas module unavailable) ---" | tee -a "$REPORT"
            echo "gui_perf_benchmark_backend=javascript_node" | tee -a "$REPORT"
            echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
            echo "gui_perf_benchmark_reason=node canvas module not installable" | tee -a "$REPORT"
            echo "" | tee -a "$REPORT"
        fi
    fi
else
    echo "--- javascript_node: SKIPPED (node not found) ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=javascript_node" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "" | tee -a "$REPORT"
fi

# ── 4. Electron (via existing infrastructure) ──
ELECTRON_BIN=$(command -v electron 2>/dev/null || echo "")
if [[ -n "$ELECTRON_BIN" ]]; then
    run_bench "electron" "echo 'gui_perf_benchmark_backend=electron' && echo 'gui_perf_benchmark_status=deferred' && echo 'gui_perf_benchmark_reason=use-existing-wm-compare-electron-matrix'"
else
    echo "--- electron: SKIPPED (electron not installed) ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=electron" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "gui_perf_benchmark_reason=electron binary not found; existing contract reports cold_startup=4075ms" | tee -a "$REPORT"
    echo "" | tee -a "$REPORT"
fi

# ── 5. Tauri ──
if command -v cargo >/dev/null 2>&1 && cargo tauri --version >/dev/null 2>&1; then
    echo "--- tauri: integration pending ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=tauri" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "gui_perf_benchmark_reason=tauri benchmark app not yet built; requires cargo-tauri + webview2" | tee -a "$REPORT"
else
    echo "--- tauri: SKIPPED (cargo tauri not found) ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=tauri" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "gui_perf_benchmark_reason=cargo tauri CLI not installed" | tee -a "$REPORT"
    echo "" | tee -a "$REPORT"
fi

# ── 6. Pure Simple (CUDA-backed) ──
if command -v nvidia-smi >/dev/null 2>&1 && [[ -x "$PROJECT_DIR/bin/simple" ]]; then
    run_bench "pure_simple_cuda" "$PROJECT_DIR/bin/simple run $PROJECT_DIR/src/app/wm_compare/backend_measurement_export.spl -- --measure-cuda-device-buffer --width $WIDTH --height $HEIGHT --fixture gui-perf-8k-fill --shell simple-web --command bench-8k --host $(hostname)"
elif command -v nvidia-smi >/dev/null 2>&1 && [[ -x "$PROJECT_DIR/bin/bootstrap/simple" ]]; then
    run_bench "pure_simple_cuda" "$PROJECT_DIR/bin/bootstrap/simple run $PROJECT_DIR/src/app/wm_compare/backend_measurement_export.spl -- --measure-cuda-device-buffer --width $WIDTH --height $HEIGHT --fixture gui-perf-8k-fill --shell simple-web --command bench-8k --host $(hostname)"
else
    echo "--- pure_simple_cuda: SKIPPED ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=pure_simple_cuda" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    if ! command -v nvidia-smi >/dev/null 2>&1; then
        echo "gui_perf_benchmark_reason=no CUDA GPU available" | tee -a "$REPORT"
    else
        echo "gui_perf_benchmark_reason=simple compiler binary not found" | tee -a "$REPORT"
    fi
    echo "" | tee -a "$REPORT"
fi

# ── 7. Simple Web Renderer (software path) ──
SIMPLE_BIN="$PROJECT_DIR/bin/simple"
[[ ! -x "$SIMPLE_BIN" ]] && SIMPLE_BIN="$PROJECT_DIR/bin/bootstrap/simple"
if [[ -x "$SIMPLE_BIN" ]]; then
    run_bench "simple_web_software" "$SIMPLE_BIN run $PROJECT_DIR/src/app/wm_compare/backend_measurement_export.spl -- --initialized-gpu-backend software --probe-initialized-gpu --width $WIDTH --height $HEIGHT --fixture gui-perf-8k-software --shell simple-web --command bench-8k --host $(hostname)"
else
    echo "--- simple_web_software: SKIPPED ---" | tee -a "$REPORT"
    echo "gui_perf_benchmark_backend=simple_web_software" | tee -a "$REPORT"
    echo "gui_perf_benchmark_status=unavailable" | tee -a "$REPORT"
    echo "gui_perf_benchmark_reason=simple compiler binary not found" | tee -a "$REPORT"
    echo "" | tee -a "$REPORT"
fi

# ── Summary ──
echo "========================================" | tee -a "$REPORT"
echo "Benchmark complete. Full report: $REPORT" | tee -a "$REPORT"
echo "Per-backend outputs: $BUILD_DIR/*.stdout" | tee -a "$REPORT"
