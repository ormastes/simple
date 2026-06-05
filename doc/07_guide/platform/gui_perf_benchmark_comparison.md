# GUI Performance Benchmark Comparison Guide

## Overview

Cross-framework GUI rendering performance comparison at 8K resolution (7680x4320).
Measures cold startup, warm frame time, and fill-rate across 7 backend lanes.

## Frameworks Compared

| Backend | Language | Renderer | 8K Status | Integration |
|---------|----------|----------|-----------|-------------|
| Pure Simple (CUDA) | Simple | CUDA PTX kernel | **Ready** | `backend_measurement_cuda.spl` |
| Simple Web (Software) | Simple | Software rasterizer | **Ready** | `backend_measurement_export.spl` |
| Electron | JS/Chromium | Chromium compositor | **Partial** | `wm_compare` electron matrix |
| GTK3 | C | Cairo/X11 | **Ready** | `tools/gui_perf_bench/bench_gtk.c` |
| JavaScript (Node) | JS | node-canvas (Cairo) | **Ready** | `tools/gui_perf_bench/bench_js_node.js` |
| JavaScript (Browser) | JS | Canvas 2D (GPU) | **Ready** | `tools/gui_perf_bench/bench_js.html` |
| Python (tkinter) | Python | Tk/X11 | **Ready** | `tools/gui_perf_bench/bench_python.py` |
| Tauri | Rust/WebView | WebView2/WebKitGTK | **Unavailable** | Requires `cargo-tauri` CLI |

## Running Benchmarks

### Full comparison (all backends):
```bash
cd tools/gui_perf_bench
./run_all_benchmarks.sh --width 7680 --height 4320 --frames 60
```

### Individual backends:
```bash
# Pure Simple CUDA (8K fill)
bin/simple run src/app/wm_compare/backend_measurement_export.spl -- \
  --measure-cuda-device-buffer --width 7680 --height 4320 \
  --fixture gui-perf-8k-fill --host $(hostname)

# GTK3
gcc -O2 -o build/bench_gtk tools/gui_perf_bench/bench_gtk.c \
  $(pkg-config --cflags --libs gtk+-3.0) -lm
./build/bench_gtk --width 7680 --height 4320 --frames 60

# JavaScript (Node headless)
node tools/gui_perf_bench/bench_js_node.js --width 7680 --height 4320 --frames 60

# Python tkinter
python3 tools/gui_perf_bench/bench_python.py --width 7680 --height 4320 --frames 60
```

## Metrics

All backends emit a uniform key=value format:

| Metric | Unit | Description |
|--------|------|-------------|
| `cold_startup_ms` | ms | Time from process start to first frame |
| `warm_total_ms` | ms | Total wall-clock for all measured frames |
| `frame_time_avg_ms` | ms | Mean frame render time |
| `frame_time_p50_ms` | ms | Median frame render time |
| `frame_time_p95_ms` | ms | 95th percentile frame time |
| `frame_time_max_ms` | ms | Worst-case frame time |
| `pixel_count` | px | Total pixels per frame (8K = 33,177,600) |
| `bytes_per_frame` | bytes | RGBA buffer size (8K = 132,710,400 = ~127 MB) |
| `pixel_checksum` | sum | Pixel integrity checksum (parity gate) |
| `max_rss_kb` | KB | Peak resident memory |

## 8K Resolution Analysis

At 7680x4320 (33.2M pixels, ~127 MB/frame RGBA):

- **Fill-rate dominated**: The bottleneck is memory bandwidth, not computation.
  A single 8K RGBA fill writes 127 MB. DDR4-3200 peaks at ~51 GB/s; a naïve
  single-core fill saturates at ~400 fps. GPU (A6000 at 768 GB/s) can fill at
  ~6000 fps.

- **CUDA advantage**: Pure Simple CUDA lane bypasses the CPU memory bus entirely.
  The PTX fill kernel runs on-device; only the readback crosses PCIe. For
  rendering-only workloads (no readback needed for display), CUDA eliminates
  the 127 MB/frame copy.

- **Cairo-based backends** (GTK3, Node canvas): Share the same Cairo rasterizer.
  Performance differences are overhead (GTK widget tree vs raw canvas), not
  rasterizer speed.

- **Electron**: Chromium's compositor adds process isolation, IPC, and GPU
  process overhead. Current contract shows cold_startup=4075ms, which includes
  Chromium bootstrap.

## Pixel Parity Gate

The "do not cheat" constraint means optimizations must not change pixel output.
The existing parity infrastructure enforces this:

1. `production_gui_web_renderer_parity.spl` — exact pixel comparison between
   software, cpu_simd, and metal backends
2. `backend_parity.spl` — framebuffer vs software reference byte-for-byte match
3. `golden_gate.spl` — golden-image drift detection with exact-only acceptance

**Before optimizing**: capture baseline checksums at 8K resolution.
**After optimizing**: re-run parity checks. Gate must pass with zero pixel diff.

## Current Contract Status

From `build/codex_production_gui_perf_contract.stdout`:

| Metric | Value | Status |
|--------|-------|--------|
| Parity | electron matrix fail (checksum=0) | **FAIL** |
| Cold startup | 4075 ms | Measured |
| Warm startup | unavailable | Probe not wired |
| Frame time p50 | unavailable | Probe not wired |
| Frame time p95 | unavailable | Probe not wired |
| Input-to-paint | unavailable | Probe not wired |
| Max RSS | 93,488 KB | Measured |
| Binary size | 53,746,144 bytes | Measured |

### Why electron_checksum=0

The electron backend produces zero pixels on headless Linux — Chromium requires
a display server. The parity check correctly reports this as a failure rather
than silently accepting empty output.

## Optimization Opportunities

### CUDA Pure Simple lane (highest impact)
- **Module caching**: `CudaSession.module_cache` already caches PTX module.
  Ensure it persists across frames (warm path skips `load_module`).
- **Persistent allocation**: Reuse device buffer across frames instead of
  alloc/free per frame. At 8K, each alloc is 127 MB.
- **Async readback**: Use `cuMemcpyDtoHAsync` + stream sync instead of
  blocking `cuda_memcpy_dtoh`. Overlap readback with next frame's compute.

### Software rasterizer
- **SIMD fill**: The `cpu_simd` backend already uses SIMD for fill/copy/alpha/blit.
  At 8K, ensure the hot loop uses 256-bit AVX2 stores (32 bytes/cycle vs 16
  for SSE4).
- **Dirty rect**: `FramePacer` and dirty-rect tracking skip unchanged regions.
  At 8K, partial updates avoid the full 127 MB write.

### General
- **Frame pacer**: `frame_pacer.spl` prevents busy-wait. Ensure vsync alignment
  doesn't add artificial latency in benchmark mode.
- **Perf counters**: Wire `WmPerfCounters` per-phase timings (event_wait, input,
  layout, paint, present, idle) into the contract output to identify where time
  is actually spent.

## Unwired Probes (To Complete)

The contract reports several metrics as "unavailable". To wire them:

1. **warm_startup**: Time from module-cached state to first frame. The CUDA
   backend already computes `warm_us = artifact_load_us + frame_us`. Wire
   this into the contract output via `--warm-startup-ms` flag.

2. **frame_time_p50/p95**: Run N frames, sort timings. The `WmPerfCounters`
   rolling sample buffer already computes this — emit via perf report.

3. **input_to_paint**: Requires an input event probe. Timestamp at event
   dispatch, timestamp at paint completion, report delta. The compositor's
   `perf_counters.spl` tracks `input` and `paint` phases separately.

## File Layout

```
tools/gui_perf_bench/
  run_all_benchmarks.sh     # Orchestrator — runs all backends, collects results
  bench_gtk.c               # C/GTK3 benchmark (Cairo rasterizer)
  bench_python.py           # Python/tkinter benchmark
  bench_js.html             # Browser JS Canvas benchmark
  bench_js_node.js          # Node.js headless canvas benchmark

src/app/wm_compare/
  backend_measurement_cuda.spl    # CUDA device-buffer measurement
  backend_measurement_export.spl  # CLI entry point for measurements
  backend_measurement_report.spl  # BackendComparisonSample struct + SDN export
  production_gui_web_renderer_parity.spl  # Pixel parity gate

src/os/compositor/
  perf_counters.spl         # Per-phase timing (event/input/layout/paint/present)
  frame_pacer.spl           # Frame budget + vsync alignment
```
