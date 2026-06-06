# GUI Performance Benchmark Comparison Guide

## Overview

Cross-framework GUI rendering performance comparison at 8K resolution (7680x4320).
All numbers measured on this host unless marked otherwise.

## Measured Results (2026-06-05)

### 8K Fill + Widget Scene (7680x4320, 33.18M pixels, 60 frames)

| Backend | Cold Start | Frame Avg | Frame p50 | Frame p95 | Measurement |
|---------|-----------|-----------|-----------|-----------|-------------|
| Node.js Canvas | 2.25 ms | 17.3 ms | 16.4 ms | 17.3 ms | Headless, node-canvas (Cairo) |
| GTK3/C | 104 ms | 150.4 ms | 153.0 ms | 163.4 ms | Xvfb :99, full render cycle |
| Python/tkinter | — | — | — | — | Unavailable (no tkinter module) |
| Electron | 4075 ms | — | — | — | Existing contract; checksum=0 headless |
| Tauri | — | — | — | — | Unavailable (no cargo-tauri) |
| Simple CUDA | — | — | — | — | Interpreter lacks CUDA FFI; needs compiled binary |
<<<<<<< Conflict 1 of 2
+++++++ Contents of side #1
| Simple Web Soft | 3440 ms | 3267 ms | 3267 ms | 3267 ms | 2026-06-06 smoke, 320x240, software render-loop row |
%%%%%%% Changes from base to side #2
-| Simple Web Soft | 3315 ms | 3292 ms | 3292 ms | 3292 ms | 2026-06-06 smoke, 320x240, software render-loop row |
+| Simple Web Soft | — | — | — | — | Interpreter probe only; needs compiled binary |
>>>>>>> Conflict 1 of 2 ends

**Notes**: GTK frame times are frame-to-frame intervals (draw + composite + X11 present).
Cairo draw calls alone take 0.035ms; the remaining ~150ms is GTK/X11 software compositing
on Xvfb. Node.js canvas is headless (in-memory buffer, no display server), so the 9.3x
speed difference is partly the display-server overhead, not renderer speed alone.

### Existing Evidence: Simple vs GTK Cold Start (from `gtk_gui_repeat_evidence`)

| Metric | Simple (compiled) | GTK3 | Ratio |
|--------|------------------|------|-------|
| Cold start | 0.192 ms | 65.865 ms | **343x faster** |
| Warm frame | 0.001 ms | 0.085 ms | **85x faster** |
| RSS | ~14 KB | 32.5 MB | **~2300x smaller** |

### Existing Evidence: Engine2D at 1080p (from `engine2d_compute_dispatch_benchmark`)

10 warmup + 100 timed frames, pixel-hash verified identical output.

| Scene | C Scalar p50 | Simple Scalar p50 | C px/s | Simple px/s |
|-------|-------------|-------------------|--------|-------------|
| fill_1080p | 4.5 ms | 141 ms | 458M | 14.7M |
| blit_tiles | 4.8 ms | 43 ms | 434M | 47.9M |
| clipped_scroll | 2.3 ms | 23 ms | 898M | 89M |

### Startup Audit (from `startup_size_performance_audit`)

| Binary | Size | Startup ms |
|--------|------|-----------|
| Simple hello (core-c) | 14 KB | 3.1 |
| C hello | 14 KB | 5.6 |
| Simple TUI standalone | 14 KB | 5.3 |
| Simple full TUI app | 14 KB | 6.5 |
| Electron (Chromium) | ~54 MB | 4075 |

## Running Benchmarks

```bash
# Full comparison (needs Xvfb for GTK/tkinter):
Xvfb :99 -screen 0 7680x4320x24 &
DISPLAY=:99 tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60

# Individual:
node tools/gui_perf_bench/bench_js_node.js --width 7680 --height 4320 --frames 60
DISPLAY=:99 build/gui_perf_bench/bench_gtk --width 7680 --height 4320 --frames 60

# Simple backends (requires compiled binary, not interpreter):
bin/simple run src/app/wm_compare/backend_measurement_export.spl -- \
  --measure-cuda-device-buffer --width 7680 --height 4320
```

## Pixel Parity Gate

"Do not cheat" — optimizations must not change pixel output.

1. `production_gui_web_renderer_parity.spl` — exact software/cpu_simd/metal match
2. `backend_parity.spl` — framebuffer vs software byte-for-byte
3. `golden_gate.spl` — golden-image drift, exact-only acceptance

## Optimization Opportunities

### CUDA (highest impact, currently unmeasured at 8K)
- Persistent device buffer reuse (skip 127 MB alloc/free per frame)
- Async readback via `cuMemcpyDtoHAsync` + stream sync
- Module caching already in `CudaSession.module_cache`

### Software rasterizer
- Engine2D Simple scalar is 31x slower than C scalar for fill at 1080p
- Key optimization: the Simple-to-C compilation gap, not algorithmic
- CPU SIMD (AVX2) backend exists but needs 8K throughput measurement
- Dirty-rect tracking avoids full 127 MB writes for partial updates
<<<<<<< Conflict 2 of 2
+++++++ Contents of side #1
- Software layout renders must not replay the already-painted framebuffer
  through an Engine2D software present/readback cycle. The 2026-06-06
  render-loop smoke dropped from about 13.98s to about 3.27s at 320x240 after
  returning the painted software framebuffer directly.
- Text remains the dominant software-layout cost. Direct 320x240 fixture timing
  showed a solid page at about 2ms, layout without text at about 244ms, and
  layout with text at about 1.21-1.29s after char-code glyph lookup and packed
  glyph rows. Treat further software-only text tweaks as secondary to GPU or
  compiled-mode text rasterization.
%%%%%%% Changes from base to side #2
-- Software layout renders must not replay the already-painted framebuffer
-  through an Engine2D software present/readback cycle. The 2026-06-06
-  render-loop smoke dropped from about 13.98s to about 3.29s at 320x240 after
-  returning the painted software framebuffer directly.
>>>>>>> Conflict 2 of 2 ends

### General
- Frame pacer prevents busy-wait; verify no artificial latency in bench mode
- `WmPerfCounters.report_contract()` now emits per-phase timings when probes are driven

## Remaining Work

1. **Compiled Simple benchmarks**: CUDA and software backends need compiled binary
   (interpreter can't drive CUDA FFI or measure real frame throughput)
2. **CPU SIMD at 8K**: AVX2 backend exists but no 8K throughput evidence yet
3. **Tauri integration**: Needs `cargo-tauri` CLI + WebKitGTK dev package
4. **Wire perf probes**: `start_phase`/`end_phase` calls need to be added to the
   benchmark measurement path for `WmPerfCounters` to have non-zero samples

## File Layout

```
tools/gui_perf_bench/
  run_all_benchmarks.shs     # Orchestrator — all backends, collects results
  bench_gtk.c               # C/GTK3 benchmark (Cairo/X11)
  bench_python.py           # Python/tkinter benchmark
  bench_js.html             # Browser JS Canvas benchmark
  bench_js_node.js          # Node.js headless canvas benchmark

src/app/wm_compare/
  backend_measurement_cuda.spl    # CUDA device-buffer measurement
  backend_measurement_export.spl  # CLI entry point
  backend_measurement_report.spl  # BackendComparisonSample + SDN export

src/os/compositor/
  perf_counters.spl         # Per-phase timing + report_contract()
  frame_pacer.spl           # Frame budget + vsync + report_contract()
```
