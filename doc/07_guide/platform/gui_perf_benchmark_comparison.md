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
| Simple Web Soft | — | — | — | — | 8K run deferred; 320x240 measured smoke below |

**Notes**: GTK frame times are frame-to-frame intervals (draw + composite + X11 present).
Cairo draw calls alone take 0.035ms; the remaining ~150ms is GTK/X11 software compositing
on Xvfb. Node.js canvas is headless (in-memory buffer, no display server), so the 9.3x
speed difference is partly the display-server overhead, not renderer speed alone.

### Current Simple Backend Evidence (2026-06-06 smoke)

`doc/09_report/gui_perf_benchmark_2026-06-06.md` is the canonical linked smoke
report for the current Simple backend profile. It was regenerated at 320x240,
1 frame, with `profile_report_contract=true`.

| Backend | Frame p50 | Frame p95 | Status | Measurement |
|---------|-----------|-----------|--------|-------------|
| Simple CUDA fill | 0.479 ms | 0.479 ms | valid | Device-buffer fill/readback, checksum `sum32:328570011648000`, `nonzero_pixels:76800` |
| Simple Web software | 3011.155 ms | 3011.155 ms | valid | Narrow software-only `simple_web_render_html_to_pixels_with_engine2d_backend` render-loop row, checksum `sum32:328745677397784`, `nonzero_pixels:76800` |

The CUDA row proves the generated Engine2D GPU fill lane is measurable on this
host. The software web row is not an availability probe anymore; it is a real
frame measurement and shows the current pure Simple web GUI path remains
dominated by interpreted text/layout work.

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
  --measure-cuda-device-buffer true --width 7680 --height 4320

bin/simple run src/app/wm_compare/backend_measurement_software_export.spl -- \
  --software-render-backend software \
  --width 320 --height 240 --warmup-count 1 --sample-count 1
```

## Pixel Parity Gate

"Do not cheat" — optimizations must not change pixel output.

1. `production_gui_web_renderer_parity.spl` — exact software/cpu_simd/metal match
2. `backend_parity.spl` — framebuffer vs software byte-for-byte
3. `golden_gate.spl` — golden-image drift, exact-only acceptance

## Optimization Opportunities

### CUDA (highest impact, measured smoke; needs 8K repeats)
- Persistent device buffer reuse (skip 127 MB alloc/free per frame)
- Async readback via `cuMemcpyDtoHAsync` + stream sync
- Module caching already in `CudaSession.module_cache`

### Software rasterizer
- Engine2D Simple scalar is 31x slower than C scalar for fill at 1080p
- Key optimization: the Simple-to-C compilation gap, not algorithmic
- CPU SIMD (AVX2) backend exists but needs 8K throughput measurement
- Dirty-rect tracking avoids full 127 MB writes for partial updates
- Software layout renders must not replay the already-painted framebuffer
  through an Engine2D software present/readback cycle. The 2026-06-06
  render-loop smoke dropped from about 20.82s in the broad profile path to
  about 3.01s at 320x240 after returning the painted software framebuffer
  directly and measuring through the narrow software-only exporter.
- Text remains the dominant software-layout cost. Direct 320x240 fixture timing
  showed a solid page at about 2ms, layout without text at about 244ms, and
  layout with text at about 1.21-1.29s after char-code glyph lookup and packed
  glyph rows. Treat further software-only text tweaks as secondary to GPU or
  compiled-mode text rasterization.

### General
- Frame pacer prevents busy-wait; verify no artificial latency in bench mode
- `WmPerfCounters.report_contract()` now emits per-phase timings when probes are driven

## Remaining Work

1. **Compiled Simple 8K repeats**: CUDA and software backends now have measured
   smoke rows; repeat at 8K with multiple frames before making release claims.
2. **CPU SIMD at 8K**: AVX2 backend exists but no 8K throughput evidence yet
3. **Tauri integration**: Needs `cargo-tauri` CLI + WebKitGTK dev package
4. **Software text/layout optimization**: the real software render-loop row is
   still far slower than JS/GTK at 320x240; move bitmap/vector font and text-blit
   work onto generated Engine2D GPU lanes or compiled text raster paths.

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
  backend_measurement_software_export.spl # Narrow software render-loop CLI
  backend_measurement_report.spl  # BackendComparisonSample + SDN export

src/os/compositor/
  perf_counters.spl         # Per-phase timing + report_contract()
  frame_pacer.spl           # Frame budget + vsync + report_contract()
```
