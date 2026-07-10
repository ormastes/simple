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
Current harness runs also emit `gui_perf_cpu_base_compare_*` fields after the
backend rows. The comparison uses `simple_web_cpu_simd` and the first completed
CPU drawing-library baseline, preferring Node Canvas/Cairo and falling back to
GTK/Cairo draw-only timing. If neither baseline is available, the comparison is
reported as unavailable rather than passed. The comparison row records its
source, pixels, DPI, frame count, and Simple execution mode so retained reports
cannot be mistaken for a smaller or interpreter-backed run.
Simple CPU rows run in `SIMPLE_WEB_CPU_MODE=native` by default and fail closed
if the runner reports interpreter fallback.
Simple CPU render-loop rows default to 300dpi retina metadata. Pass `--dpi N`
to override it; the report keeps `logical_pixels` and `physical_pixels` equal to
the requested benchmark dimensions so DPI evidence cannot hide a smaller render.
Use `scripts/check/check-cpu-simd-render-dpi-contract.shs` for the focused
default/override contract check.
Use `scripts/check/check-cpu-simd-render-scale-contract.shs` for the focused
CPU-SIMD 4K/8K no-reduction contract; it fails closed on fallback, missing
checksum/nonzero-pixel proof, missing timing, or reduced logical/physical size.

### Current Simple Backend Evidence (2026-07-08 smoke)

`doc/09_report/gui_perf_benchmark_2026-07-08.md` is the canonical linked smoke
report for the current Simple backend profile. It was regenerated at
7680x4320, 1 frame, 300dpi, with `SIMPLE_WEB_CPU_MODE=native` and
`profile_report_contract=true`.

| Backend | Frame p50 | Frame p95 | Status | Measurement |
|---------|-----------|-----------|--------|-------------|
| Simple Web CPU-SIMD | 1282.166 ms | 1282.166 ms | valid | Native CPU-SIMD render-loop row, checksum `sum32:135445232233405312`, `nonzero_pixels:33177600` |
| Simple Web software | 909.530 ms | 909.530 ms | valid | Native scalar software render-loop row, same checksum and pixel proof as CPU-SIMD |
| Simple CUDA fill | n/a | n/a | unavailable | CUDA row did not complete in this CPU-SIMD-focused run |

The 2026-07-08 run is the current full-size CPU drawing comparison. It proves
the CPU-SIMD and scalar software paths preserve checksum and full 8K pixel
coverage with no screen-size reduction; it does not claim the CUDA lane passed
on that host. It also records `gui_perf_cpu_base_compare_target_met=no` against
Node Canvas/Cairo; the open blocker is
`doc/08_tracking/bug/cpu_simd_external_cairo_8k_perf_gap_2026-07-09.md`.

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

BUILD_DIR=build/gui_perf_bench_cpu REPORT_PATH=doc/09_report/gui_perf_benchmark_cpu.md \
  tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60 --dpi 300

# No-hardware summary contract for CUDA/Vulkan local perf output:
sh scripts/check/check-local-gpu-perf-summary.shs
```

The no-hardware summary contract must report
`gpu_perf_summary_contract=verdict-timing-overhead` plus explicit
`gpu_perf_summary_case_*` pass markers for both canonical runner paths, proving
the self-test still covers faster, near-CPU, slower-overhead, ambiguous generic
speedup, timing-line parsing, fail precedence, and missing-contract/case-marker
rejection.

## Pixel Parity Gate

"Do not cheat" — optimizations must not change pixel output.

1. `production_gui_web_renderer_parity.spl` — exact software/cpu_simd/metal match
2. `backend_parity.spl` — framebuffer vs software byte-for-byte
3. `golden_gate.spl` — golden-image drift, exact-only acceptance

For focused backend execution evidence, run
`scripts/check/check-production-gui-web-backend-executed-evidence.shs`. It keeps
the Metal/OpenCL/Vulkan same-frame readback subset separate from the CPU-SIMD
alpha quality check and requires `production_gui_backend_cpu_simd_alpha_quality_status=pass`.
Timing budget fields are emitted as pass/warn scheduling evidence; correctness
status is driven by parity, readback, and CPU-SIMD quality gates.

## Optimization Opportunities

### CUDA (highest impact, measured smoke; needs 8K repeats)
- Persistent device buffer reuse (skip 127 MB alloc/free per frame)
- Async readback via `cuMemcpyDtoHAsync` + stream sync
- Module caching already in `CudaSession.module_cache`

### Software rasterizer
- Engine2D Simple scalar is 31x slower than C scalar for fill at 1080p
- Key optimization: the Simple-to-C compilation gap, not algorithmic
- CPU SIMD (AVX2) backend exists. The benchmark harness now records
  `simple_web_cpu_simd` separately from `simple_web_software`, but still needs
  release-grade 8K throughput measurement before making a speed claim.
- CPU drawing-library comparison is emitted as `gui_perf_cpu_base_compare_*`
  fields in `tools/gui_perf_bench/run_all_benchmarks.shs`. The Simple CPU rows
  use `SIMPLE_WEB_CPU_MODE=native` by default; override only for diagnostics.
- CPU render-loop DPI evidence defaults to 300dpi retina metadata and is
  configurable through `--dpi` without changing the requested pixel dimensions.
  The focused wrapper is `scripts/check/check-cpu-simd-render-dpi-contract.shs`.
- CPU-SIMD alpha quality is gated by
  `scripts/check/check-production-gui-web-backend-executed-evidence.shs`; the
  wrapper requires semi-transparent fill output to match software exactly and
  records the alpha hit count/checksums.
- CPU-SIMD arch coverage is gated by
  `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs`. It reuses
  `check-cpu-simd-engine2d-evidence.shs` for x86_64, aarch64, and riscv64,
  records each architecture independently, and supports
  `CPU_SIMD_ARCH_MATRIX_STRICT=1` when all full native SIMD evidence rows are
  expected to pass. Current retained matrix evidence is split into three
  signals: x86_64 full Engine2D SIMD evidence passes on this host;
  cross-target native-build smoke passes for x86_64, aarch64, and riscv64 when
  target builds are enabled; full aarch64/riscv64 SIMD evidence rows remain
  unavailable until matching target Simple binaries are supplied. The wrapper
  also cross-compiles the native runtime owner for x86_64, aarch64, generic
  riscv64, and `rv64gcv` RVV when compilers are present. riscv64 native RVV
  target proof remains tracked at
  `doc/08_tracking/bug/cpu_simd_engine2d_rvv_native_rows_missing_2026-07-08.md`.
- CPU-SIMD 4K/8K scale evidence is gated by
  `scripts/check/check-cpu-simd-render-scale-contract.shs`. It runs native
  CPU-SIMD rows at 3840x2160 and 7680x4320, requires full logical/physical
  dimensions, 300dpi retina metadata, checksum/nonzero-pixel proof, scalar
  software checksum parity for the same scene/dimensions, p50/p95 timing for
  both CPU-SIMD and software baseline rows, a software-vs-SIMD p50 ratio, and
  no fallback/unavailable reason. Latest retained evidence:
  `doc/09_report/cpu_simd_render_scale_contract_2026-07-08.md`.
- `SIMPLE_WEB_GPU_PAINT=1` now allows `cpu_simd` through the per-primitive
  Engine2D paint path for focused experiments; the default upload-bound
  software/GPU present path is unchanged.
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
2. **CPU SIMD at 8K**: AVX2 backend has a dedicated `simple_web_cpu_simd`
   benchmark row and CPU drawing-library compare fields. The focused native
   scale contract captures 8K p50/p95 timing, no-reduction proof, checksum
   parity, and software-baseline timing. Current retained 4K and 8K ratios are
   both above `1000`; keep multiple-frame repeats before making broad
   release-grade CPU-SIMD speedup claims.
   Cross-arch target-native-build smoke now builds and runs x86_64, aarch64,
   and riscv64 outputs. Completion still needs current aarch64 NEON and
   riscv64 RVV Simple SIMD runtime matrix rows, plus strict mode with matching
   target Simple binaries, before those rows can pass as native SIMD rather
   than scalar-correct.
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
