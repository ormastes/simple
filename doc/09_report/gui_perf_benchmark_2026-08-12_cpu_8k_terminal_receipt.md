# GUI Performance Profile

**Date:** 2026-08-12T02:02:56+00:00
**Resolution:** 7680x4320
**Frames:** 1
**DPI:** 300
**Simple Web CPU mode:** native
**Profile script:** `tools/gui_perf_bench/run_all_benchmarks.shs`
**Report path:** `doc/09_report/gui_perf_benchmark_2026-08-12_cpu_8k_terminal_receipt.md`

## Methodology

- Builds or invokes available GUI/backend lanes and records each backend separately.
- Captures stdout, stderr, exit status, and maximum resident set size with `/usr/bin/time -v`.
- Marks unavailable dependencies and failed backends explicitly; skipped rows are environment facts, not performance wins.
- Uses the same resolution and frame count for all lanes that can accept those knobs.

## Environment

- Host: `dl`
- OS: `x86_64 / Linux 6.8.0-137-generic`
- GPU: `NVIDIA RTX A6000`
- Build dir: `build/gui_perf_bench_cpu_8k_terminal_receipt`

## TUI startup speed

TUI startup speed is not measured by this GUI profile. The canonical startup audit is
`scripts/check/check-startup-size-performance-audit.shs`, which reports
`Simple standalone TUI` and `Simple full TUI app` rows in
`doc/09_report/startup_size_performance_audit_2026-05-27.md`.

## Backend Results

### gtk3

```text
gui_perf_benchmark_backend=gtk3
gui_perf_benchmark_resolution=7680x4320
gui_perf_benchmark_frames=1
gui_perf_benchmark_cold_startup_ms=158.94
gui_perf_benchmark_warm_total_ms=97.17
gui_perf_benchmark_frame_time_avg_ms=0.000
gui_perf_benchmark_frame_time_p50_ms=0.000
gui_perf_benchmark_frame_time_p95_ms=0.000
gui_perf_benchmark_frame_time_max_ms=0.000
gui_perf_benchmark_draw_only_avg_ms=97.173
gui_perf_benchmark_pixel_count=33177600
gui_perf_benchmark_bytes_per_frame=132710400
gui_perf_benchmark_argb_sum32=sum32:141975141816729600
gui_perf_benchmark_fixture=gui-perf-cpu-base-solid
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=207360
gui_perf_benchmark_exit_code=0

--- python_tkinter: SKIPPED (tkinter not found) ---
gui_perf_benchmark_backend=python_tkinter
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=python3 tkinter not available

### javascript_node

```text
gui_perf_benchmark_backend=javascript_node_canvas
gui_perf_benchmark_resolution=7680x4320
gui_perf_benchmark_frames=1
gui_perf_benchmark_cold_startup_ms=1.88
gui_perf_benchmark_warm_total_ms=95.10
gui_perf_benchmark_frame_time_avg_ms=95.085
gui_perf_benchmark_frame_time_p50_ms=95.085
gui_perf_benchmark_frame_time_p95_ms=95.085
gui_perf_benchmark_frame_time_max_ms=95.085
gui_perf_benchmark_pixel_count=33177600
gui_perf_benchmark_bytes_per_frame=132710400
gui_perf_benchmark_pixel_checksum=11645337600
gui_perf_benchmark_argb_sum32=sum32:141975141816729600
gui_perf_benchmark_fixture=gui-perf-cpu-base-solid
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=325632
gui_perf_benchmark_exit_code=0

--- electron: SKIPPED (electron not installed) ---
gui_perf_benchmark_backend=electron
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=electron binary not found; existing contract reports cold_startup=4075ms

--- tauri: integration pending ---
gui_perf_benchmark_backend=tauri
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=tauri benchmark app not yet built; requires cargo-tauri + webview2
### pure_simple_cuda

gui_perf_benchmark_backend=pure_simple_cuda
gui_perf_benchmark_status=failed
gui_perf_benchmark_exit_code=143
```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Deprecated syntax for type parameters
  --> /home/ormastes/dev/pub/simple/src/lib/common/string_core.spl:116:44
   |
116 |     while i < slen and is_whitespace_char(s[i]):
   |                                            ^

Use angle brackets: s<...> instead of s[...]

Run `simple migrate --fix-generics` to automatically update your code

[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /home/ormastes/dev/pub/simple/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:3:1
   |
  3 | export use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer_core.*
   | ^

Use explicit exports instead

```

### simple_web_cpu_simd

gui_perf_benchmark_backend=simple_web_cpu_simd
gui_perf_benchmark_status=failed
gui_perf_benchmark_exit_code=143
```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /home/ormastes/dev/pub/simple/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:3:1
   |
  3 | export use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer_core.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module

[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /home/ormastes/dev/pub/simple/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:4:1
   |
  4 | export use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer_paint_layout.*
   | ^

Use explicit exports instead

```

### simple_web_software

## Terminal-receipt verdict

**INVALID AS A COMPLETE HARNESS RUN.** The outer dedicated process group hit
its 180-second deadline while the harness was in `simple_web_software`. A
SIGTERM delivered to that process group prevented the shell EXIT trap from
appending `gui_perf_benchmark_harness_status`; therefore this file has no
terminal harness receipt. It must not be used for a Simple CPU backend timing,
RSS, checksum, or 8K/80 claim.

The completed GTK and Node rows above are retained as their own measured
external reference rows. Both are approximately 95–97 ms for one 8K solid
frame and thus do not meet an 80 fps (12.5 ms) target. CUDA and Simple rows
were incomplete/failed and are not measurements.

The harness source now emits a terminal receipt on ordinary shell failure, but
an outer hard process-group kill can still prevent any cleanup handler. Future
benchmark control must let the harness own its deadline or provide an external
supervisor receipt written outside the killed group.
