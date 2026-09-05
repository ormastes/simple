# GUI Performance Profile

**Date:** 2026-08-11T15:36:50+00:00
**Resolution:** 7680x4320
**Frames:** 1
**DPI:** 300
**Simple Web CPU mode:** native
**Profile script:** `tools/gui_perf_bench/run_all_benchmarks.shs`
**Report path:** `doc/09_report/gui_perf_benchmark_2026-08-11.md`

## Methodology

- Builds or invokes available GUI/backend lanes and records each backend separately.
- Captures stdout, stderr, exit status, and maximum resident set size with `/usr/bin/time -v`.
- Marks unavailable dependencies and failed backends explicitly; skipped rows are environment facts, not performance wins.
- Uses the same resolution and frame count for all lanes that can accept those knobs.

## Environment

- Host: `dl`
- OS: `x86_64 / Linux 6.8.0-137-generic`
- GPU: `NVIDIA RTX A6000`
- Build dir: `build/gui_perf_bench`

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
gui_perf_benchmark_cold_startup_ms=95.00
gui_perf_benchmark_warm_total_ms=81.92
gui_perf_benchmark_frame_time_avg_ms=0.000
gui_perf_benchmark_frame_time_p50_ms=0.000
gui_perf_benchmark_frame_time_p95_ms=0.000
gui_perf_benchmark_frame_time_max_ms=0.000
gui_perf_benchmark_draw_only_avg_ms=81.922
gui_perf_benchmark_pixel_count=33177600
gui_perf_benchmark_bytes_per_frame=132710400
gui_perf_benchmark_argb_sum32=sum32:141975141816729600
gui_perf_benchmark_fixture=gui-perf-cpu-base-solid
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=208128
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
gui_perf_benchmark_cold_startup_ms=0.82
gui_perf_benchmark_warm_total_ms=81.83
gui_perf_benchmark_frame_time_avg_ms=81.819
gui_perf_benchmark_frame_time_p50_ms=81.819
gui_perf_benchmark_frame_time_p95_ms=81.819
gui_perf_benchmark_frame_time_max_ms=81.819
gui_perf_benchmark_pixel_count=33177600
gui_perf_benchmark_bytes_per_frame=132710400
gui_perf_benchmark_pixel_checksum=11645337600
gui_perf_benchmark_argb_sum32=sum32:141975141816729600
gui_perf_benchmark_fixture=gui-perf-cpu-base-solid
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=325296
gui_perf_benchmark_exit_code=0

--- electron: SKIPPED (electron not installed) ---
gui_perf_benchmark_backend=electron
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=electron binary not found; existing contract reports cold_startup=4075ms

--- tauri: integration pending ---
gui_perf_benchmark_backend=tauri
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=tauri benchmark app not yet built; requires cargo-tauri + webview2
--- pure_simple_cuda: SKIPPED ---
gui_perf_benchmark_backend=pure_simple_cuda
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=self-hosted Simple compiler binary not found

--- simple_web_cpu_simd/simple_web_software: SKIPPED ---
gui_perf_benchmark_backend=simple_web_cpu_simd,simple_web_software
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=self-hosted Simple compiler binary not found

## CPU Drawing Library Baseline Compare

gui_perf_cpu_base_compare_source=gui_perf_bench_external_cpu_library
gui_perf_cpu_base_compare_pixels=7680x4320
gui_perf_cpu_base_compare_dpi=300
gui_perf_cpu_base_compare_dpi_source=
gui_perf_cpu_base_compare_frames=1
gui_perf_cpu_base_compare_simple_mode=native
gui_perf_cpu_base_compare_simple_launch_kind=run
gui_perf_cpu_base_compare_simple_native_artifact_used=false
gui_perf_cpu_base_compare_schedule_order=cpu_simd_first
gui_perf_cpu_base_compare_physical_pixels=
gui_perf_cpu_base_compare_screen_size_reduced=
gui_perf_cpu_base_compare_simple_checksum=
gui_perf_cpu_base_compare_simple_pixel_proof=
gui_perf_cpu_base_compare_runtime_compute_target=
gui_perf_cpu_base_compare_runtime_execution_path=
gui_perf_cpu_base_compare_render_readback_scope=
gui_perf_cpu_base_compare_offload_tag_kind=
gui_perf_cpu_base_compare_simd_provider_hits=
gui_perf_cpu_base_compare_native_simd_executed=
gui_perf_cpu_base_compare_fallback_used=
gui_perf_cpu_base_compare_status=unavailable
gui_perf_cpu_base_compare_reason=self_hosted_simple_compiler_unavailable

## Reproducibility

Run from the repository root:

```sh
tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 1 --dpi 300
```

Useful knobs: `WIDTH`, `HEIGHT`, `FRAMES`, `DPI`, `SIMPLE_WEB_CPU_MODE`, `BUILD_DIR`, and `REPORT_PATH`.

Per-backend stdout/stderr files are written under `build/gui_perf_bench`.

## Limitations

- Headless hosts need `xvfb-run` for GTK; without it GTK is recorded as failed or unavailable.
- Electron, Tauri, CUDA, and Node canvas rows depend on host-installed tools.
- Backend rows that print startup-only or unmeasured fields must not be used as frame-time evidence.
- The report compares available lanes on one host; release claims need repeated runs on the target platform.

Benchmark complete. Full report: `doc/09_report/gui_perf_benchmark_2026-08-11.md`
FAIL: status must be completed
render_8k80_receipt_gate=false
