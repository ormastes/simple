# GUI Performance Profile

**Date:** 2026-07-09T18:53:37+00:00
**Resolution:** 7680x4320
**Frames:** 1
**DPI:** 300
**Simple Web CPU mode:** native
**Profile script:** `tools/gui_perf_bench/run_all_benchmarks.shs`
**Report path:** `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`

## Methodology

- Builds or invokes available GUI/backend lanes and records each backend separately.
- Captures stdout, stderr, exit status, and maximum resident set size with `/usr/bin/time -v`.
- Marks unavailable dependencies and failed backends explicitly; skipped rows are environment facts, not performance wins.
- Uses the same resolution and frame count for all lanes that can accept those knobs.

## Environment

- Host: `dl`
- OS: `x86_64 / Linux 6.8.0-124-generic`
- GPU: `NVIDIA RTX A6000`
- Build dir: `build/gui_perf_bench_2026-07-09_cpu_base`

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
gui_perf_benchmark_cold_startup_ms=75.18
gui_perf_benchmark_warm_total_ms=0.04
gui_perf_benchmark_frame_time_avg_ms=0.000
gui_perf_benchmark_frame_time_p50_ms=0.000
gui_perf_benchmark_frame_time_p95_ms=0.000
gui_perf_benchmark_frame_time_max_ms=0.000
gui_perf_benchmark_draw_only_avg_ms=0.035
gui_perf_benchmark_pixel_count=33177600
gui_perf_benchmark_bytes_per_frame=132710400
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=81408
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
gui_perf_benchmark_cold_startup_ms=0.72
gui_perf_benchmark_warm_total_ms=73.90
gui_perf_benchmark_frame_time_avg_ms=73.892
gui_perf_benchmark_frame_time_p50_ms=73.892
gui_perf_benchmark_frame_time_p95_ms=73.892
gui_perf_benchmark_frame_time_max_ms=73.892
gui_perf_benchmark_pixel_count=33177600
gui_perf_benchmark_bytes_per_frame=132710400
gui_perf_benchmark_pixel_checksum=12851353600
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=324096
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
[33mwarning[0m: Deprecated syntax for type parameters
  --> /home/ormastes/dev/pub/simple/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:3733:24
   |
3733 |     while a < b and (cb[a] == 32 or cb[a] == 9 or cb[a] == 10 or cb[a] == 13):
   |                        ^

Use angle brackets: cb<...> instead of cb[...]

Run `simple migrate --fix-generics` to automatically update your code

[33mwarning[0m: Deprecated syntax for type parameters
  --> /home/ormastes/dev/pub/simple/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:4753:58
   |
4753 |         if ri >= right_count or (li < left_count and left[li] <= right[ri]):
   |                                                          ^

Use angle brackets: left<...> instead of left[...]

Run `simple migrate --fix-generics` to automatically update your code

```

### simple_web_cpu_simd

```text
(backend_comparison_samples sample_count: 1 scalar_baseline_p50_us: 0 backend_faster_than_scalar_count: 0 backend_equal_to_scalar_count: 0 backend_slower_than_scalar_count: 0 offload_overhead_contained_count: 0 offload_overhead_dominates_count: 0 offload_useful_count: 0 offload_faster_but_overhead_dominates_count: 0 offload_break_even_count: 0 offload_slower_communication_overhead_count: 0 offload_slower_compute_bound_count: 0 offload_missing_scalar_baseline_count: 0 valid: true
  (backend_comparison_sample fixture_id: "gui-perf-8k-cpu-simd" backend_family: "cpu_simd" shell: "simple-web" requested: "cpu_simd" selected: "cpu_simd" device_id: "host-software" status: "Initialized" command: "bench-8k" host: "dl" warmup_count: 1 sample_count: 1 cold_start_us: 767872 warm_start_us: 767872 p50_frame_us: 767872 p95_frame_us: 767872 p95_input_to_paint_us: 767872 max_rss_kb: 1 binary_size_bytes: 54795064 baseline_binary_size_bytes: 54795064 binary_size_delta_bytes: 0 package_size_bytes: 54795064 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 767872 artifact_sync_us: 0 artifact_readback_us: 0 artifact_total_us: 767872 offload_overhead_verdict: "not-gpu-offload" speed_verdict: "missing-scalar-baseline" offload_efficiency_verdict: "not-gpu-offload" render_readback_scope: "software-render-loop" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "" generated_entry_symbol: "" generated_source_format: "none" generated_binary_format: "none" generated_artifact_path_suffix: "" runtime_compute_target: "cpu_simd" runtime_execution_path: "simple_web_layout_engine2d_cpu_simd" runtime_launch_api: "RenderBackend" runtime_entry_symbol: "RenderBackend.draw_text_or_text_blit" runtime_artifact_name: "" runtime_status: "cpu-simd-render-loop-ready" checksum: "sum32:135445232233405312" pixel_proof: "nonzero_pixels:33177600" scalar_baseline_compared: true fallback_used: false fallback_reason: "" unavailable_reason: "")
)
gui_perf_benchmark_dpi=300
gui_perf_benchmark_dpi_default=300
gui_perf_benchmark_dpi_source=default
gui_perf_benchmark_density_profile=retina
gui_perf_benchmark_logical_pixels=7680x4320
gui_perf_benchmark_physical_pixels=7680x4320
gui_perf_benchmark_screen_size_reduced=false
```
gui_perf_benchmark_max_rss_kb=901392
gui_perf_benchmark_exit_code=0

### simple_web_software

```text
(backend_comparison_samples sample_count: 1 scalar_baseline_p50_us: 799203 backend_faster_than_scalar_count: 0 backend_equal_to_scalar_count: 0 backend_slower_than_scalar_count: 0 offload_overhead_contained_count: 0 offload_overhead_dominates_count: 0 offload_useful_count: 0 offload_faster_but_overhead_dominates_count: 0 offload_break_even_count: 0 offload_slower_communication_overhead_count: 0 offload_slower_compute_bound_count: 0 offload_missing_scalar_baseline_count: 0 valid: true
  (backend_comparison_sample fixture_id: "gui-perf-8k-software" backend_family: "software" shell: "simple-web" requested: "software" selected: "software" device_id: "host-software" status: "Initialized" command: "bench-8k" host: "dl" warmup_count: 1 sample_count: 1 cold_start_us: 799203 warm_start_us: 799203 p50_frame_us: 799203 p95_frame_us: 799203 p95_input_to_paint_us: 799203 max_rss_kb: 1 binary_size_bytes: 54795064 baseline_binary_size_bytes: 54795064 binary_size_delta_bytes: 0 package_size_bytes: 54795064 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 799203 artifact_sync_us: 0 artifact_readback_us: 0 artifact_total_us: 799203 offload_overhead_verdict: "not-gpu-offload" speed_verdict: "backend-equal-to-scalar" offload_efficiency_verdict: "not-gpu-offload" render_readback_scope: "software-render-loop" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "" generated_entry_symbol: "" generated_source_format: "none" generated_binary_format: "none" generated_artifact_path_suffix: "" runtime_compute_target: "cpu_scalar" runtime_execution_path: "simple_web_layout_software" runtime_launch_api: "RenderBackend" runtime_entry_symbol: "RenderBackend.draw_text_or_text_blit" runtime_artifact_name: "" runtime_status: "cpu-scalar-baseline-ready" checksum: "sum32:135445232233405312" pixel_proof: "nonzero_pixels:33177600" scalar_baseline_compared: true fallback_used: false fallback_reason: "" unavailable_reason: "")
)
gui_perf_benchmark_dpi=300
gui_perf_benchmark_dpi_default=300
gui_perf_benchmark_dpi_source=default
gui_perf_benchmark_density_profile=retina
gui_perf_benchmark_logical_pixels=7680x4320
gui_perf_benchmark_physical_pixels=7680x4320
gui_perf_benchmark_screen_size_reduced=false
```
gui_perf_benchmark_max_rss_kb=941660
gui_perf_benchmark_exit_code=0

## CPU Drawing Library Baseline Compare

gui_perf_cpu_base_compare_source=gui_perf_bench_external_cpu_library
gui_perf_cpu_base_compare_pixels=7680x4320
gui_perf_cpu_base_compare_dpi=300
gui_perf_cpu_base_compare_dpi_source=default
gui_perf_cpu_base_compare_frames=1
gui_perf_cpu_base_compare_simple_mode=native
gui_perf_cpu_base_compare_schedule_order=cpu_simd_first
gui_perf_cpu_base_compare_physical_pixels=7680x4320
gui_perf_cpu_base_compare_screen_size_reduced=false
gui_perf_cpu_base_compare_simple_checksum=sum32:135445232233405312
gui_perf_cpu_base_compare_simple_pixel_proof=nonzero_pixels:33177600
gui_perf_cpu_base_compare_runtime_compute_target=cpu_simd
gui_perf_cpu_base_compare_runtime_execution_path=simple_web_layout_engine2d_cpu_simd
gui_perf_cpu_base_compare_render_readback_scope=software-render-loop
gui_perf_cpu_base_compare_offload_tag_kind=@gpu
gui_perf_cpu_base_compare_fallback_used=false
gui_perf_cpu_base_compare_status=measured
gui_perf_cpu_base_compare_simple_backend=simple_web_cpu_simd
gui_perf_cpu_base_compare_simple_p50_ms=767.872
gui_perf_cpu_base_compare_baseline_backend=javascript_node_canvas
gui_perf_cpu_base_compare_baseline_metric=frame_time_p50_ms
gui_perf_cpu_base_compare_baseline_ms=73.892
gui_perf_cpu_base_compare_baseline_over_simple_ratio=0.096
gui_perf_cpu_base_compare_target_met=no

## Reproducibility

Run from the repository root:

```sh
tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 1 --dpi 300
```

Useful knobs: `WIDTH`, `HEIGHT`, `FRAMES`, `DPI`, `SIMPLE_WEB_CPU_MODE`, `BUILD_DIR`, and `REPORT_PATH`.

Per-backend stdout/stderr files are written under `build/gui_perf_bench_2026-07-09_cpu_base`.

## Limitations

- Headless hosts need `xvfb-run` for GTK; without it GTK is recorded as failed or unavailable.
- Electron, Tauri, CUDA, and Node canvas rows depend on host-installed tools.
- Backend rows that print startup-only or unmeasured fields must not be used as frame-time evidence.
- The report compares available lanes on one host; release claims need repeated runs on the target platform.

Benchmark complete. Full report: `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`
