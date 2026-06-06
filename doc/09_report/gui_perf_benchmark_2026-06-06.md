# GUI Performance Profile

**Date:** 2026-06-06T09:51:02+00:00
**Resolution:** 320x240
**Frames:** 1
**Profile script:** `tools/gui_perf_bench/run_all_benchmarks.shs`
**Report path:** `doc/09_report/gui_perf_benchmark_2026-06-06.md`

## Methodology

- Builds or invokes available GUI/backend lanes and records each backend separately.
- Captures stdout, stderr, exit status, and maximum resident set size with `/usr/bin/time -v`.
- Marks unavailable dependencies and failed backends explicitly; skipped rows are environment facts, not performance wins.
- Uses the same resolution and frame count for all lanes that can accept those knobs.

## Environment

- Host: `dl`
- OS: `x86_64 / Linux 6.8.0-117-generic`
- GPU: `NVIDIA RTX A6000`
- Build dir: `build/profile_reporting/gui`

## TUI startup speed

TUI startup speed is not measured by this GUI profile. The canonical startup audit is
`scripts/check/check-startup-size-performance-audit.shs`, which reports
`Simple standalone TUI` and `Simple full TUI app` rows in
`doc/09_report/startup_size_performance_audit_2026-05-27.md`.

## Backend Results

### gtk3

```text
gui_perf_benchmark_backend=gtk3
gui_perf_benchmark_resolution=320x240
gui_perf_benchmark_frames=1
gui_perf_benchmark_cold_startup_ms=73.51
gui_perf_benchmark_warm_total_ms=0.03
gui_perf_benchmark_frame_time_avg_ms=0.000
gui_perf_benchmark_frame_time_p50_ms=0.000
gui_perf_benchmark_frame_time_p95_ms=0.000
gui_perf_benchmark_frame_time_max_ms=0.000
gui_perf_benchmark_draw_only_avg_ms=0.023
gui_perf_benchmark_pixel_count=76800
gui_perf_benchmark_bytes_per_frame=307200
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=80896
gui_perf_benchmark_exit_code=0

--- python_tkinter: SKIPPED (tkinter not found) ---
gui_perf_benchmark_backend=python_tkinter
gui_perf_benchmark_status=unavailable
gui_perf_benchmark_reason=python3 tkinter not available

### javascript_node

```text
gui_perf_benchmark_backend=javascript_node_canvas
gui_perf_benchmark_resolution=320x240
gui_perf_benchmark_frames=1
gui_perf_benchmark_cold_startup_ms=0.62
gui_perf_benchmark_warm_total_ms=0.29
gui_perf_benchmark_frame_time_avg_ms=0.292
gui_perf_benchmark_frame_time_p50_ms=0.292
gui_perf_benchmark_frame_time_p95_ms=0.292
gui_perf_benchmark_frame_time_max_ms=0.292
gui_perf_benchmark_pixel_count=76800
gui_perf_benchmark_bytes_per_frame=307200
gui_perf_benchmark_pixel_checksum=32801960
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=64512
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

```text
(backend_comparison_samples sample_count: 1 valid: true
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "cuda" shell: "simple-web" requested: "cuda" selected: "cuda" device_id: "cuda:0" status: "Initialized" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 1 cold_start_us: 131452 warm_start_us: 130991 p50_frame_us: 528 p95_frame_us: 528 p95_input_to_paint_us: 528 max_rss_kb: 1 binary_size_bytes: 1 baseline_binary_size_bytes: 1 binary_size_delta_bytes: 0 package_size_bytes: 1 artifact_build_us: 461 artifact_load_us: 130463 artifact_submit_us: 379 artifact_sync_us: 16 artifact_readback_us: 133 render_readback_scope: "render+readback" offload_tag_kind: "@gpu" operation_family: "fill" generated_operation: "simple_2d_fill_u32" generated_entry_symbol: "simple_2d_fill_u32" generated_source_format: "cuda-c" generated_binary_format: "ptx" generated_artifact_path_suffix: "simple_2d_optimization.ptx" runtime_compute_target: "cuda" runtime_execution_path: "generated_2d_kernel" runtime_launch_api: "rt_cuda_launch_kernel" runtime_entry_symbol: "simple_2d_fill_u32" runtime_artifact_name: "simple_2d_optimization.ptx" runtime_status: "ready" checksum: "sum32:328570011648000" pixel_proof: "nonzero_pixels:76800" scalar_baseline_compared: true fallback_used: false fallback_reason: "" unavailable_reason: "")
)
```
gui_perf_benchmark_max_rss_kb=272604
gui_perf_benchmark_exit_code=0

### simple_web_software

```text
(backend_comparison_samples sample_count: 1 valid: true
  (backend_comparison_sample fixture_id: "gui-perf-8k-software" backend_family: "software" shell: "simple-web" requested: "software" selected: "software" device_id: "host-software" status: "Initialized" command: "bench-8k" host: "dl" warmup_count: 1 sample_count: 1 cold_start_us: 20821511 warm_start_us: 20821511 p50_frame_us: 20821511 p95_frame_us: 20821511 p95_input_to_paint_us: 20821511 max_rss_kb: 1 binary_size_bytes: 213 baseline_binary_size_bytes: 213 binary_size_delta_bytes: 0 package_size_bytes: 213 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 20821511 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "software-render-loop" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "" generated_entry_symbol: "" generated_source_format: "none" generated_binary_format: "none" generated_artifact_path_suffix: "" runtime_compute_target: "cpu_scalar" runtime_execution_path: "engine2d-cpu_scalar" runtime_launch_api: "RenderBackend" runtime_entry_symbol: "RenderBackend.draw_text_or_text_blit" runtime_artifact_name: "" runtime_status: "cpu-scalar-baseline-ready" checksum: "sum32:328745677397784" pixel_proof: "nonzero_pixels:76800" scalar_baseline_compared: true fallback_used: false fallback_reason: "" unavailable_reason: "")
)
```
gui_perf_benchmark_max_rss_kb=199096
gui_perf_benchmark_exit_code=0

## Reproducibility

Run from the repository root:

```sh
tools/gui_perf_bench/run_all_benchmarks.shs --width 320 --height 240 --frames 1
```

Useful knobs: `WIDTH`, `HEIGHT`, `FRAMES`, `BUILD_DIR`, and `REPORT_PATH`.

Per-backend stdout/stderr files are written under `build/profile_reporting/gui`.

## Limitations

- Headless hosts need `xvfb-run` for GTK; without it GTK is recorded as failed or unavailable.
- Electron, Tauri, CUDA, and Node canvas rows depend on host-installed tools.
- Backend rows that print startup-only or unmeasured fields must not be used as frame-time evidence.
- The report compares available lanes on one host; release claims need repeated runs on the target platform.

Benchmark complete. Full report: `doc/09_report/gui_perf_benchmark_2026-06-06.md`
