# GUI Performance Profile

**Date:** 2026-06-06T09:04:24+00:00
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
gui_perf_benchmark_resolution=320x240
gui_perf_benchmark_frames=1
gui_perf_benchmark_cold_startup_ms=75.55
gui_perf_benchmark_warm_total_ms=0.04
gui_perf_benchmark_frame_time_avg_ms=0.000
gui_perf_benchmark_frame_time_p50_ms=0.000
gui_perf_benchmark_frame_time_p95_ms=0.000
gui_perf_benchmark_frame_time_max_ms=0.000
gui_perf_benchmark_draw_only_avg_ms=0.035
gui_perf_benchmark_pixel_count=76800
gui_perf_benchmark_bytes_per_frame=307200
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=81152
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
gui_perf_benchmark_cold_startup_ms=0.42
gui_perf_benchmark_warm_total_ms=0.29
gui_perf_benchmark_frame_time_avg_ms=0.286
gui_perf_benchmark_frame_time_p50_ms=0.286
gui_perf_benchmark_frame_time_p95_ms=0.286
gui_perf_benchmark_frame_time_max_ms=0.286
gui_perf_benchmark_pixel_count=76800
gui_perf_benchmark_bytes_per_frame=307200
gui_perf_benchmark_pixel_checksum=32801960
gui_perf_benchmark_status=completed
```
gui_perf_benchmark_max_rss_kb=64000
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
(backend_comparison_samples sample_count: 6 valid: false
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "metal" shell: "simple-web" requested: "metal" selected: "metal" device_id: "" status: "Unavailable" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 0 cold_start_us: 0 warm_start_us: 0 p50_frame_us: 0 p95_frame_us: 0 p95_input_to_paint_us: 0 max_rss_kb: 0 binary_size_bytes: 0 baseline_binary_size_bytes: 0 binary_size_delta_bytes: 0 package_size_bytes: 0 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "simple_2d_copy_u32" generated_entry_symbol: "simple_2d_copy_u32" generated_source_format: "metal-shading-language" generated_binary_format: "metallib" generated_artifact_path_suffix: "simple_2d_optimization.metallib" runtime_compute_target: "metal" runtime_execution_path: "generated_2d_kernel" runtime_launch_api: "MTLComputeCommandEncoder.dispatchThreads" runtime_entry_symbol: "simple_2d_copy_u32" runtime_artifact_name: "simple_2d_optimization.metallib" runtime_status: "runtime-unavailable" checksum: "" pixel_proof: "" scalar_baseline_compared: false fallback_used: false fallback_reason: "" unavailable_reason: "Metal requires macOS")
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "vulkan" shell: "simple-web" requested: "vulkan" selected: "vulkan" device_id: "" status: "Unavailable" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 0 cold_start_us: 0 warm_start_us: 0 p50_frame_us: 0 p95_frame_us: 0 p95_input_to_paint_us: 0 max_rss_kb: 0 binary_size_bytes: 0 baseline_binary_size_bytes: 0 binary_size_delta_bytes: 0 package_size_bytes: 0 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "" generated_entry_symbol: "" generated_source_format: "none" generated_binary_format: "none" generated_artifact_path_suffix: "" runtime_compute_target: "unsupported" runtime_execution_path: "generated_2d_kernel" runtime_launch_api: "none" runtime_entry_symbol: "" runtime_artifact_name: "" runtime_status: "plan-not-ready:backend-inactive" checksum: "" pixel_proof: "" scalar_baseline_compared: false fallback_used: false fallback_reason: "" unavailable_reason: "vulkan probe unavailable in interpreter")
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "cuda" shell: "simple-web" requested: "cuda" selected: "cuda" device_id: "" status: "Failed" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 0 cold_start_us: 0 warm_start_us: 0 p50_frame_us: 0 p95_frame_us: 0 p95_input_to_paint_us: 0 max_rss_kb: 0 binary_size_bytes: 0 baseline_binary_size_bytes: 0 binary_size_delta_bytes: 0 package_size_bytes: 0 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "simple_2d_copy_u32" generated_entry_symbol: "simple_2d_copy_u32" generated_source_format: "cuda-c" generated_binary_format: "ptx" generated_artifact_path_suffix: "simple_2d_optimization.ptx" runtime_compute_target: "cuda" runtime_execution_path: "generated_2d_kernel" runtime_launch_api: "rt_cuda_launch_kernel" runtime_entry_symbol: "simple_2d_copy_u32" runtime_artifact_name: "simple_2d_optimization.ptx" runtime_status: "cuda-runtime-unavailable" checksum: "" pixel_proof: "" scalar_baseline_compared: false fallback_used: false fallback_reason: "" unavailable_reason: "backend-specific measurement missing")
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "opencl" shell: "simple-web" requested: "opencl" selected: "opencl" device_id: "" status: "Unavailable" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 0 cold_start_us: 0 warm_start_us: 0 p50_frame_us: 0 p95_frame_us: 0 p95_input_to_paint_us: 0 max_rss_kb: 0 binary_size_bytes: 0 baseline_binary_size_bytes: 0 binary_size_delta_bytes: 0 package_size_bytes: 0 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "simple_2d_copy_u32" generated_entry_symbol: "simple_2d_copy_u32" generated_source_format: "opencl-c" generated_binary_format: "spirv" generated_artifact_path_suffix: "simple_2d_optimization.spirv" runtime_compute_target: "opencl" runtime_execution_path: "generated_2d_kernel" runtime_launch_api: "clEnqueueNDRangeKernel" runtime_entry_symbol: "simple_2d_copy_u32" runtime_artifact_name: "simple_2d_optimization.spirv" runtime_status: "opencl-runtime-or-queue-unavailable" checksum: "" pixel_proof: "" scalar_baseline_compared: false fallback_used: false fallback_reason: "" unavailable_reason: "OpenCL session proof failed: OpenClSessionEvidence[op=init success=false status=context-unavailable reason=opencl-context-create-failed platform=1 context=0 queue=0 program=0 kernel=0 generation=0 readback=false expected=0 actual=0]")
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "hip" shell: "simple-web" requested: "rocm" selected: "rocm" device_id: "" status: "Unavailable" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 0 cold_start_us: 0 warm_start_us: 0 p50_frame_us: 0 p95_frame_us: 0 p95_input_to_paint_us: 0 max_rss_kb: 0 binary_size_bytes: 0 baseline_binary_size_bytes: 0 binary_size_delta_bytes: 0 package_size_bytes: 0 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "" offload_tag_kind: "@gpu" operation_family: "text_blit" generated_operation: "simple_2d_copy_u32" generated_entry_symbol: "simple_2d_copy_u32" generated_source_format: "hip-cpp" generated_binary_format: "hsaco" generated_artifact_path_suffix: "simple_2d_optimization.hsaco" runtime_compute_target: "hip" runtime_execution_path: "generated_2d_kernel" runtime_launch_api: "rt_rocm_launch_kernel" runtime_entry_symbol: "simple_2d_copy_u32" runtime_artifact_name: "simple_2d_optimization.hsaco" runtime_status: "hip-runtime-unavailable" checksum: "" pixel_proof: "" scalar_baseline_compared: false fallback_used: false fallback_reason: "" unavailable_reason: "ROCm/HIP probe unavailable in interpreter")
  (backend_comparison_sample fixture_id: "gui-perf-8k-fill" backend_family: "cpu_simd" shell: "simple-web" requested: "cpu_simd" selected: "cpu_simd" device_id: "host-cpu" status: "Initialized" command: "bench-8k" host: "dl" warmup_count: 0 sample_count: 0 cold_start_us: 0 warm_start_us: 0 p50_frame_us: 0 p95_frame_us: 0 p95_input_to_paint_us: 0 max_rss_kb: 0 binary_size_bytes: 0 baseline_binary_size_bytes: 0 binary_size_delta_bytes: 0 package_size_bytes: 0 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "startup-size-audit" offload_tag_kind: "baseline" operation_family: "cpu_simd" generated_operation: "cpu_simd_baseline" generated_entry_symbol: "RenderBackend" generated_source_format: "engine2d-cpu" generated_binary_format: "none" generated_artifact_path_suffix: "" runtime_compute_target: "cpu_simd" runtime_execution_path: "engine2d-cpu-simd" runtime_launch_api: "RenderBackend" runtime_entry_symbol: "RenderBackend" runtime_artifact_name: "" runtime_status: "cpu-simd-baseline-ready" checksum: "sha256:unmeasured" pixel_proof: "startup-size-only" scalar_baseline_compared: true fallback_used: false fallback_reason: "" unavailable_reason: "")
)
```
gui_perf_benchmark_max_rss_kb=287140
gui_perf_benchmark_exit_code=0

### simple_web_software

```text
(backend_comparison_samples sample_count: 1 valid: true
  (backend_comparison_sample fixture_id: "gui-perf-8k-software" backend_family: "software" shell: "simple-web" requested: "software" selected: "software" device_id: "host-cpu" status: "Initialized" command: "bench-8k" host: "dl" warmup_count: 1 sample_count: 1 cold_start_us: 3439796 warm_start_us: 3266908 p50_frame_us: 3266908 p95_frame_us: 3266908 p95_input_to_paint_us: 3266908 max_rss_kb: 1 binary_size_bytes: 44980744 baseline_binary_size_bytes: 44980744 binary_size_delta_bytes: 0 package_size_bytes: 44980744 artifact_build_us: 0 artifact_load_us: 0 artifact_submit_us: 0 artifact_sync_us: 0 artifact_readback_us: 0 render_readback_scope: "render+readback" offload_tag_kind: "baseline" operation_family: "text_blit" generated_operation: "simple_web_render_html_to_pixels" generated_entry_symbol: "RenderBackend.draw_text_or_text_blit" generated_source_format: "simple" generated_binary_format: "none" generated_artifact_path_suffix: "" runtime_compute_target: "cpu_scalar" runtime_execution_path: "engine2d-cpu_scalar" runtime_launch_api: "RenderBackend" runtime_entry_symbol: "RenderBackend.draw_text_or_text_blit" runtime_artifact_name: "" runtime_status: "cpu-render-loop-ready" checksum: "sum32:328820832230016" pixel_proof: "nonzero_pixels:76800" scalar_baseline_compared: true fallback_used: false fallback_reason: "" unavailable_reason: "")
)
```
gui_perf_benchmark_max_rss_kb=217344
gui_perf_benchmark_exit_code=0

## Reproducibility

Run from the repository root:

```sh
tools/gui_perf_bench/run_all_benchmarks.shs --width 320 --height 240 --frames 1
```

Useful knobs: `WIDTH`, `HEIGHT`, `FRAMES`, `BUILD_DIR`, and `REPORT_PATH`.

Per-backend stdout/stderr files are written under `build/gui_perf_bench`.

## Limitations

- Headless hosts need `xvfb-run` for GTK; without it GTK is recorded as failed or unavailable.
- Electron, Tauri, CUDA, and Node canvas rows depend on host-installed tools.
- Backend rows that print startup-only or unmeasured fields must not be used as frame-time evidence.
- The report compares available lanes on one host; release claims need repeated runs on the target platform.

Benchmark complete. Full report: `doc/09_report/gui_perf_benchmark_2026-06-06.md`
