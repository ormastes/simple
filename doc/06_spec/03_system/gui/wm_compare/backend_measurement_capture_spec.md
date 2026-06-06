# Backend Measurement Capture Specification

> <details>

<!-- sdn-diagram:id=backend_measurement_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_measurement_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_measurement_capture_spec -> std
backend_measurement_capture_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_measurement_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Measurement Capture Specification

## Scenarios

### wm_compare backend measurement capture

#### parses repeated /usr/bin/time samples into p50 p95 and max RSS

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "sample=1 elapsed_s=37.71 max_rss_kb=929240\nsample=2 elapsed_s=38.58 max_rss_kb=930308\nsample=3 elapsed_s=38.89 max_rss_kb=930160\n"
val measurement = parse_usr_bin_time_measurements(
    "simple test backend_measurement_report_spec",
    "linux-x86_64",
    output,
    454623792,
    454623792,
    "backend-measurement-spec-startup"
)
expect(measurement.sample_count).to_equal(3)
expect(measurement.p50_us).to_equal(38580000)
expect(measurement.p95_us).to_equal(38890000)
expect(measurement.max_rss_kb).to_equal(930308)
```

</details>

#### converts host measurements into backend measurement records

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "sample=1 elapsed_s=1.00 max_rss_kb=100\nsample=2 elapsed_s=2.00 max_rss_kb=200\n"
val measurement = parse_usr_bin_time_measurements(
    "simple test representative comparison",
    "linux-x86_64",
    output,
    1000,
    1000,
    "render+readback"
)
val record = host_measurement_record(
    "cpu_simd", "cpu_simd", "Initialized",
    measurement,
    true,
    false,
    "host measurement"
)
expect(backend_measurement_initialized_valid(record)).to_equal(true)
val sdn = backend_measurement_record_sdn(record)
expect(sdn).to_contain("p50_us: 1000000")
expect(sdn).to_contain("p95_us: 2000000")
```

</details>

#### converts host measurements into normalized comparison samples

<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "sample=1 elapsed_s=1.00 max_rss_kb=100\nsample=2 elapsed_s=2.00 max_rss_kb=200\n"
val measurement = parse_usr_bin_time_measurements(
    "simple test representative comparison",
    "linux-x86_64",
    output,
    1000,
    1000,
    "render+readback"
)
val record = host_measurement_record(
    "cpu_simd", "cpu_simd", "Initialized",
    measurement,
    true,
    false,
    "host measurement"
)
val sample = host_comparison_sample(
    record,
    "wm_compare:cpu",
    "cpu_simd",
    "simple-web",
    1200,
    "sha256:cpu",
    "nonzero_pixels:16",
    "host-cpu"
)
expect(backend_comparison_initialized_valid(sample)).to_equal(true)
expect(sample.cold_start_us).to_equal(2000000)
expect(sample.warm_start_us).to_equal(1000000)
```

</details>

#### builds host-safe initialized OpenCL GPU samples with compiler and runtime proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_comparison_sample_fixture(
    "opencl",
    "text_blit",
    "wm_compare:opencl:fixture",
    "simple-web"
)
expect(backend_comparison_initialized_valid(sample)).to_equal(true)
expect(sample.generated_entry_symbol).to_equal("simple_2d_copy_u32")
expect(sample.generated_binary_format).to_equal("spirv")
expect(sample.runtime_compute_target).to_equal("opencl")
expect(sample.runtime_launch_api).to_equal("clEnqueueNDRangeKernel")
expect(sample.runtime_status).to_equal("ready")
expect(sample.scalar_baseline_compared).to_equal(true)
expect(sample.fallback_used).to_equal(false)

var missing_runtime = sample
missing_runtime.runtime_status = "opencl-runtime-or-queue-unavailable"
expect(backend_comparison_sample_valid(missing_runtime)).to_equal(false)

var missing_timing = sample
missing_timing.artifact_submit_us = 0
expect(backend_comparison_sample_valid(missing_timing)).to_equal(false)
```

</details>

#### converts measured initialized CUDA GPU evidence without fixture timings

<details>
<summary>Executable SPipe</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_comparison_sample_from_measurement(
    InitializedGpuRuntimeMeasurement(
    backend: "cuda",
    operation_family: "alpha_blend",
    fixture_id: "wm_compare:cuda:measured",
    shell: "simple-web",
    command: "simple wm_compare measured cuda",
    host: "linux-x86_64",
    warmup_count: 2,
    sample_count: 7,
    p50_frame_us: 410,
    p95_frame_us: 640,
    max_rss_kb: 72000,
    binary_size_bytes: 2100000,
    baseline_binary_size_bytes: 2050000,
    render_readback_scope: "render+readback",
    cold_start_us: 52000,
    warm_start_us: 7800,
    package_size_bytes: 2200000,
    p95_input_to_paint_us: 920,
    artifact_build_us: 880,
    artifact_load_us: 90,
    artifact_submit_us: 37,
    artifact_sync_us: 19,
    artifact_readback_us: 81,
    checksum: "sha256:cuda:measured",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "cuda:0",
    width: 64,
    height: 64,
    runtime_ready: true,
    module_ready: true,
    args_ptr: 4096
    )
)
expect(backend_comparison_initialized_valid(sample)).to_equal(true)
expect(sample.warmup_count).to_equal(2)
expect(sample.sample_count).to_equal(7)
expect(sample.p50_frame_us).to_equal(410)
expect(sample.p95_frame_us).to_equal(640)
expect(sample.artifact_submit_us).to_equal(37)
expect(sample.artifact_readback_us).to_equal(81)
expect(sample.generated_operation).to_equal("alpha_blend")
expect(sample.runtime_compute_target).to_equal("cuda")
expect(sample.runtime_launch_api).to_equal("rt_cuda_launch_kernel")
expect(sample.runtime_status).to_equal("ready")
```

</details>

#### rejects measured initialized GPU evidence when runtime gate is not ready

<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_comparison_sample_from_measurement(
    InitializedGpuRuntimeMeasurement(
    backend: "opencl",
    operation_family: "text_blit",
    fixture_id: "wm_compare:opencl:not-ready",
    shell: "simple-web",
    command: "simple wm_compare measured opencl",
    host: "linux-x86_64",
    warmup_count: 1,
    sample_count: 5,
    p50_frame_us: 500,
    p95_frame_us: 750,
    max_rss_kb: 71000,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    render_readback_scope: "render+readback",
    cold_start_us: 51000,
    warm_start_us: 8200,
    package_size_bytes: 2150000,
    p95_input_to_paint_us: 900,
    artifact_build_us: 700,
    artifact_load_us: 80,
    artifact_submit_us: 44,
    artifact_sync_us: 18,
    artifact_readback_us: 77,
    checksum: "sha256:opencl:not-ready",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "opencl:0",
    width: 64,
    height: 64,
    runtime_ready: true,
    module_ready: false,
    args_ptr: 4096
    )
)
expect(sample.runtime_status).to_equal("module-not-loaded")
expect(backend_comparison_sample_valid(sample)).to_equal(false)
```

</details>

#### exports measured initialized OpenCL GPU evidence as normalized SDN

<details>
<summary>Executable SPipe</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = initialized_gpu_measurement_export_sdn(
    InitializedGpuRuntimeMeasurement(
    backend: "opencl",
    operation_family: "image_blit",
    fixture_id: "wm_compare:opencl:measured-export",
    shell: "simple-web",
    command: "simple wm_compare measured opencl",
    host: "linux-x86_64",
    warmup_count: 3,
    sample_count: 9,
    p50_frame_us: 430,
    p95_frame_us: 690,
    max_rss_kb: 73500,
    binary_size_bytes: 2110000,
    baseline_binary_size_bytes: 2060000,
    render_readback_scope: "render+readback",
    cold_start_us: 54000,
    warm_start_us: 8300,
    package_size_bytes: 2210000,
    p95_input_to_paint_us: 990,
    artifact_build_us: 910,
    artifact_load_us: 88,
    artifact_submit_us: 41,
    artifact_sync_us: 22,
    artifact_readback_us: 95,
    checksum: "sha256:opencl:measured-export",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "opencl:0",
    width: 64,
    height: 64,
    runtime_ready: true,
    module_ready: true,
    args_ptr: 4096
    )
)
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("sample_count: 1")
expect(sdn).to_contain("backend_family: \"opencl\"")
expect(sdn).to_contain("operation_family: \"image_blit\"")
expect(sdn).to_contain("generated_operation: \"copy\"")
expect(sdn).to_contain("runtime_launch_api: \"clEnqueueNDRangeKernel\"")
expect(sdn).to_contain("runtime_status: \"ready\"")
expect(sdn).to_contain("artifact_submit_us: 41")
expect(sdn).to_contain("artifact_readback_us: 95")
expect(sdn).to_contain("checksum: \"sha256:opencl:measured-export\"")
```

</details>

#### emits initialized runner samples only when backend probe and generated gate are ready

1. BackendProbeResult success
   - Expected: backend_comparison_initialized_valid(sample) is true
   - Expected: sample.status equals `Initialized`
   - Expected: sample.runtime_status equals `ready`
   - Expected: sample.artifact_submit_us equals `39`


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_runner_comparison_sample_from_probe(
    InitializedGpuRuntimeMeasurement(
    backend: "cuda",
    operation_family: "text_blit",
    fixture_id: "wm_compare:cuda:runner-ready",
    shell: "simple-web",
    command: "simple wm_compare runner cuda",
    host: "linux-x86_64",
    warmup_count: 2,
    sample_count: 6,
    p50_frame_us: 420,
    p95_frame_us: 650,
    max_rss_kb: 72000,
    binary_size_bytes: 2100000,
    baseline_binary_size_bytes: 2050000,
    render_readback_scope: "render+readback",
    cold_start_us: 53000,
    warm_start_us: 7900,
    package_size_bytes: 2200000,
    p95_input_to_paint_us: 930,
    artifact_build_us: 880,
    artifact_load_us: 90,
    artifact_submit_us: 39,
    artifact_sync_us: 20,
    artifact_readback_us: 83,
    checksum: "sha256:cuda:runner-ready",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "cuda:0",
    width: 64,
    height: 64,
    runtime_ready: true,
    module_ready: true,
    args_ptr: 4096
    ),
    BackendProbeResult.success("cuda", "test cuda initialized")
)
expect(backend_comparison_initialized_valid(sample)).to_equal(true)
expect(sample.status).to_equal("Initialized")
expect(sample.runtime_status).to_equal("ready")
expect(sample.artifact_submit_us).to_equal(39)
```

</details>

#### emits explicit unavailable runner samples when generated module gate is not ready

1. BackendProbeResult success
   - Expected: backend_comparison_sample_valid(sample) is true
   - Expected: sample.status equals `Failed`
   - Expected: sample.runtime_status equals `opencl-runtime-or-queue-unavailable`


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_runner_comparison_sample_from_probe(
    InitializedGpuRuntimeMeasurement(
    backend: "opencl",
    operation_family: "text_blit",
    fixture_id: "wm_compare:opencl:runner-not-ready",
    shell: "simple-web",
    command: "simple wm_compare runner opencl",
    host: "linux-x86_64",
    warmup_count: 2,
    sample_count: 6,
    p50_frame_us: 420,
    p95_frame_us: 650,
    max_rss_kb: 72000,
    binary_size_bytes: 2100000,
    baseline_binary_size_bytes: 2050000,
    render_readback_scope: "render+readback",
    cold_start_us: 53000,
    warm_start_us: 7900,
    package_size_bytes: 2200000,
    p95_input_to_paint_us: 930,
    artifact_build_us: 880,
    artifact_load_us: 90,
    artifact_submit_us: 39,
    artifact_sync_us: 20,
    artifact_readback_us: 83,
    checksum: "sha256:opencl:runner-not-ready",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "opencl:0",
    width: 64,
    height: 64,
    runtime_ready: true,
    module_ready: false,
    args_ptr: 4096
    ),
    BackendProbeResult.success("opencl", "test opencl initialized")
)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
expect(sample.status).to_equal("Failed")
expect(sample.unavailable_reason).to_contain("generated Engine2D module not loaded")
expect(sample.runtime_status).to_equal("opencl-runtime-or-queue-unavailable")
```

</details>

#### exports unavailable ROCm runner samples when strict probe cannot initialize

<details>
<summary>Executable SPipe</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = initialized_gpu_runner_export_sdn(
    InitializedGpuRuntimeMeasurement(
    backend: "rocm",
    operation_family: "text_blit",
    fixture_id: "wm_compare:rocm:runner-probe",
    shell: "simple-web",
    command: "simple wm_compare runner rocm",
    host: "linux-x86_64",
    warmup_count: 1,
    sample_count: 5,
    p50_frame_us: 500,
    p95_frame_us: 700,
    max_rss_kb: 70000,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    render_readback_scope: "render+readback",
    cold_start_us: 51000,
    warm_start_us: 8200,
    package_size_bytes: 2150000,
    p95_input_to_paint_us: 900,
    artifact_build_us: 700,
    artifact_load_us: 80,
    artifact_submit_us: 44,
    artifact_sync_us: 18,
    artifact_readback_us: 77,
    checksum: "sha256:rocm:runner-probe",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "rocm:0",
    width: 64,
    height: 64,
    runtime_ready: true,
    module_ready: true,
    args_ptr: 4096
    )
)
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("backend_family: \"rocm\"")
expect(sdn).to_contain("status: \"Unavailable\"")
expect(sdn).to_contain("ROCm/HIP probe unavailable in interpreter")
```

</details>

#### captures OpenCL device-buffer measurements or explicit unavailable evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = opencl_device_buffer_measurement_sample(
    OpenClDeviceMeasurementOptions(
    fixture_id: "wm_compare:opencl:device-buffer",
    shell: "simple-web",
    command: "simple wm_compare opencl device-buffer",
    host: "linux-x86_64",
    width: 8,
    height: 8,
    color: 4278255360,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
expect(sample.backend_family).to_equal("opencl")
expect(sample.operation_family).to_equal("fill")
expect(sample.runtime_launch_api).to_equal("clEnqueueNDRangeKernel")
if sample.status == "Initialized":
    expect(sample.checksum).to_contain("sum32:")
    expect(sample.pixel_proof).to_contain("nonzero_pixels:")
    expect(sample.artifact_submit_us).to_be_greater_than(0)
    expect(sample.artifact_readback_us).to_be_greater_than(0)
    expect(sample.runtime_status).to_equal("ready")
else:
    expect(sample.unavailable_reason != "").to_equal(true)
```

</details>

#### exports OpenCL device-buffer measurement rows as normalized SDN

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = opencl_device_buffer_measurement_export_sdn(
    OpenClDeviceMeasurementOptions(
    fixture_id: "wm_compare:opencl:device-buffer-export",
    shell: "simple-web",
    command: "simple wm_compare opencl device-buffer",
    host: "linux-x86_64",
    width: 8,
    height: 8,
    color: 4278255360,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("sample_count: 1")
expect(sdn).to_contain("backend_family: \"opencl\"")
expect(sdn).to_contain("operation_family: \"fill\"")
expect(sdn).to_contain("runtime_launch_api: \"clEnqueueNDRangeKernel\"")
```

</details>

#### captures CUDA device-buffer measurements or explicit unavailable evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = cuda_device_buffer_measurement_sample(
    CudaDeviceMeasurementOptions(
    fixture_id: "wm_compare:cuda:device-buffer",
    shell: "simple-web",
    command: "simple wm_compare cuda device-buffer",
    host: "linux-x86_64",
    width: 8,
    height: 8,
    color: 4278255360,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
expect(sample.backend_family).to_equal("cuda")
expect(sample.operation_family).to_equal("fill")
expect(sample.runtime_launch_api).to_equal("rt_cuda_launch_kernel")
if sample.status == "Initialized":
    expect(sample.checksum).to_contain("sum32:")
    expect(sample.pixel_proof).to_contain("nonzero_pixels:")
    expect(sample.artifact_submit_us).to_be_greater_than(0)
    expect(sample.artifact_readback_us).to_be_greater_than(0)
    expect(sample.runtime_status).to_equal("ready")
else:
    expect(sample.unavailable_reason != "").to_equal(true)
```

</details>

#### exports CUDA device-buffer measurement rows as normalized SDN

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = cuda_device_buffer_measurement_export_sdn(
    CudaDeviceMeasurementOptions(
    fixture_id: "wm_compare:cuda:device-buffer-export",
    shell: "simple-web",
    command: "simple wm_compare cuda device-buffer",
    host: "linux-x86_64",
    width: 8,
    height: 8,
    color: 4278255360,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("sample_count: 1")
expect(sdn).to_contain("backend_family: \"cuda\"")
expect(sdn).to_contain("operation_family: \"fill\"")
expect(sdn).to_contain("runtime_launch_api: \"rt_cuda_launch_kernel\"")
```

</details>

#### captures ROCm HIP device-buffer runtime status as explicit evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = rocm_device_buffer_measurement_sample(
    RocmDeviceMeasurementOptions(
    fixture_id: "wm_compare:rocm:device-buffer",
    shell: "simple-web",
    command: "simple wm_compare rocm device-buffer",
    host: "linux-x86_64",
    width: 8,
    height: 8,
    color: 4278255360,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
expect(sample.backend_family).to_equal("rocm")
expect(sample.operation_family).to_equal("fill")
expect(sample.generated_binary_format).to_equal("hsaco")
expect(sample.runtime_launch_api).to_equal("rt_rocm_launch_kernel")
expect(sample.unavailable_reason == "missing-rocm-ffi").to_equal(false)
expect(sample.unavailable_reason).to_contain("rocm")
```

</details>

#### exports ROCm HIP device-buffer measurement rows as normalized SDN

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = rocm_device_buffer_measurement_export_sdn(
    RocmDeviceMeasurementOptions(
    fixture_id: "wm_compare:rocm:device-buffer-export",
    shell: "simple-web",
    command: "simple wm_compare rocm device-buffer",
    host: "linux-x86_64",
    width: 8,
    height: 8,
    color: 4278255360,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("sample_count: 1")
expect(sdn).to_contain("backend_family: \"rocm\"")
expect(sdn).to_contain("generated_binary_format: \"hsaco\"")
expect(sdn).to_contain("runtime_launch_api: \"rt_rocm_launch_kernel\"")
```

</details>

<details>
<summary>Advanced: measures Simple Web software render loops with non-zero frame samples and pixel proof</summary>

#### measures Simple Web software render loops with non-zero frame samples and pixel proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = software_render_loop_measurement_sample(
    SoftwareRenderLoopMeasurementOptions(
    backend: "software",
    operation_family: "text_blit",
    fixture_id: "wm_compare:software:render-loop",
    shell: "simple-web",
    command: "simple wm_compare software render loop",
    host: "linux-x86_64",
    width: 32,
    height: 24,
    warmup_count: 1,
    sample_count: 2,
    max_rss_kb: 70000,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
expect(sample.status).to_equal("Initialized")
expect(sample.sample_count).to_equal(2)
expect(sample.p50_frame_us).to_be_greater_than(0)
expect(sample.p95_frame_us).to_be_greater_than(0)
expect(sample.checksum).to_contain("sum32:")
expect(sample.pixel_proof).to_contain("nonzero_pixels:")
expect(sample.runtime_status).to_equal("cpu-render-loop-ready")
```

</details>


</details>

<details>
<summary>Advanced: exports Simple Web software render-loop rows as normalized SDN</summary>

#### exports Simple Web software render-loop rows as normalized SDN

<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = software_render_loop_measurement_export_sdn(
    SoftwareRenderLoopMeasurementOptions(
    backend: "software",
    operation_family: "text_blit",
    fixture_id: "wm_compare:software:render-loop-export",
    shell: "simple-web",
    command: "simple wm_compare software render loop",
    host: "linux-x86_64",
    width: 32,
    height: 24,
    warmup_count: 1,
    sample_count: 2,
    max_rss_kb: 70000,
    binary_size_bytes: 2000000,
    baseline_binary_size_bytes: 1950000,
    package_size_bytes: 2050000
    )
)
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("sample_count: 1")
expect(sdn).to_contain("backend_family: \"software\"")
expect(sdn).to_contain("p50_frame_us:")
expect(sdn).to_contain("checksum: \"sum32:")
expect(sdn).to_contain("runtime_status: \"cpu-render-loop-ready\"")
```

</details>


</details>

<details>
<summary>Advanced: builds a current-host backend matrix with explicit unavailable GPU lanes</summary>

#### builds a current-host backend matrix with explicit unavailable GPU lanes

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "sample=1 elapsed_s=37.71 max_rss_kb=929240\nsample=2 elapsed_s=38.58 max_rss_kb=930308\nsample=3 elapsed_s=38.89 max_rss_kb=930160\n"
val records = current_host_backend_measurement_matrix(
    "simple test backend_measurement_report_spec",
    "linux-x86_64",
    output,
    454623792,
    454623792,
    "backend-measurement-spec-startup"
)
expect(records.len()).to_equal(6)
expect(backend_measurement_matrix_valid(records)).to_equal(true)
val sdn = backend_measurement_matrix_sdn(records)
expect(sdn).to_contain("metal_status:")
expect(sdn).to_contain("vulkan_status:")
expect(sdn).to_contain("cuda_status:")
expect(sdn).to_contain("opencl_status:")
expect(sdn).to_contain("hip_status:")
expect(sdn).to_contain("cpu_simd_status: \"Initialized\"")
```

</details>


</details>

#### builds normalized current-host comparison samples for GPU and CPU lanes

<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "sample=1 elapsed_s=37.71 max_rss_kb=929240\nsample=2 elapsed_s=38.58 max_rss_kb=930308\nsample=3 elapsed_s=38.89 max_rss_kb=930160\n"
val samples = current_host_backend_comparison_samples(
    "simple test backend_measurement_report_spec",
    "linux-x86_64",
    output,
    454623792,
    454623792,
    455000000,
    "backend-measurement-spec-startup",
    "wm_compare:startup",
    "simple-web",
    "text_blit",
    "sha256:startup",
    "nonzero_pixels:256"
)
expect(samples.len()).to_equal(6)
expect(backend_comparison_samples_valid(samples)).to_equal(true)
val sdn = backend_comparison_samples_sdn(samples)
expect(sdn).to_contain("backend_family: \"metal\"")
expect(sdn).to_contain("backend_family: \"vulkan\"")
expect(sdn).to_contain("backend_family: \"cuda\"")
expect(sdn).to_contain("backend_family: \"opencl\"")
expect(sdn).to_contain("backend_family: \"hip\"")
expect(sdn).to_contain("backend_family: \"cpu_simd\"")
expect(sdn).to_contain("fixture_id: \"wm_compare:startup\"")
expect(sdn).to_contain("offload_tag_kind: \"@gpu\"")
expect(sdn).to_contain("operation_family: \"text_blit\"")
expect(sdn).to_contain("generated_entry_symbol: \"simple_2d_copy_u32\"")
expect(sdn).to_contain("generated_binary_format: \"spirv\"")
expect(sdn).to_contain("runtime_launch_api: \"clEnqueueNDRangeKernel\"")
expect(sdn).to_contain("runtime_status: \"opencl-runtime-or-queue-unavailable\"")
expect(sdn).to_contain("offload_tag_kind: \"baseline\"")
```

</details>

#### exports normalized startup size samples as SDN for audit reports

<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "sample=1 elapsed_s=0.004 max_rss_kb=1200\nsample=2 elapsed_s=0.006 max_rss_kb=1400\n"
val sdn = backend_measurement_export_sdn(
    "build/startup_size_perf_audit/simple_tui_standalone",
    "linux-x86_64",
    output,
    14336,
    14472,
    14336,
    "startup-size-audit",
    "startup-size:simple_tui_standalone",
    "simple-tui",
    "text_blit",
    "sha256:startup-size",
    "startup-size-only"
)
expect(sdn).to_contain("backend_comparison_samples")
expect(sdn).to_contain("sample_count: 6")
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("backend_family: \"opencl\"")
expect(sdn).to_contain("backend_family: \"cpu_simd\"")
expect(sdn).to_contain("fixture_id: \"startup-size:simple_tui_standalone\"")
expect(sdn).to_contain("binary_size_bytes: 14336")
expect(sdn).to_contain("baseline_binary_size_bytes: 14472")
expect(sdn).to_contain("package_size_bytes: 14336")
expect(sdn).to_contain("max_rss_kb: 1400")
expect(sdn).to_contain("generated_source_format: \"opencl-c\"")
expect(sdn).to_contain("generated_artifact_path_suffix: \"simple_2d_optimization.spirv\"")
expect(sdn).to_contain("runtime_compute_target: \"opencl\"")
```

</details>

<details>
<summary>Advanced: exports measured Simple software render-loop rows with non-zero frame evidence</summary>

#### exports measured Simple software render-loop rows with non-zero frame evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = software_render_loop_export_sdn([
    "--measure-software-render-loop", "true",
    "--software-render-backend", "software",
    "--width", "8",
    "--height", "8",
    "--warmup-count", "0",
    "--sample-count", "1",
    "--fixture", "wm_compare:software-render-loop",
    "--shell", "simple-web",
    "--command", "software-render-loop-spec",
    "--host", "linux-x86_64"
])
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("backend_family: \"software\"")
expect(sdn).to_contain("render_readback_scope: \"software-render-loop\"")
expect(sdn).to_contain("checksum: \"sum32:")
expect(sdn).to_contain("pixel_proof: \"nonzero_pixels:")
expect(sdn).to_contain("sample_count: 1")
```

</details>


</details>

<details>
<summary>Advanced: exports measured Simple software render-loop rows through the narrow software entrypoint</summary>

#### exports measured Simple software render-loop rows through the narrow software entrypoint

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = software_only_render_loop_export_sdn([
    "--software-render-backend", "software",
    "--width", "8",
    "--height", "8",
    "--warmup-count", "0",
    "--sample-count", "1",
    "--fixture", "wm_compare:software-only-render-loop",
    "--shell", "simple-web",
    "--command", "software-only-render-loop-spec",
    "--host", "linux-x86_64"
])
expect(sdn).to_contain("valid: true")
expect(sdn).to_contain("backend_family: \"software\"")
expect(sdn).to_contain("render_readback_scope: \"software-render-loop\"")
expect(sdn).to_contain("checksum: \"sum32:")
expect(sdn).to_contain("pixel_proof: \"nonzero_pixels:")
expect(sdn).to_contain("sample_count: 1")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/backend_measurement_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare backend measurement capture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
