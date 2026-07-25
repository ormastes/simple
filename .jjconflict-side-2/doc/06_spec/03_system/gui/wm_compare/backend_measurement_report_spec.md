# Backend Measurement Report Specification

> <details>

<!-- sdn-diagram:id=backend_measurement_report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_measurement_report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_measurement_report_spec -> std
backend_measurement_report_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_measurement_report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Measurement Report Specification

## Scenarios

### wm_compare backend measurement evidence

#### accepts initialized accelerated lanes with timings, RSS, size, and scalar baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = _initialized_record("cpu_simd")
expect(backend_measurement_initialized_valid(record)).to_equal(true)
expect(backend_measurement_satisfies_lane(record)).to_equal(true)
```

</details>

#### records binary size delta for initialized measurement evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = _initialized_record("cpu_simd")
expect(backend_measurement_binary_size_delta_valid(record)).to_equal(true)
expect(backend_measurement_binary_size_delta_bytes(record)).to_equal(10000)
val sdn = backend_measurement_record_sdn(record)
expect(sdn).to_contain("binary_size_bytes: 1000000")
expect(sdn).to_contain("baseline_binary_size_bytes: 990000")
expect(sdn).to_contain("binary_size_delta_bytes: 10000")
```

</details>

#### normalizes initialized backend comparison samples for shared UI and GPU reports

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = _initialized_sample()
expect(backend_comparison_initialized_valid(sample)).to_equal(true)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
val sdn = backend_comparison_sample_sdn(sample)
expect(sdn).to_contain("fixture_id: \"wm_compare:button_grid:64\"")
expect(sdn).to_contain("backend_family: \"cuda\"")
expect(sdn).to_contain("shell: \"simple-web\"")
expect(sdn).to_contain("cold_start_us: 42000")
expect(sdn).to_contain("warm_start_us: 9000")
expect(sdn).to_contain("package_size_bytes: 1250000")
expect(sdn).to_contain("artifact_build_us: 310")
expect(sdn).to_contain("offload_tag_kind: \"@gpu\"")
expect(sdn).to_contain("operation_family: \"text_blit\"")
expect(sdn).to_contain("generated_entry_symbol: \"simple_2d_copy_u32\"")
expect(sdn).to_contain("generated_binary_format: \"ptx\"")
expect(sdn).to_contain("generated_artifact_path_suffix: \"simple_2d_optimization.ptx\"")
expect(sdn).to_contain("runtime_compute_target: \"cuda\"")
expect(sdn).to_contain("runtime_execution_path: \"generated_2d_kernel\"")
expect(sdn).to_contain("runtime_launch_api: \"cuda_launch_api\"")
expect(sdn).to_contain("runtime_status: \"ready\"")
expect(sdn).to_contain("checksum: \"sha256:1234\"")
expect(sdn).to_contain("pixel_proof: \"nonzero_pixels:4096\"")
expect(sdn).to_contain("artifact_total_us: 660")
expect(sdn).to_contain("offload_overhead_verdict: \"offload-overhead-contained\"")
expect(sdn).to_contain("speed_verdict: \"missing-scalar-baseline\"")
expect(sdn).to_contain("offload_efficiency_verdict: \"missing-scalar-baseline\"")
```

</details>

#### classifies measured backend speed against an explicit scalar baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = _initialized_sample()
expect(backend_comparison_speed_verdict(sample, 2000)).to_equal("backend-faster-than-scalar")
expect(backend_comparison_speed_verdict(sample, 1000)).to_equal("backend-equal-to-scalar")
expect(backend_comparison_speed_verdict(sample, 900)).to_equal("backend-slower-than-scalar")
expect(backend_comparison_speed_verdict(sample, 0)).to_equal("missing-scalar-baseline")
expect(backend_comparison_offload_efficiency_verdict(sample, 2000)).to_equal("offload-useful")
```

</details>

#### classifies communication overhead that dominates the measured frame

- var sample =  initialized sample
   - Expected: backend_comparison_artifact_total_us(sample) equals `1510`
   - Expected: backend_comparison_offload_overhead_verdict(sample) equals `offload-overhead-dominates`
   - Expected: backend_comparison_offload_efficiency_verdict(sample, 2000) equals `offload-faster-but-overhead-dominates`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sample = _initialized_sample()
sample.artifact_submit_us = 700
sample.artifact_readback_us = 400
expect(backend_comparison_artifact_total_us(sample)).to_equal(1510)
expect(backend_comparison_offload_overhead_verdict(sample)).to_equal("offload-overhead-dominates")
expect(backend_comparison_offload_efficiency_verdict(sample, 2000)).to_equal("offload-faster-but-overhead-dominates")
```

</details>

#### classifies slower offloads by communication overhead versus compute cost

- var transfer bound =  initialized sample
   - Expected: backend_comparison_offload_efficiency_verdict(transfer_bound, 2000) equals `offload-slower-communication-overhead`
- var compute bound =  initialized sample
   - Expected: backend_comparison_offload_efficiency_verdict(compute_bound, 2000) equals `offload-slower-compute-bound`
- var break even =  initialized sample
   - Expected: backend_comparison_offload_efficiency_verdict(break_even, 2000) equals `offload-break-even`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var transfer_bound = _initialized_sample()
transfer_bound.p50_frame_us = 2500
transfer_bound.p95_frame_us = 2600
transfer_bound.p95_input_to_paint_us = 2700
transfer_bound.artifact_submit_us = 2100
expect(backend_comparison_offload_efficiency_verdict(transfer_bound, 2000)).to_equal("offload-slower-communication-overhead")

var compute_bound = _initialized_sample()
compute_bound.p50_frame_us = 2500
compute_bound.p95_frame_us = 2600
compute_bound.p95_input_to_paint_us = 2700
expect(backend_comparison_offload_efficiency_verdict(compute_bound, 2000)).to_equal("offload-slower-compute-bound")

var break_even = _initialized_sample()
break_even.p50_frame_us = 2000
break_even.p95_frame_us = 2100
break_even.p95_input_to_paint_us = 2200
expect(backend_comparison_offload_efficiency_verdict(break_even, 2000)).to_equal("offload-break-even")
```

</details>

#### summarizes measured offload combinations against the scalar baseline

- var slower =  initialized sample
- var slower overhead =  initialized sample
- var overhead =  initialized sample
- var equal =  initialized sample
   - Expected: backend_comparison_scalar_p50_us(samples) equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = _software_sample(2000)
val fast = _initialized_sample()
var slower = _initialized_sample()
slower.fixture_id = "wm_compare:button_grid:64:slow"
slower.p50_frame_us = 2500
slower.p95_frame_us = 2600
slower.p95_input_to_paint_us = 2700
var slower_overhead = _initialized_sample()
slower_overhead.fixture_id = "wm_compare:button_grid:64:slow-overhead"
slower_overhead.p50_frame_us = 2500
slower_overhead.p95_frame_us = 2600
slower_overhead.p95_input_to_paint_us = 2700
slower_overhead.artifact_submit_us = 2100
var overhead = _initialized_sample()
overhead.fixture_id = "wm_compare:button_grid:64:overhead"
overhead.artifact_submit_us = 700
overhead.artifact_readback_us = 400
var equal = _initialized_sample()
equal.fixture_id = "wm_compare:button_grid:64:equal"
equal.p50_frame_us = 2000
equal.p95_frame_us = 2100
equal.p95_input_to_paint_us = 2200
val samples = [scalar, fast, slower, slower_overhead, overhead, equal]
expect(backend_comparison_scalar_p50_us(samples)).to_equal(2000)
val sdn = backend_comparison_samples_sdn(samples)
expect(sdn).to_contain("scalar_baseline_p50_us: 2000")
expect(sdn).to_contain("backend_faster_than_scalar_count: 2")
expect(sdn).to_contain("backend_equal_to_scalar_count: 1")
expect(sdn).to_contain("backend_slower_than_scalar_count: 2")
expect(sdn).to_contain("offload_overhead_contained_count: 3")
expect(sdn).to_contain("offload_overhead_dominates_count: 2")
expect(sdn).to_contain("offload_useful_count: 1")
expect(sdn).to_contain("offload_faster_but_overhead_dominates_count: 1")
expect(sdn).to_contain("offload_break_even_count: 1")
expect(sdn).to_contain("offload_slower_communication_overhead_count: 1")
expect(sdn).to_contain("offload_slower_compute_bound_count: 1")
expect(sdn).to_contain("offload_missing_scalar_baseline_count: 0")
expect(sdn).to_contain("offload_efficiency_verdict: \"offload-useful\"")
expect(sdn).to_contain("offload_efficiency_verdict: \"offload-slower-communication-overhead\"")
expect(sdn).to_contain("offload_efficiency_verdict: \"offload-slower-compute-bound\"")
```

</details>

#### rejects initialized comparison samples without pixel proof fallback reason compiler metadata or runtime provenance

- var missing proof =  initialized sample
   - Expected: backend_comparison_sample_valid(missing_proof) is false
- var missing reason =  initialized sample
   - Expected: backend_comparison_sample_valid(missing_reason) is false
- var missing metadata =  initialized sample
   - Expected: backend_comparison_sample_valid(missing_metadata) is false
- var missing runtime =  initialized sample
   - Expected: backend_comparison_sample_valid(missing_runtime) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var missing_proof = _initialized_sample()
missing_proof.pixel_proof = ""
expect(backend_comparison_sample_valid(missing_proof)).to_equal(false)

var missing_reason = _initialized_sample()
missing_reason.fallback_used = true
missing_reason.fallback_reason = ""
expect(backend_comparison_sample_valid(missing_reason)).to_equal(false)

var missing_metadata = _initialized_sample()
missing_metadata.generated_entry_symbol = ""
expect(backend_comparison_sample_valid(missing_metadata)).to_equal(false)

var missing_runtime = _initialized_sample()
missing_runtime.runtime_status = ""
expect(backend_comparison_sample_valid(missing_runtime)).to_equal(false)
```

</details>

#### rejects initialized accelerated lane evidence without scalar baseline comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = BackendProbeResult.success("cuda", "initialized for measurement")
val record = backend_measurement_from_probe(
    probe,
    "simple test representative comparison",
    "local-linux",
    1,
    5,
    1000,
    1200,
    64000,
    1000000,
    990000,
    "render+readback",
    false
)
expect(backend_measurement_initialized_valid(record)).to_equal(false)
expect(backend_measurement_satisfies_lane(record)).to_equal(false)
```

</details>

#### rejects initialized OpenCL lane evidence without scalar baseline comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = BackendProbeResult.success("opencl", "initialized for measurement")
val record = backend_measurement_from_probe(
    probe,
    "simple test representative comparison",
    "local-linux",
    1,
    5,
    1000,
    1200,
    64000,
    1000000,
    990000,
    "render+readback",
    false
)
expect(backend_measurement_initialized_valid(record)).to_equal(false)
expect(backend_measurement_satisfies_lane(record)).to_equal(false)
```

</details>

#### accepts unavailable backend lanes only with explicit reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = StrictBackendFactory.strict().create_backend("metal")
val record = backend_measurement_from_probe(
    probe, "", "local-linux", 0, 0, 0, 0, 0, 0, 0, "", false
)
expect(record.requested_backend).to_equal("metal")
expect(record.status).to_equal("Unavailable")
expect(backend_measurement_unavailable_valid(record)).to_equal(true)
expect(backend_measurement_satisfies_lane(record)).to_equal(true)
```

</details>

#### normalizes unavailable backend comparison samples with explicit reason

- StrictBackendFactory strict
   - Expected: backend_comparison_unavailable_valid(sample) is true
   - Expected: backend_comparison_sample_valid(sample) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = backend_measurement_from_probe(
    StrictBackendFactory.strict().create_backend("hip"),
    "simple test representative comparison",
    "local-linux",
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    "",
    false
)
val sample = backend_comparison_from_measurement(
    record,
    "wm_compare:button_grid:64",
    "hip",
    "tauri",
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    "",
    "",
    ""
)
expect(backend_comparison_unavailable_valid(sample)).to_equal(true)
expect(backend_comparison_sample_valid(sample)).to_equal(true)
val sdn = backend_comparison_sample_sdn(sample)
expect(sdn).to_contain("backend_family: \"hip\"")
expect(sdn).to_contain("unavailable_reason:")
```

</details>

#### rejects fallback evidence for an accelerated lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = BackendMeasurementRecord(
    requested_backend: "vulkan",
    selected_backend: "cpu",
    status: "Initialized",
    command: "simple test representative comparison",
    host: "local-linux",
    warmup_count: 1,
    sample_count: 5,
    p50_us: 1000,
    p95_us: 1200,
    max_rss_kb: 64000,
    binary_size_bytes: 1000000,
    baseline_binary_size_bytes: 990000,
    render_readback_scope: "render+readback",
    scalar_baseline_compared: true,
    fallback_used: true,
    unavailable_reason: "fallback to CPU"
)
expect(backend_measurement_satisfies_lane(record)).to_equal(false)
```

</details>

#### rejects fallback evidence for OpenCL like CUDA and Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = BackendMeasurementRecord(
    requested_backend: "opencl",
    selected_backend: "cpu",
    status: "Initialized",
    command: "simple test representative comparison",
    host: "local-linux",
    warmup_count: 1,
    sample_count: 5,
    p50_us: 1000,
    p95_us: 1200,
    max_rss_kb: 64000,
    binary_size_bytes: 1000000,
    baseline_binary_size_bytes: 990000,
    render_readback_scope: "render+readback",
    scalar_baseline_compared: true,
    fallback_used: true,
    unavailable_reason: "fallback to CPU"
)
expect(backend_measurement_satisfies_lane(record)).to_equal(false)
```

</details>

#### requires OpenCL initialized samples to carry GPU artifact timings

-  initialized record
   - Expected: backend_comparison_sample_valid(sample) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = backend_comparison_from_measurement(
    _initialized_record("opencl"),
    "wm_compare:button_grid:64",
    "opencl",
    "simple-web",
    42000,
    9000,
    1250000,
    1800,
    0,
    0,
    0,
    0,
    0,
    "sha256:opencl",
    "nonzero_pixels:4096",
    "opencl:0"
)
expect(backend_comparison_sample_valid(sample)).to_equal(false)
```

</details>

<details>
<summary>Advanced: requires Metal Vulkan CUDA OpenCL HIP and CPU SIMD lanes in the matrix</summary>

#### requires Metal Vulkan CUDA OpenCL HIP and CPU SIMD lanes in the matrix

- StrictBackendFactory strict
- StrictBackendFactory strict
- StrictBackendFactory strict
- StrictBackendFactory strict
- StrictBackendFactory strict
   - Expected: backend_measurement_matrix_valid(records) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metal = backend_measurement_from_probe(
    StrictBackendFactory.strict().create_backend("metal"),
    "", "local-linux", 0, 0, 0, 0, 0, 0, 0, "", false
)
val vulkan = backend_measurement_from_probe(
    StrictBackendFactory.strict().create_backend("vulkan"),
    "", "local-linux", 0, 0, 0, 0, 0, 0, 0, "", false
)
val cuda = backend_measurement_from_probe(
    StrictBackendFactory.strict().create_backend("cuda"),
    "", "local-linux", 0, 0, 0, 0, 0, 0, 0, "", false
)
val opencl = backend_measurement_from_probe(
    StrictBackendFactory.strict().create_backend("opencl"),
    "", "local-linux", 0, 0, 0, 0, 0, 0, 0, "", false
)
val rocm = backend_measurement_from_probe(
    StrictBackendFactory.strict().create_backend("rocm"),
    "", "local-linux", 0, 0, 0, 0, 0, 0, 0, "", false
)
val cpu_simd = _initialized_record("cpu_simd")
val records = [metal, vulkan, cuda, opencl, rocm, cpu_simd]
expect(backend_measurement_matrix_valid(records)).to_equal(true)
val sdn = backend_measurement_matrix_sdn(records)
expect(sdn).to_contain("metal_status:")
expect(sdn).to_contain("vulkan_status:")
expect(sdn).to_contain("cuda_status:")
expect(sdn).to_contain("opencl_status:")
expect(sdn).to_contain("hip_status:")
expect(sdn).to_contain("cpu_simd_status:")
expect(sdn).to_contain("p50_us:")
expect(sdn).to_contain("p95_us:")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/backend_measurement_report_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare backend measurement evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
