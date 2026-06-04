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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Measurement Report Specification

## Scenarios

### wm_compare backend measurement evidence

#### accepts initialized accelerated lanes with timings, RSS, size, and scalar baseline

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
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
expect(sdn).to_contain("checksum: \"sha256:1234\"")
expect(sdn).to_contain("pixel_proof: \"nonzero_pixels:4096\"")
```

</details>

#### rejects initialized comparison samples without pixel proof or fallback reason

1. var missing proof =  initialized sample
   - Expected: backend_comparison_sample_valid(missing_proof) is false

2. var missing reason =  initialized sample
   - Expected: backend_comparison_sample_valid(missing_reason) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var missing_proof = _initialized_sample()
missing_proof.pixel_proof = ""
expect(backend_comparison_sample_valid(missing_proof)).to_equal(false)

var missing_reason = _initialized_sample()
missing_reason.fallback_used = true
missing_reason.fallback_reason = ""
expect(backend_comparison_sample_valid(missing_reason)).to_equal(false)
```

</details>

#### rejects initialized accelerated lane evidence without scalar baseline comparison

<details>
<summary>Executable SPipe</summary>

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

#### accepts unavailable backend lanes only with explicit reason

<details>
<summary>Executable SPipe</summary>

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

1. StrictBackendFactory strict
   - Expected: backend_comparison_unavailable_valid(sample) is true
   - Expected: backend_comparison_sample_valid(sample) is true


<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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

<details>
<summary>Advanced: requires Metal Vulkan CUDA OpenCL HIP and CPU SIMD lanes in the matrix</summary>

#### requires Metal Vulkan CUDA OpenCL HIP and CPU SIMD lanes in the matrix

1. StrictBackendFactory strict

2. StrictBackendFactory strict

3. StrictBackendFactory strict

4. StrictBackendFactory strict

5. StrictBackendFactory strict
   - Expected: backend_measurement_matrix_valid(records) is true


<details>
<summary>Executable SPipe</summary>

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare backend measurement evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
