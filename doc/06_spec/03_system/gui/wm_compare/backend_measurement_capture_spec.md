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
| 5 | 5 | 0 | 0 |

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

Runnable source: 24 lines folded for reproduction.
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
```

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
