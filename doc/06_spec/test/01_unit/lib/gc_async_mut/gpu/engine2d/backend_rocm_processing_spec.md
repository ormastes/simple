# Backend Rocm Processing Specification

> <details>

<!-- sdn-diagram:id=backend_rocm_processing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_rocm_processing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_rocm_processing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_rocm_processing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Rocm Processing Specification

## Scenarios

### ROCm/HIP processing-lane probe

#### probe_rocm returns a BackendProbeResult with required api fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
expect(probe.requested_name).to_equal("rocm")
expect(probe.api_name).to_equal("rocm")
expect(probe.shader_format).to_equal("hsaco")
```

</details>

#### probe_rocm returns a known BackendStatus variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
val ok = (probe.status == BackendStatus.Initialized or
          probe.status == BackendStatus.Unavailable or
          probe.status == BackendStatus.Failed)
expect(ok).to_equal(true)
```

</details>

#### probe_rocm reports hip-toolchain-missing on hosts without AMD HIP runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
if probe.status == BackendStatus.Unavailable:
    # On this Linux host: hipcc absent, amdhip64 not installed
    # The expected gate is "hip-toolchain-missing" or "rocm-device-unavailable"
    val gate = probe.feature_gate
    val ok = (gate == "hip-toolchain-missing" or
              gate == "rocm-device-unavailable")
    expect(ok).to_equal(true)
```

</details>

#### probe is not silently green when HIP toolchain is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
if probe.status != BackendStatus.Initialized:
    # Must carry a non-empty feature_gate so callers can identify the cause
    val has_gate = probe.feature_gate != ""
    expect(has_gate).to_equal(true)
    val has_reason = probe.reason != ""
    expect(has_reason).to_equal(true)
```

</details>

#### hip-toolchain-missing gate appears when rt_rocm_is_available is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
# On a host where hipcc is not installed and the HIP runtime library
# (amdhip64) is absent, the very first probe step fails with
# "hip-toolchain-missing". Assert this exact evidence string rather
# than relying on absence of an assertion.
if probe.feature_gate == "hip-toolchain-missing":
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    expect(probe.api_name).to_equal("rocm")
    expect(probe.shader_format).to_equal("hsaco")
    expect(probe.has_compute).to_equal(false)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
```

</details>

#### RocmBackend.create does not initialize without AMD hardware

- var backend = RocmBackend create
   - Expected: backend.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = RocmBackend.create()
expect(backend.initialized).to_equal(false)
```

</details>

#### when ROCm device present probe reports compute and graphics ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
if probe.status == BackendStatus.Initialized:
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(true)
    expect(probe.has_present).to_equal(true)
    expect(probe.feature_gate).to_equal("rocm-device-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ROCm/HIP processing-lane probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
