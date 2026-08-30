# Backend Cuda Processing Specification

> <details>

<!-- sdn-diagram:id=backend_cuda_processing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_cuda_processing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_cuda_processing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_cuda_processing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Cuda Processing Specification

## Scenarios

### CUDA processing-lane probe

#### probe_cuda_processing returns a BackendProbeResult with required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_processing()
expect(probe.requested_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
```

</details>

#### probe_cuda_processing returns a known BackendStatus variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_processing()
val ok = (probe.status == BackendStatus.Initialized or
          probe.status == BackendStatus.Unavailable or
          probe.status == BackendStatus.Failed)
expect(ok).to_equal(true)
```

</details>

#### probe_cuda_processing matches probe_cuda_2d output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = probe_cuda_processing()
val p2 = probe_cuda_2d()
expect(p1.requested_name).to_equal(p2.requested_name)
expect(p1.api_name).to_equal(p2.api_name)
expect(p1.feature_gate).to_equal(p2.feature_gate)
expect(p1.shader_format).to_equal(p2.shader_format)
```

</details>

#### reports cuda-device-unavailable feature gate when no NVIDIA device present

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_processing()
if probe.status == BackendStatus.Unavailable:
    val gate = probe.feature_gate
    val ok = (gate == "cuda-device-unavailable" or
              gate == "cuda_runtime" or
              gate == "cuda_init")
    expect(ok).to_equal(true)
```

</details>

#### when no device: feature_gate is cuda-device-unavailable not cuda_device (legacy)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_processing()
if probe.feature_gate == "cuda_device":
    # This should never trigger — "cuda_device" is the old gate value
    # that was replaced by "cuda-device-unavailable" in AC-1.
    # If this assertion runs, the rename was reverted.
    expect(probe.feature_gate).to_equal("cuda-device-unavailable")
```

</details>

#### probe is not silently green when CUDA device is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_processing()
if probe.status != BackendStatus.Initialized:
    # Must have a non-empty feature_gate so callers can identify the failure mode
    val has_gate = probe.feature_gate != ""
    expect(has_gate).to_equal(true)
    val has_reason = probe.reason != ""
    expect(has_reason).to_equal(true)
```

</details>

#### when CUDA device is present probe reports compute capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_processing()
if probe.status == BackendStatus.Initialized:
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(true)
    expect(probe.has_present).to_equal(true)
    expect(probe.feature_gate).to_equal("cuda_2d_render")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CUDA processing-lane probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
