# Backend Cuda Processing Specification

> Tests covering CUDA processing-lane probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Cuda Processing Specification

## Scenarios

### CUDA processing-lane probe

#### probe_cuda_processing returns a BackendProbeResult with required fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe_cuda_processing returns a BackendProbeResult with required fields
   - Expected: probe.requested_name equals `cuda`
   - Expected: probe.api_name equals `cuda`
   - Expected: probe.shader_format equals `ptx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_cuda_processing returns a BackendProbeResult with required fields")
val probe = probe_cuda_processing()
expect(probe.requested_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
```

</details>

#### probe_cuda_processing returns a known BackendStatus variant

- probe_cuda_processing returns a known BackendStatus variant
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_cuda_processing returns a known BackendStatus variant")
val probe = probe_cuda_processing()
val ok = (probe.status == BackendStatus.Initialized or
          probe.status == BackendStatus.Unavailable or
          probe.status == BackendStatus.Failed)
expect(ok).to_equal(true)
```

</details>

#### probe_cuda_processing matches probe_cuda_2d output

- probe_cuda_processing matches probe_cuda_2d output
   - Expected: p1.requested_name equals `p2.requested_name`
   - Expected: p1.api_name equals `p2.api_name`
   - Expected: p1.feature_gate equals `p2.feature_gate`
   - Expected: p1.shader_format equals `p2.shader_format`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_cuda_processing matches probe_cuda_2d output")
val p1 = probe_cuda_processing()
val p2 = probe_cuda_2d()
expect(p1.requested_name).to_equal(p2.requested_name)
expect(p1.api_name).to_equal(p2.api_name)
expect(p1.feature_gate).to_equal(p2.feature_gate)
expect(p1.shader_format).to_equal(p2.shader_format)
```

</details>

#### reports cuda-device-unavailable feature gate when no NVIDIA device present

- reports cuda-device-unavailable feature gate when no NVIDIA device present
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports cuda-device-unavailable feature gate when no NVIDIA device present")
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

- when no device: feature_gate is cuda-device-unavailable not cuda_device (legacy)
   - Expected: probe.feature_gate equals `cuda-device-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when no device: feature_gate is cuda-device-unavailable not cuda_device (legacy)")
val probe = probe_cuda_processing()
if probe.feature_gate == "cuda_device":
    # This should never trigger — "cuda_device" is the old gate value
    # that was replaced by "cuda-device-unavailable" in AC-1.
    # If this assertion runs, the rename was reverted.
    expect(probe.feature_gate).to_equal("cuda-device-unavailable")
```

</details>

#### probe is not silently green when CUDA device is absent

- probe is not silently green when CUDA device is absent
   - Expected: has_gate is true
   - Expected: has_reason is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe is not silently green when CUDA device is absent")
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

- when CUDA device is present probe reports compute capability
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is true
   - Expected: probe.has_present is true
   - Expected: probe.feature_gate equals `cuda_2d_render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when CUDA device is present probe reports compute capability")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CUDA processing-lane probe.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59487adbf784967dd0990f0c60a923bd0d5d18cbdfd378e248634b1b70b75490`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59487adbf784967dd0990f0c60a923bd0d5d18cbdfd378e248634b1b70b75490`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59487adbf784967dd0990f0c60a923bd0d5d18cbdfd378e248634b1b70b75490`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_cuda_processing returns a BackendProbeResult with required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_cuda_processing returns a known BackendStatus variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_cuda_processing matches probe_cuda_2d output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
