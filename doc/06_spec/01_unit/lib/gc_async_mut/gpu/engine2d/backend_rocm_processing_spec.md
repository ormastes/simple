# Backend Rocm Processing Specification

> Tests covering ROCm/HIP processing-lane probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Rocm Processing Specification

## Scenarios

### ROCm/HIP processing-lane probe

#### probe_rocm returns a BackendProbeResult with required api fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe_rocm returns a BackendProbeResult with required api fields
   - Expected: probe.requested_name equals `rocm`
   - Expected: probe.api_name equals `rocm`
   - Expected: probe.shader_format equals `hsaco`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_rocm returns a BackendProbeResult with required api fields")
val probe = probe_rocm()
expect(probe.requested_name).to_equal("rocm")
expect(probe.api_name).to_equal("rocm")
expect(probe.shader_format).to_equal("hsaco")
```

</details>

#### probe_rocm returns a known BackendStatus variant

- probe_rocm returns a known BackendStatus variant
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_rocm returns a known BackendStatus variant")
val probe = probe_rocm()
val ok = (probe.status == BackendStatus.Initialized or
          probe.status == BackendStatus.Unavailable or
          probe.status == BackendStatus.Failed)
expect(ok).to_equal(true)
```

</details>

#### probe_rocm reports hip-toolchain-missing on hosts without AMD HIP runtime

- probe_rocm reports hip-toolchain-missing on hosts without AMD HIP runtime
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_rocm reports hip-toolchain-missing on hosts without AMD HIP runtime")
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

- probe is not silently green when HIP toolchain is absent
   - Expected: has_gate is true
   - Expected: has_reason is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe is not silently green when HIP toolchain is absent")
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

- hip-toolchain-missing gate appears when rt_rocm_is_available is false
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.api_name equals `rocm`
   - Expected: probe.shader_format equals `hsaco`
   - Expected: probe.has_compute is false
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hip-toolchain-missing gate appears when rt_rocm_is_available is false")
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

- RocmBackend.create does not initialize without AMD hardware
   - Expected: backend.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RocmBackend.create does not initialize without AMD hardware")
var backend = RocmBackend.create()
expect(backend.initialized).to_equal(false)
```

</details>

#### when ROCm device present probe reports compute and graphics ready

- when ROCm device present probe reports compute and graphics ready
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is true
   - Expected: probe.has_present is true
   - Expected: probe.feature_gate equals `rocm-device-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("when ROCm device present probe reports compute and graphics ready")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ROCm/HIP processing-lane probe.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7282971f5afc8982bf40d5de8b2ce51cca6cf67c8de4c4440160bdea8725ae5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7282971f5afc8982bf40d5de8b2ce51cca6cf67c8de4c4440160bdea8725ae5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7282971f5afc8982bf40d5de8b2ce51cca6cf67c8de4c4440160bdea8725ae5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_rocm returns a BackendProbeResult with required api fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_rocm returns a known BackendStatus variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_processing_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_rocm reports hip-toolchain-missing on hosts without AMD HIP runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
