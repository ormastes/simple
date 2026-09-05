# Ffi Cuda Out Param Marshalling Specification

> Tests covering CudaDynFfi out-parameter results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Cuda Out Param Marshalling Specification

## Scenarios

### CudaDynFfi out-parameter results

#### reports the same device count in dynamic mode as the marshalling static path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the same device count in dynamic mode as the marshalling static path
   - Expected: dyn_ffi != nil is true
   - Expected: dyn_ffi.device_count() equals `truth`
   - Expected: static_ffi.device_count() equals `truth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the same device count in dynamic mode as the marshalling static path")
# The static extern marshals cuDeviceGetCount's out pointer correctly.
# Dynamic mode must agree with it. Before the fix dynamic mode returned
# the CUresult (0 on success), so on any host with GPUs present the two
# disagreed, and on a host with none the wrong answer was invisible.
val truth = rt_cuda_device_count()

val dyn_ffi = CudaDynFfi.create(GpuFfiMode.Dynamic)
expect(dyn_ffi != nil).to_equal(true)
expect(dyn_ffi.device_count()).to_equal(truth)

val static_ffi = CudaDynFfi.create_static()
expect(static_ffi.device_count()).to_equal(truth)
```

</details>

#### never claims availability while reporting zero devices

- never claims availability while reporting zero devices
   - Expected: dyn_ffi.device_count() > 0 is true
   - Expected: static_ffi.device_count() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never claims availability while reporting zero devices")
# is_available() used to be `call0("cuInit") == 0`. cuInit takes a flags
# argument, so call0 left that register undefined; and even a clean
# CUDA_SUCCESS only means the driver loaded, not that a GPU exists.
# "Available but zero devices" is the incoherent state that let callers
# walk into a device-0 lookup on a machine with no GPU.
val dyn_ffi = CudaDynFfi.create(GpuFfiMode.Dynamic)
if dyn_ffi.is_available():
    expect(dyn_ffi.device_count() > 0).to_equal(true)

val static_ffi = CudaDynFfi.create_static()
if static_ffi.is_available():
    expect(static_ffi.device_count() > 0).to_equal(true)
```

</details>

#### agrees between modes on whether CUDA is available at all

- agrees between modes on whether CUDA is available at all
   - Expected: dyn_ffi.is_available() equals `static_ffi.is_available()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees between modes on whether CUDA is available at all")
val dyn_ffi = CudaDynFfi.create(GpuFfiMode.Dynamic)
val static_ffi = CudaDynFfi.create_static()
expect(dyn_ffi.is_available()).to_equal(static_ffi.is_available())
```

</details>

#### never returns a device count below zero in either mode

- never returns a device count below zero in either mode
   - Expected: CudaDynFfi.create_static().device_count() >= 0 is true
   - Expected: CudaDynFfi.create(GpuFfiMode.Dynamic).device_count() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never returns a device count below zero in either mode")
# A CUresult leaking through as a payload can be a negative error code.
# A count is a cardinality and can never be negative.
expect(CudaDynFfi.create_static().device_count() >= 0).to_equal(true)
expect(CudaDynFfi.create(GpuFfiMode.Dynamic).device_count() >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CudaDynFfi out-parameter results.
- CudaDynFfi out-parameter results

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `24d60325197faa46afce106eb33c53571909c354776fcc6d276f264c37941942`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24d60325197faa46afce106eb33c53571909c354776fcc6d276f264c37941942`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24d60325197faa46afce106eb33c53571909c354776fcc6d276f264c37941942`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the same device count in dynamic mode as the marshalling static path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never claims availability while reporting zero devices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees between modes on whether CUDA is available at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
