# Cuda Fill U32 Validation Specification

> Tests covering CUDA ProcessingIR pre-device validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Fill U32 Validation Specification

## Scenarios

### CUDA ProcessingIR pre-device validation

#### should reject invalid IR with zero device provenance

- should reject invalid IR with zero device provenance
   - Expected: zero.reason equals `invalid-element-count`

Zero-sized, overflowing, and unsupported requests fail before any CUDA driver
operation. Every failure has its exact validation reason, empty output, and
zero backend handle/device identity.

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject invalid IR with zero device provenance")
val zero = processing_ir_execute_cuda(processing_ir_fill_u32(0, 7u32))
expect(zero.reason).to_equal("invalid-element-count")
_expect_rejected(zero, "invalid-element-count")
_expect_rejected(processing_ir_execute_cuda(processing_ir_fill_u32(536870912, 7u32)), "output-size-overflow")
_expect_rejected(processing_ir_execute_cuda(ProcessingIr(op: 99, element_count: 1, value: 7u32)), "unsupported-op")
```

</details>

#### should reject work after executor shutdown without touching CUDA

- should reject work after executor shutdown without touching CUDA


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject work after executor shutdown without touching CUDA")
var executor = ProcessingCudaExecutor.create()
executor.shutdown()
_expect_rejected(
    processing_ir_execute_cuda_with_executor(
        executor, processing_ir_fill_u32(8, 7u32)),
    "cuda-executor-closed")
```

</details>

#### should reject drawing IR until a native CUDA drawing executor exists

- should reject drawing IR until a native CUDA drawing executor exists
   - Expected: artifact.valid is false
   - Expected: artifact.reason equals `cuda-unsupported-processing-op`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject drawing IR until a native CUDA drawing executor exists")
val rect = processing_ir_fill_rect_u32(8, 8, 8, 1, 1, 4, 4, 7u32)
val artifact = processing_cuda_artifact(rect)
expect(artifact.valid).to_equal(false)
expect(artifact.reason).to_equal("cuda-unsupported-processing-op")
_expect_rejected(processing_ir_execute_cuda(rect), "cuda-unsupported-processing-op")
```

</details>

#### should generate a deterministic shared-contract PTX artifact

- should generate a deterministic shared-contract PTX artifact
- Exercise success branches
   - Expected: artifact.target equals `ProcessingBackendTarget.CudaPtx`
   - Expected: artifact.format equals `ptx`
   - Expected: artifact.entry_point equals `processing_fill_u32`
   - Expected: artifact.source equals `repeated.source`
   - Expected: artifact.semantic_key equals `repeated.semantic_key`
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should generate a deterministic shared-contract PTX artifact")
step("Exercise success branches")
val ir = processing_ir_fill_u32(64, 0x01020304u32)
val artifact = processing_cuda_artifact(ir)
val repeated = processing_cuda_artifact(ir)
expect(artifact.target).to_equal(ProcessingBackendTarget.CudaPtx)
expect(artifact.format).to_equal("ptx")
expect(artifact.entry_point).to_equal("processing_fill_u32")
expect(artifact.source).to_equal(repeated.source)
expect(artifact.semantic_key).to_equal(repeated.semantic_key)
expect(artifact.source).to_contain(".visible .entry processing_fill_u32")
expect(artifact.source).to_contain("st.global.u32")
expect(artifact.valid).to_equal(true)
expect(artifact.reason).to_equal("ok")
```

</details>

#### should preserve the one-element CUDA dispatch boundary in its artifact

- should preserve the one-element CUDA dispatch boundary in its artifact
- Exercise boundary branches
   - Expected: artifact.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve the one-element CUDA dispatch boundary in its artifact")
step("Exercise boundary branches")
val ir = processing_ir_fill_u32(1, 0xFFFFFFFFu32)
val artifact = processing_cuda_artifact(ir)
expect(artifact.valid).to_equal(true)
expect(artifact.semantic_key).to_contain("count=1")
expect(artifact.source).to_contain("setp.ge.u32")
```

</details>

#### should fail compile evidence closed without a named successful compiler

- should fail compile evidence closed without a named successful compiler
- Exercise rejection branches
   - Expected: failed.artifact_valid is true
   - Expected: failed.compiler_succeeded is false
   - Expected: failed.validator_succeeded is false
   - Expected: failed.reason equals `cuda-compiler-failed`
   - Expected: unnamed.compiler_succeeded is false
   - Expected: unnamed.reason equals `cuda-compiler-identity-missing`
   - Expected: accepted.artifact_valid is true
   - Expected: accepted.compiler_succeeded is true
   - Expected: accepted.validator_succeeded is true
   - Expected: accepted.validator_identity equals `cuda-driver-module-load`
   - Expected: accepted.reason equals `ok`
   - Expected: invalid.artifact_valid is false
   - Expected: invalid.reason equals `invalid-element-count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should fail compile evidence closed without a named successful compiler")
step("Exercise rejection branches")
val ir = processing_ir_fill_u32(64, 7u32)
val failed = processing_cuda_compile_evidence(ir, false, "nvcc 13.0")
expect(failed.artifact_valid).to_equal(true)
expect(failed.compiler_succeeded).to_equal(false)
expect(failed.validator_succeeded).to_equal(false)
expect(failed.reason).to_equal("cuda-compiler-failed")
val unnamed = processing_cuda_compile_evidence(ir, true, "")
expect(unnamed.compiler_succeeded).to_equal(false)
expect(unnamed.reason).to_equal("cuda-compiler-identity-missing")
val accepted = processing_cuda_compile_evidence(ir, true, "CUDA driver 580.126.16")
expect(accepted.artifact_valid).to_equal(true)
expect(accepted.compiler_succeeded).to_equal(true)
expect(accepted.validator_succeeded).to_equal(true)
expect(accepted.validator_identity).to_equal("cuda-driver-module-load")
expect(accepted.reason).to_equal("ok")
val invalid = processing_cuda_compile_evidence(processing_ir_fill_u32(0, 7u32), true, "CUDA driver")
expect(invalid.artifact_valid).to_equal(false)
expect(invalid.reason).to_equal("invalid-element-count")
```

</details>

#### should accept only device-origin exact CUDA readback evidence

- should accept only device-origin exact CUDA readback evidence
- Measure branch coverage
   - Expected: exact.submitted is true
   - Expected: exact.device_origin is true
   - Expected: exact.oracle_match is true
   - Expected: exact.reason equals `ok`
   - Expected: mirror.device_origin is false
   - Expected: mirror.oracle_match is true
   - Expected: mirror.values.len() equals `0`
   - Expected: mirror.reason equals `cuda-device-provenance-missing`
   - Expected: mismatch.oracle_match is false
   - Expected: mismatch.values.len() equals `0`
   - Expected: mismatch.reason equals `cuda-oracle-mismatch`
   - Expected: incomplete.submitted is false
   - Expected: incomplete.device_origin is false
   - Expected: incomplete.oracle_match is false
   - Expected: incomplete.reason equals `cuda-dispatch-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should accept only device-origin exact CUDA readback evidence")
step("Measure branch coverage")
val ir = processing_ir_fill_u32(2, 9u32)
val exact = processing_cuda_readback_evidence(
    ir, ProcessingCudaResult(completed: true, reason: "ok", values: [9u32, 9u32], backend_handle: 2, device_identity: 3))
expect(exact.submitted).to_equal(true)
expect(exact.device_origin).to_equal(true)
expect(exact.oracle_match).to_equal(true)
expect(exact.reason).to_equal("ok")
val mirror = processing_cuda_readback_evidence(
    ir, ProcessingCudaResult(completed: true, reason: "ok", values: [9u32, 9u32], backend_handle: 0, device_identity: 0))
expect(mirror.device_origin).to_equal(false)
expect(mirror.oracle_match).to_equal(true)
expect(mirror.values.len()).to_equal(0)
expect(mirror.reason).to_equal("cuda-device-provenance-missing")
val mismatch = processing_cuda_readback_evidence(
    ir, ProcessingCudaResult(completed: true, reason: "ok", values: [9u32, 8u32], backend_handle: 2, device_identity: 3))
expect(mismatch.oracle_match).to_equal(false)
expect(mismatch.values.len()).to_equal(0)
expect(mismatch.reason).to_equal("cuda-oracle-mismatch")
val incomplete = processing_cuda_readback_evidence(
    ir, ProcessingCudaResult(completed: false, reason: "cuda-dispatch-failed", values: [], backend_handle: 0, device_identity: 0))
expect(incomplete.submitted).to_equal(false)
expect(incomplete.device_origin).to_equal(false)
expect(incomplete.oracle_match).to_equal(false)
expect(incomplete.reason).to_equal("cuda-dispatch-failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CUDA ProcessingIR pre-device validation.
- CUDA ProcessingIR pre-device validation

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
- `REQ-003`
- `REQ-006`
- `REQ-007`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4dee4c53f1f480c3c0e1d8240d070bd7577172036a363343881f15f7f47d1b3c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4dee4c53f1f480c3c0e1d8240d070bd7577172036a363343881f15f7f47d1b3c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4dee4c53f1f480c3c0e1d8240d070bd7577172036a363343881f15f7f47d1b3c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=70 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid IR with zero device provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject invalid IR with zero device provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject work after executor shutdown without touching CUDA' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject work after executor shutdown without touching CUDA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject drawing IR until a native CUDA drawing executor exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject drawing IR until a native CUDA drawing executor exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate a deterministic shared-contract PTX artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the one-element CUDA dispatch boundary in its artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail compile evidence closed without a named successful compiler' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
