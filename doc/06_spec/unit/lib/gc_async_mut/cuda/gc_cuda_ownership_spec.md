# Gc Cuda Ownership Specification

> Tests covering GC CUDA Ownership, CudaStreamWrapper, CudaEventWrapper, CudaDeviceMemWrapper, Ownership transfer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Cuda Ownership Specification

## Scenarios

### GC CUDA Ownership

### CudaStreamWrapper

#### owned stream frees on drop

- owned stream frees on drop
   - Expected: s.should_free() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owned stream frees on drop")
val s = owned_stream(42)
expect(s.should_free()).to_equal(true)
```

</details>

#### borrowed stream does not free

- borrowed stream does not free
   - Expected: s.should_free() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("borrowed stream does not free")
val s = borrowed_stream(42)
expect(s.should_free()).to_equal(false)
```

</details>

### CudaEventWrapper

#### owned event frees on drop

- owned event frees on drop
   - Expected: e.should_free() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owned event frees on drop")
val e = owned_event(99)
expect(e.should_free()).to_equal(true)
```

</details>

### CudaDeviceMemWrapper

#### owned memory frees on drop

- owned memory frees on drop
   - Expected: m.should_free() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owned memory frees on drop")
val m = owned_mem(100)
expect(m.should_free()).to_equal(true)
```

</details>

### Ownership transfer

#### only owner frees shared handle

- only owner frees shared handle
   - Expected: borrower.should_free() is false
   - Expected: owner.should_free() is true
   - Expected: owner.handle equals `borrower.handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only owner frees shared handle")
val owner = owned_stream(77)
val borrower = borrowed_stream(77)
# Borrower should not free
expect(borrower.should_free()).to_equal(false)
# Owner should free
expect(owner.should_free()).to_equal(true)
# Same handle
expect(owner.handle).to_equal(borrower.handle)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GC CUDA Ownership, CudaStreamWrapper, CudaEventWrapper, CudaDeviceMemWrapper, Ownership transfer.
- GC CUDA Ownership
- CudaStreamWrapper
- CudaEventWrapper
- CudaDeviceMemWrapper
- Ownership transfer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4b0072952f23fb8309a870f03385cb20301683d2af6294c5818bdfc016d245da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b0072952f23fb8309a870f03385cb20301683d2af6294c5818bdfc016d245da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b0072952f23fb8309a870f03385cb20301683d2af6294c5818bdfc016d245da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owned stream frees on drop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'borrowed stream does not free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owned event frees on drop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
