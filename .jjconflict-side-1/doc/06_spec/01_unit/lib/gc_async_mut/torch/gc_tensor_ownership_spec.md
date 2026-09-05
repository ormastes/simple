# Gc Tensor Ownership Specification

> Tests covering GC Tensor Ownership, Basic ownership, Sub/div workaround, Mark borrowed pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Tensor Ownership Specification

## Scenarios

### GC Tensor Ownership

### Basic ownership

#### owned tensor frees on drop

- owned tensor frees on drop
   - Expected: t.should_free() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("owned tensor frees on drop")
val t = create_tensor(10)
# Verify the tensor would free (owns_handle is true)
expect(t.should_free()).to_equal(true)
```

</details>

#### borrowed tensor does not free

- borrowed tensor does not free
   - Expected: t.should_free() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("borrowed tensor does not free")
val t = MockTensor(handle: 10, owns_handle: false)
# Verify the tensor would NOT free
expect(t.should_free()).to_equal(false)
```

</details>

### Sub/div workaround

#### sub workaround does not double-free

- sub workaround does not double-free
   - Expected: result.should_free() is true
   - Expected: result.handle equals `120`
   - Expected: original.should_free() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sub workaround does not double-free")
val original = create_tensor(20)
val result = original.sub_workaround()
# Result should own its handle
expect(result.should_free()).to_equal(true)
expect(result.handle).to_equal(120)
# Original still owns its handle
expect(original.should_free()).to_equal(true)
```

</details>

### Mark borrowed pattern

#### marking as borrowed prevents free

- marking as borrowed prevents free
   - Expected: borrowed.should_free() is false
   - Expected: t.should_free() is true
   - Expected: borrowed.handle equals `t.handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marking as borrowed prevents free")
val t = create_tensor(30)
val borrowed = t.mark_borrowed()
# Borrowed should not free
expect(borrowed.should_free()).to_equal(false)
# Original should still free
expect(t.should_free()).to_equal(true)
# Same handle
expect(borrowed.handle).to_equal(t.handle)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GC Tensor Ownership, Basic ownership, Sub/div workaround, Mark borrowed pattern.
- GC Tensor Ownership
- Basic ownership
- Sub/div workaround
- Mark borrowed pattern

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab8705e84e325b1b31ad1d1f8ad662cc50f7585549eeb4110e6d0b5c67aff0f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab8705e84e325b1b31ad1d1f8ad662cc50f7585549eeb4110e6d0b5c67aff0f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab8705e84e325b1b31ad1d1f8ad662cc50f7585549eeb4110e6d0b5c67aff0f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owned tensor frees on drop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'borrowed tensor does not free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch/gc_tensor_ownership_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sub workaround does not double-free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
