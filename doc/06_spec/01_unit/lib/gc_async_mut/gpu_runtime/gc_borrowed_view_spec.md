# Gc Borrowed View Specification

> Tests covering GC Borrowed View Pattern, Temporary wrapper access, Owned vs borrowed comparison, NoGC replacement pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Borrowed View Specification

## Scenarios

### GC Borrowed View Pattern

### Temporary wrapper access

#### borrowed view does not free handle

- borrowed view does not free handle
   - Expected: t.should_free() is false
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("borrowed view does not free handle")
val t = MockWrapper(handle: 42, owns_handle: false)
expect(t.should_free()).to_equal(false)
val result = mock_gpu_tensor_is_cuda(42)
expect(result).to_equal(true)
```

</details>

#### borrowed view returns correct value

- borrowed view returns correct value
   - Expected: numel equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("borrowed view returns correct value")
val numel = mock_gpu_tensor_numel(5)
expect(numel).to_equal(50)
```

</details>

### Owned vs borrowed comparison

#### owned wrapper frees, borrowed does not

- owned wrapper frees, borrowed does not
   - Expected: borrowed.should_free() is false
   - Expected: owned.should_free() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("owned wrapper frees, borrowed does not")
val owned = MockWrapper(handle: 10, owns_handle: true)
val borrowed = MockWrapper(handle: 10, owns_handle: false)
expect(borrowed.should_free()).to_equal(false)
expect(owned.should_free()).to_equal(true)
```

</details>

### NoGC replacement pattern

#### direct FFI call replaces borrowed view

- direct FFI call replaces borrowed view
   - Expected: is_cuda is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("direct FFI call replaces borrowed view")
# In NoGC: fn gpu_tensor_is_cuda(h: i64) -> bool:
#     rt_torch_torchtensor_is_cuda(h)
# No wrapper created, no ownership question
val handle = 42
val is_cuda = handle > 0
expect(is_cuda).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GC Borrowed View Pattern, Temporary wrapper access, Owned vs borrowed comparison, NoGC replacement pattern.
- GC Borrowed View Pattern
- Temporary wrapper access
- Owned vs borrowed comparison
- NoGC replacement pattern

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

- Canonical SPipe generation for source `45aacb2fc1686862e30a5c32bcacbedb8b8d5a4fa1b5a6c7cc554b9141005dd6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45aacb2fc1686862e30a5c32bcacbedb8b8d5a4fa1b5a6c7cc554b9141005dd6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45aacb2fc1686862e30a5c32bcacbedb8b8d5a4fa1b5a6c7cc554b9141005dd6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'borrowed view does not free handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'borrowed view returns correct value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owned wrapper frees, borrowed does not' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
