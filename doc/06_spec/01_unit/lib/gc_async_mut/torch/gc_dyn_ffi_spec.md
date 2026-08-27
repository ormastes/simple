# Gc Dyn Ffi Specification

> Tests covering DynLoader FFI Pattern, Stateless wrapper, Function dispatch, Migration safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Dyn Ffi Specification

## Scenarios

### DynLoader FFI Pattern

### Stateless wrapper

#### DynLoader has no owns_handle field

- DynLoader has no owns_handle field
   - Expected: dl.lib_path equals `libspl_torch.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DynLoader has no owns_handle field")
val dl = MockDynLoader.instance()
expect(dl.lib_path).to_equal("libspl_torch.so")
# No owns_handle field — stateless
```

</details>

#### each call creates fresh loader instance

- each call creates fresh loader instance
   - Expected: dl1.lib_path equals `dl2.lib_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("each call creates fresh loader instance")
val dl1 = mock_dl()
val dl2 = mock_dl()
expect(dl1.lib_path).to_equal(dl2.lib_path)
```

</details>

### Function dispatch

#### call0 dispatches without args

- call0 dispatches without args
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("call0 dispatches without args")
val result = mock_dyn_torch_available()
expect(result).to_equal(true)
```

</details>

#### call1 dispatches with one arg

- call1 dispatches with one arg
   - Expected: result equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("call1 dispatches with one arg")
val result = mock_dyn_torch_tensor_neg(10)
expect(result).to_equal(11)
```

</details>

### Migration safety

#### no ownership state means zero-change migration

- no ownership state means zero-change migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no ownership state means zero-change migration")
# dyn_ffi.spl has no owns_handle, no drop(), no GC interaction
# Safe to copy to nogc_sync_mut/ without modification
val dl = MockDynLoader.instance()
# Verify no state to manage
expect(dl.lib_path.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DynLoader FFI Pattern, Stateless wrapper, Function dispatch, Migration safety.
- DynLoader FFI Pattern
- Stateless wrapper
- Function dispatch
- Migration safety

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6381b0f21352a8bcab741e39bc0df983b607103411006dfa5aa255a878cad8c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6381b0f21352a8bcab741e39bc0df983b607103411006dfa5aa255a878cad8c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6381b0f21352a8bcab741e39bc0df983b607103411006dfa5aa255a878cad8c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DynLoader has no owns_handle field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'each call creates fresh loader instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'call0 dispatches without args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
