# Gpu Status Code Sign Specification

> Tests covering gpu_ops CUDA status sign.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Status Code Sign Specification

## Scenarios

### gpu_ops CUDA status sign

#### treats CUDA_SUCCESS (0) as success

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats CUDA_SUCCESS (0) as success
   - Expected: is_ok(gpu_status(0)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats CUDA_SUCCESS (0) as success")
# Control: passes both before and after the fix. Proves the predicate is
# not simply reporting failure for everything.
expect(is_ok(gpu_status(0))).to_equal(true)
```

</details>

#### treats a POSITIVE CUresult as failure

- treats a POSITIVE CUresult as failure
   - Expected: is_ok(gpu_status(1)) is false
   - Expected: is_ok(gpu_status(2)) is false
   - Expected: is_ok(gpu_status(3)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats a POSITIVE CUresult as failure")
# The regression. `< 0` accepted all three of these as success.
expect(is_ok(gpu_status(1))).to_equal(false)
expect(is_ok(gpu_status(2))).to_equal(false)
expect(is_ok(gpu_status(3))).to_equal(false)
```

</details>

#### treats a NEGATED CUresult as failure

- treats a NEGATED CUresult as failure
   - Expected: is_ok(gpu_status(-1)) is false
   - Expected: is_ok(gpu_status(-3)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats a NEGATED CUresult as failure")
# Control: passes both before and after the fix. The other runtime hooks
# return the status pre-negated and must keep working.
expect(is_ok(gpu_status(-1))).to_equal(false)
expect(is_ok(gpu_status(-3))).to_equal(false)
```

</details>

#### preserves the reported status code in the error

- preserves the reported status code in the error
   - Expected: "no error raised for CUDA_ERROR_NOT_INITIALIZED" equals `an error`
   - Expected: e.code equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves the reported status code in the error")
match gpu_status(3):
    case Ok(_):
        expect("no error raised for CUDA_ERROR_NOT_INITIALIZED").to_equal("an error")
    case Err(e):
        expect(e.code).to_equal(3)
```

</details>

#### still succeeds on the null-pointer short circuit (control)

- still succeeds on the null-pointer short circuit (control)
   - Expected: is_ok(gpu_free(nullp)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still succeeds on the null-pointer short circuit (control)")
# Control: gpu_free short-circuits before any driver call, so this is Ok
# in both directions and shows the suite is not uniformly red.
val nullp = GpuPtr(device_ptr: 0, size: 0, is_valid: false)
expect(is_ok(gpu_free(nullp))).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gpu_ops CUDA status sign.
- gpu_ops CUDA status sign

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

- Canonical SPipe generation for source `e73b9495b399cb4d487fc0babbf5a240866f55079fe307713f5f15cffc56893b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e73b9495b399cb4d487fc0babbf5a240866f55079fe307713f5f15cffc56893b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e73b9495b399cb4d487fc0babbf5a240866f55079fe307713f5f15cffc56893b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats CUDA_SUCCESS (0) as success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a POSITIVE CUresult as failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu_status_code_sign_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a NEGATED CUresult as failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
