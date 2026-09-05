# Gpu Driver Status Code Sign Specification

> Tests covering gpu_driver CUDA status sign.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Driver Status Code Sign Specification

## Scenarios

### gpu_driver CUDA status sign

#### treats CUDA_SUCCESS (0) as success

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats CUDA_SUCCESS (0) as success


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats CUDA_SUCCESS (0) as success")
# Control: passes both before and after the fix. Proves the predicate is
# not simply reporting failure for everything.
assert_true(is_ok(gpu_status(0)))
```

</details>

#### treats a POSITIVE CUresult as failure

- treats a POSITIVE CUresult as failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a POSITIVE CUresult as failure")
# The regression. `< 0` accepted all three of these as success.
assert_false(is_ok(gpu_status(1)))
assert_false(is_ok(gpu_status(2)))
assert_false(is_ok(gpu_status(3)))
```

</details>

#### treats a NEGATED CUresult as failure

- treats a NEGATED CUresult as failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a NEGATED CUresult as failure")
# Control: passes both before and after the fix. The hooks that return
# the status pre-negated must keep working.
assert_false(is_ok(gpu_status(-1)))
assert_false(is_ok(gpu_status(-3)))
```

</details>

#### preserves the reported status code in the error

- preserves the reported status code in the error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the reported status code in the error")
match gpu_status(3):
    case Ok(_):
        assert_equal("no error for CUDA_ERROR_NOT_INITIALIZED", "an error")
    case Err(e):
        assert_equal(e.code, 3)
```

</details>

#### still succeeds on the null-pointer short circuit (control)

- still succeeds on the null-pointer short circuit (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still succeeds on the null-pointer short circuit (control)")
# Control: gpu_free short-circuits before any driver call, so this is Ok
# in both directions and shows the suite is not uniformly red.
val nullp = GpuPtr(device_ptr: 0, size: 0, is_valid: false)
assert_true(is_ok(gpu_free(nullp)))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gpu_driver CUDA status sign.
- gpu_driver CUDA status sign

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

- Canonical SPipe generation for source `80992002246b0a0f3599cb7375150d1e5a84c9d1dd9b38312eaa9b05703b133a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80992002246b0a0f3599cb7375150d1e5a84c9d1dd9b38312eaa9b05703b133a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80992002246b0a0f3599cb7375150d1e5a84c9d1dd9b38312eaa9b05703b133a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats CUDA_SUCCESS (0) as success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a POSITIVE CUresult as failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu_driver_status_code_sign_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a NEGATED CUresult as failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
