# 29 Job Manager Specification

> Tests covering T32 job manager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 29 Job Manager Specification

## Scenarios

### T32 job manager

#### synchronous eval

#### eval completes synchronously

- eval completes synchronously
   - Expected: "eval 1+1 failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval completes synchronously")
val result = t32_hw_eval(client, "1+1")
match result:
    Ok(v):
        # Should return a value immediately
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval 1+1 failed: {e}").to_equal("")
```

</details>

#### long eval completes

- long eval completes
   - Expected: "VERSION.BUILD() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("long eval completes")
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.BUILD() failed: {e}").to_equal("")
```

</details>

#### sequential evals

#### multiple evals in sequence

- multiple evals in sequence
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multiple evals in sequence")
val r1 = t32_hw_eval(client, "1+1")
val r2 = t32_hw_eval(client, "2+2")
val r3 = t32_hw_eval(client, "3+3")
val ok1 = match r1:
    Ok(_): true
    Err(_): false
val ok2 = match r2:
    Ok(_): true
    Err(_): false
val ok3 = match r3:
    Ok(_): true
    Err(_): false
val all_ok = ok1 and ok2 and ok3
expect(all_ok).to_equal(true)
```

</details>

#### error recovery

#### eval after error recovers

- eval after error recovers
   - Expected: "recovery eval failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval after error recovers")
# Send a bad expression first
val bad = t32_hw_eval(client, "ZZZNOTEXPR.ZZZZ()")
# bad may be Ok or Err depending on T32 behavior
# Now send a good expression and verify it works
val good = t32_hw_eval(client, "VERSION.BUILD()")
match good:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("recovery eval failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/29_job_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 job manager.
- T32 job manager

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f4f2767559c83dc671fe85e6b433ca8b14bc291c7571967d465c31fcbdf5b1a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f4f2767559c83dc671fe85e6b433ca8b14bc291c7571967d465c31fcbdf5b1a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f4f2767559c83dc671fe85e6b433ca8b14bc291c7571967d465c31fcbdf5b1a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/29_job_manager_spec.spl
mirror: doc/06_spec/integration/t32_hw/29_job_manager_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/29_job_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/29_job_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/29_job_manager_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eval completes synchronously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/29_job_manager_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'long eval completes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/29_job_manager_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple evals in sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
