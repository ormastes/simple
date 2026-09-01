# 15 Eval Specification

> Tests covering T32 eval expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 15 Eval Specification

## Scenarios

### T32 eval expressions

#### valid expressions

#### eval VERSION.BUILD()

- eval VERSION.BUILD()
   - Expected: "VERSION.BUILD failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval VERSION.BUILD()")
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        # VERSION.BUILD returns a numeric string like "134567"
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.BUILD failed: {e}").to_equal("")
```

</details>

#### eval STATE.RUN()

- eval STATE.RUN()
   - Expected: "STATE.RUN failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval STATE.RUN()")
val result = t32_hw_eval(client, "STATE.RUN()")
match result:
    Ok(v):
        # Returns "TRUE" or "FALSE" -- non-empty means valid response
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("STATE.RUN failed: {e}").to_equal("")
```

</details>

#### eval DEBUGMODE()

- eval DEBUGMODE()
   - Expected: "DEBUGMODE failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval DEBUGMODE()")
val result = t32_hw_eval(client, "DEBUGMODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("DEBUGMODE failed: {e}").to_equal("")
```

</details>

#### eval Register(PC)

- eval Register(PC)
   - Expected: "Register(PC) failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval Register(PC)")
val result = t32_hw_eval(client, "Register(PC)")
match result:
    Ok(v):
        # PC register returns a hex value like "0x00008000"
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("Register(PC) failed: {e}").to_equal("")
```

</details>

#### invalid expressions

#### eval invalid expression

- eval invalid expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval invalid expression")
val result = t32_hw_eval(client, "NONEXISTENT.FUNC.12345()")
match result:
    Err(_): expect("error accepted").to_contain("accepted")
    Ok(_):
        # Some T32 versions may return empty on bad expr
        expect("accepted ok").to_contain("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/15_eval_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 eval expressions.
- T32 eval expressions

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07537989cf514a66eb760bc20e41fefd2e895ba5e6fa04e3be82ebd1cf1aee8d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07537989cf514a66eb760bc20e41fefd2e895ba5e6fa04e3be82ebd1cf1aee8d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07537989cf514a66eb760bc20e41fefd2e895ba5e6fa04e3be82ebd1cf1aee8d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/15_eval_spec.spl
mirror: doc/06_spec/integration/t32_hw/15_eval_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/15_eval_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/15_eval_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/15_eval_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eval VERSION.BUILD()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/15_eval_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eval STATE.RUN()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/15_eval_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eval DEBUGMODE()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
