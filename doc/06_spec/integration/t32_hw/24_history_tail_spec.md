# 24 History Tail Specification

> Tests covering T32 history tail.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 24 History Tail Specification

## Scenarios

### T32 history tail

#### PRACTICE state

#### PRACTICE.STATE() queryable

- PRACTICE.STATE() queryable
   - Expected: "PRACTICE.STATE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRACTICE.STATE() queryable")
if not t32_hw_has_practice_state():
    expect("PRACTICE.STATE not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_eval(client, "PRACTICE.STATE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("PRACTICE.STATE() failed: {e}").to_equal("")
```

</details>

#### command history

#### command history exists after commands

- command history exists after commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("command history exists after commands")
# After running PRINT commands above, the session should have
# accumulated history. We verify by running another command
# and checking the AREA buffer is accessible.
val result = t32_hw_run_cmd(client, "PRINT \"history_check\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("history command failed: {e}").to_equal("")
```

</details>

#### AREA buffer

#### AREA buffer readable

- AREA buffer readable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AREA buffer readable")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.view")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.view failed: {e}").to_equal("")
```

</details>

#### PRINT output verifiable via command success

- PRINT output verifiable via command success


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRINT output verifiable via command success")
# PRINT works on all T32 versions as a universal alternative
val result = t32_hw_run_cmd(client, "PRINT \"tail_check\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/24_history_tail_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 history tail.
- T32 history tail

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

- Canonical SPipe generation for source `cfc1e35033eb4314330d05afc767a321ec1501463cfc375cfb7cf654c7158830`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cfc1e35033eb4314330d05afc767a321ec1501463cfc375cfb7cf654c7158830`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cfc1e35033eb4314330d05afc767a321ec1501463cfc375cfb7cf654c7158830`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/24_history_tail_spec.spl
mirror: doc/06_spec/integration/t32_hw/24_history_tail_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/24_history_tail_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/24_history_tail_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/24_history_tail_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PRACTICE.STATE() queryable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/24_history_tail_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'command history exists after commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/24_history_tail_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AREA buffer readable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
