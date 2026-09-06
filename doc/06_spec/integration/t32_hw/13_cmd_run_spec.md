# 13 Cmd Run Specification

> Tests covering T32 command run.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 13 Cmd Run Specification

## Scenarios

### T32 command run

#### valid commands

#### runs SYStem.Up

- runs SYStem.Up


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs SYStem.Up")
val result = t32_hw_run_cmd(client, "SYStem.Up")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("SYStem.Up failed: {e}").to_equal("")
```

</details>

#### runs VERSION.ENvironment

- runs VERSION.ENvironment


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs VERSION.ENvironment")
val result = t32_hw_run_cmd(client, "VERSION.ENvironment")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("VERSION.ENvironment failed: {e}").to_equal("")
```

</details>

#### error handling

#### empty command returns error

- empty command returns error
   - Expected: v.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("empty command returns error")
val result = t32_hw_run_cmd(client, "")
match result:
    Ok(v):
        # Empty command may return Ok with empty output
        expect(v.len()).to_equal(0)
    Err(_):
        # Or it may return an error -- both acceptable
        expect("error accepted").to_contain("accepted")
```

</details>

#### invalid command returns error

- invalid command returns error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("invalid command returns error")
val result = t32_hw_run_cmd(client, "NONEXISTENT.COMMAND.12345")
match result:
    Err(_): expect("error accepted").to_contain("accepted")
    Ok(_):
        # Some T32 versions silently accept bad commands
        expect("accepted ok").to_contain("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/13_cmd_run_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 command run.
- T32 command run

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

- Canonical SPipe generation for source `3b38ce12fa32a15670040507d1a90a52c555b104826c3a824456982c556b9069`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b38ce12fa32a15670040507d1a90a52c555b104826c3a824456982c556b9069`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b38ce12fa32a15670040507d1a90a52c555b104826c3a824456982c556b9069`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/t32_hw/13_cmd_run_spec.spl
mirror: doc/06_spec/integration/t32_hw/13_cmd_run_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/13_cmd_run_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/13_cmd_run_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/13_cmd_run_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/t32_hw/13_cmd_run_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs SYStem.Up' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/13_cmd_run_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs VERSION.ENvironment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/13_cmd_run_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty command returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
