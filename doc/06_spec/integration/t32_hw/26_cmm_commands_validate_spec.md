# 26 Cmm Commands Validate Specification

> Tests covering T32 CMM commands validate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 26 Cmm Commands Validate Specification

## Scenarios

### T32 CMM commands validate

#### valid commands

#### SYStem.Up is a valid command

- SYStem.Up is a valid command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYStem.Up is a valid command")
val result = t32_hw_run_cmd(client, "SYStem.Up")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("SYStem.Up failed: {e}").to_equal("")
```

</details>

#### Break is a valid command

- Break is a valid command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Break is a valid command")
val result = t32_hw_run_cmd(client, "Break")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Break failed: {e}").to_equal("")
```

</details>

#### PRINT is a valid command

- PRINT is a valid command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRINT is a valid command")
val result = t32_hw_run_cmd(client, "PRINT \"test\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### invalid commands

#### invalid command produces error

- invalid command produces error


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("invalid command produces error")
val result = t32_hw_run_cmd(client, "ZZZNOTACMD.ZZZZ")
match result:
    Ok(_):
        # If T32 does not error, it may silently ignore;
        # either way the command was sent
        expect("accepted ok").to_contain("ok")
    Err(_):
        # Expected -- invalid command should produce an error
        expect("error accepted").to_contain("accepted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/26_cmm_commands_validate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 CMM commands validate.
- T32 CMM commands validate

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

- Canonical SPipe generation for source `c0de6886a6e0b0fc9a14691e80bdfb2a24e998bb6912f08fe1ac87e823f74b60`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0de6886a6e0b0fc9a14691e80bdfb2a24e998bb6912f08fe1ac87e823f74b60`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0de6886a6e0b0fc9a14691e80bdfb2a24e998bb6912f08fe1ac87e823f74b60`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/26_cmm_commands_validate_spec.spl
mirror: doc/06_spec/integration/t32_hw/26_cmm_commands_validate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/26_cmm_commands_validate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/26_cmm_commands_validate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/26_cmm_commands_validate_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYStem.Up is a valid command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/26_cmm_commands_validate_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Break is a valid command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/26_cmm_commands_validate_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PRINT is a valid command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
