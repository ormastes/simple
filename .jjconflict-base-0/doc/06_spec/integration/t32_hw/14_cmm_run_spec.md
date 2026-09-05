# 14 Cmm Run Specification

> Tests covering T32 CMM run.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 14 Cmm Run Specification

## Scenarios

### T32 CMM run

#### inline PRACTICE

#### runs inline PRACTICE

- runs inline PRACTICE


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs inline PRACTICE")
val result = t32_hw_run_cmd(client, "PRINT \"hello\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### AREA.Create succeeds

- AREA.Create succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AREA.Create succeeds")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.Create T32_HW_TEST")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Create failed: {e}").to_equal("")
```

</details>

#### AREA.Select succeeds

- AREA.Select succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AREA.Select succeeds")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.Select T32_HW_TEST")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Select failed: {e}").to_equal("")
```

</details>

#### runs multiple PRINT commands

- runs multiple PRINT commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs multiple PRINT commands")
# PRINT works on all T32 versions including old 2013 builds
val r1 = t32_hw_run_cmd(client, "PRINT \"test_line_1\"")
val r2 = t32_hw_run_cmd(client, "PRINT \"test_line_2\"")
match r1:
    Ok(_): expect("print1 ok").to_contain("ok")
    Err(e): expect("PRINT 1 failed: {e}").to_equal("")
match r2:
    Ok(_): expect("print2 ok").to_contain("ok")
    Err(e): expect("PRINT 2 failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/14_cmm_run_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 CMM run.
- T32 CMM run

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

- Canonical SPipe generation for source `cf776f0578fb9554d2593a042fd98dbf80024332e8379d2e989ced0c431799b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf776f0578fb9554d2593a042fd98dbf80024332e8379d2e989ced0c431799b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf776f0578fb9554d2593a042fd98dbf80024332e8379d2e989ced0c431799b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/14_cmm_run_spec.spl
mirror: doc/06_spec/integration/t32_hw/14_cmm_run_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/14_cmm_run_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/14_cmm_run_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/14_cmm_run_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs inline PRACTICE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/14_cmm_run_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AREA.Create succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/14_cmm_run_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AREA.Select succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
