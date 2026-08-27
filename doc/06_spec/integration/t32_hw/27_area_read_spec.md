# 27 Area Read Specification

> Tests covering T32 AREA read.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 27 Area Read Specification

## Scenarios

### T32 AREA read

#### AREA lifecycle

#### creates AREA buffer

- creates AREA buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates AREA buffer")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Create failed: {e}").to_equal("")
```

</details>

#### selects AREA buffer

- selects AREA buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("selects AREA buffer")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
val result = t32_hw_run_cmd(client, "AREA.Select T32_HW_AREA")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Select failed: {e}").to_equal("")
```

</details>

#### writes to AREA

- writes to AREA


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes to AREA")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
t32_hw_run_cmd(client, "AREA.Select T32_HW_AREA")
val result = t32_hw_run_cmd(client, "PRINT \"hw_test_output\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT to AREA failed: {e}").to_equal("")
```

</details>

#### AREA.view reads buffer

- AREA.view reads buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AREA.view reads buffer")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
t32_hw_run_cmd(client, "AREA.Select T32_HW_AREA")
t32_hw_run_cmd(client, "PRINT \"hw_test_output\"")
val result = t32_hw_run_cmd(client, "AREA.view")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.view failed: {e}").to_equal("")
```

</details>

#### universal output

#### PRINT works on all T32 versions

- PRINT works on all T32 versions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRINT works on all T32 versions")
# PRINT is available in all T32 versions as a fallback
val result = t32_hw_run_cmd(client, "PRINT \"area_fallback_test\"")
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
| Source | `test/integration/t32_hw/27_area_read_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 AREA read.
- T32 AREA read

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

- Canonical SPipe generation for source `e4fc799e0ac8339f104c862ee8b09867ac8d2d61874d9ba4c9f4c5cbbe99c1d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4fc799e0ac8339f104c862ee8b09867ac8d2d61874d9ba4c9f4c5cbbe99c1d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4fc799e0ac8339f104c862ee8b09867ac8d2d61874d9ba4c9f4c5cbbe99c1d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/27_area_read_spec.spl
mirror: doc/06_spec/integration/t32_hw/27_area_read_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/27_area_read_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/27_area_read_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/27_area_read_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates AREA buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/27_area_read_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects AREA buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/27_area_read_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes to AREA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
