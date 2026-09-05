# 28 Setup Headless Specification

> Tests covering T32 setup headless.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 28 Setup Headless Specification

## Scenarios

### T32 setup headless

#### headless operations

#### SYStem.Up in headless mode

- SYStem.Up in headless mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYStem.Up in headless mode")
val result = t32_hw_run_cmd(client, "SYStem.Up")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("SYStem.Up failed: {e}").to_equal("")
```

</details>

#### AREA operations work headless

- AREA operations work headless


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AREA operations work headless")
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val create = t32_hw_run_cmd(client, "AREA.Create T32_HEADLESS")
match create:
    Ok(_): expect("create ok").to_contain("ok")
    Err(e): expect("AREA.Create failed: {e}").to_equal("")
val select = t32_hw_run_cmd(client, "AREA.Select T32_HEADLESS")
match select:
    Ok(_): expect("select ok").to_contain("ok")
    Err(e): expect("AREA.Select failed: {e}").to_equal("")
val print_result = t32_hw_run_cmd(client, "PRINT \"headless_test\"")
match print_result:
    Ok(_): expect("print ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
val view = t32_hw_run_cmd(client, "AREA.view")
match view:
    Ok(_): expect("view ok").to_contain("ok")
    Err(e): expect("AREA.view failed: {e}").to_equal("")
```

</details>

#### PRINT works headless on all versions

- PRINT works headless on all versions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRINT works headless on all versions")
# PRINT is available in all T32 versions
val result = t32_hw_run_cmd(client, "PRINT \"headless_universal\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### eval works in headless

- eval works in headless
   - Expected: "VERSION.BUILD() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval works in headless")
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.BUILD() failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/28_setup_headless_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 setup headless.
- T32 setup headless

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

- Canonical SPipe generation for source `ea72218f3683a2903d2153a67fc087909dcda546a332e297103cddcead1d4d72`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea72218f3683a2903d2153a67fc087909dcda546a332e297103cddcead1d4d72`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea72218f3683a2903d2153a67fc087909dcda546a332e297103cddcead1d4d72`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/28_setup_headless_spec.spl
mirror: doc/06_spec/integration/t32_hw/28_setup_headless_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/28_setup_headless_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/28_setup_headless_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/28_setup_headless_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYStem.Up in headless mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/28_setup_headless_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AREA operations work headless' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/28_setup_headless_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PRINT works headless on all versions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
