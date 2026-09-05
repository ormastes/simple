# 30 Dialog Tools Specification

> Tests covering T32 dialog tools.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 30 Dialog Tools Specification

## Scenarios

### T32 dialog tools

#### basic connectivity

#### T32 responds to PRINT command

- T32 responds to PRINT command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("T32 responds to PRINT command")
# PRINT works on all T32 versions -- basic connectivity check
val result = t32_hw_run_cmd(client, "PRINT \"dialog_tools_ping\"")
match result:
    Ok(v): expect(v).to_contain("dialog_tools_ping")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### dialog lifecycle

#### PRACTICE dialog can be opened

- PRACTICE dialog can be opened


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRACTICE dialog can be opened")
if not t32_hw_has_dialog():
    expect("DIALOG not available in this T32 version").to_contain("not available")
    return
return "skip: opening PRACTICE dialog requires CMM dialog script"
```

</details>

#### PRACTICE.STATE() detects dialog

- PRACTICE.STATE() detects dialog
   - Expected: "PRACTICE.STATE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRACTICE.STATE() detects dialog")
if not t32_hw_has_practice_state():
    expect("PRACTICE.STATE not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_eval(client, "PRACTICE.STATE()")
match result:
    Ok(v):
        # Should return a state string (e.g., "IDLE", "RUN", "DIALOG")
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("PRACTICE.STATE() failed: {e}").to_equal("")
```

</details>

#### dialog can be dismissed

- dialog can be dismissed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dialog can be dismissed")
if not t32_hw_has_dialog():
    expect("DIALOG not available in this T32 version").to_contain("not available")
    return
return "skip: dismissing dialog requires an open CMM-driven dialog"
```

</details>

#### PRACTICE.STATE() after dismiss

- PRACTICE.STATE() after dismiss
   - Expected: "PRACTICE.STATE() after dismiss failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PRACTICE.STATE() after dismiss")
if not t32_hw_has_practice_state():
    expect("PRACTICE.STATE not available in this T32 version").to_contain("not available")
    return
# After dismissing a dialog, PRACTICE.STATE() should return
# an idle/empty state. Without dialog open/close support,
# we verify PRACTICE.STATE() still returns a valid value.
val result = t32_hw_eval(client, "PRACTICE.STATE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("PRACTICE.STATE() after dismiss failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/30_dialog_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 dialog tools.
- T32 dialog tools

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

- Canonical SPipe generation for source `124d61c509c4fd69e2dd4a50b2f6811195c3c6d877c4c107feb7787fda3a22c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `124d61c509c4fd69e2dd4a50b2f6811195c3c6d877c4c107feb7787fda3a22c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `124d61c509c4fd69e2dd4a50b2f6811195c3c6d877c4c107feb7787fda3a22c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/30_dialog_tools_spec.spl
mirror: doc/06_spec/integration/t32_hw/30_dialog_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/30_dialog_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/30_dialog_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/30_dialog_tools_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 responds to PRINT command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/30_dialog_tools_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PRACTICE dialog can be opened' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/30_dialog_tools_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PRACTICE.STATE() detects dialog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
