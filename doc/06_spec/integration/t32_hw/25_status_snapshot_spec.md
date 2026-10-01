# 25 Status Snapshot Specification

> Tests covering T32 status snapshot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 25 Status Snapshot Specification

## Scenarios

### T32 status snapshot

#### individual status fields

#### STATE.RUN() returns boolean

- STATE.RUN() returns boolean
   - Expected: valid is true
   - Expected: "STATE.RUN() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("STATE.RUN() returns boolean")
val result = t32_hw_eval(client, "STATE.RUN()")
match result:
    Ok(v):
        val valid = v.contains("TRUE") or v.contains("FALSE")
        expect(valid).to_equal(true)
    Err(e):
        expect("STATE.RUN() failed: {e}").to_equal("")
```

</details>

#### STATE.TARGET() returns target info

- STATE.TARGET() returns target info
   - Expected: "STATE.TARGET() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("STATE.TARGET() returns target info")
val result = t32_hw_eval(client, "STATE.TARGET()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("STATE.TARGET() failed: {e}").to_equal("")
```

</details>

#### DEBUGMODE() returns mode

- DEBUGMODE() returns mode
   - Expected: "DEBUGMODE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DEBUGMODE() returns mode")
val result = t32_hw_eval(client, "DEBUGMODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("DEBUGMODE() failed: {e}").to_equal("")
```

</details>

#### SYStem.MODE() returns system mode

- SYStem.MODE() returns system mode
   - Expected: "SYStem.MODE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SYStem.MODE() returns system mode")
val result = t32_hw_eval(client, "SYStem.MODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("SYStem.MODE() failed: {e}").to_equal("")
```

</details>

#### consistency

#### status fields are consistent

- status fields are consistent
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("status fields are consistent")
# Read multiple status fields and confirm they all succeed
val run_result = t32_hw_eval(client, "STATE.RUN()")
val target_result = t32_hw_eval(client, "STATE.TARGET()")
val mode_result = t32_hw_eval(client, "SYStem.MODE()")
val run_ok = match run_result:
    Ok(_): true
    Err(_): false
val target_ok = match target_result:
    Ok(_): true
    Err(_): false
val mode_ok = match mode_result:
    Ok(_): true
    Err(_): false
val all_ok = run_ok and target_ok and mode_ok
expect(all_ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/25_status_snapshot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 status snapshot.
- T32 status snapshot

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

- Canonical SPipe generation for source `6ee36ef46ad8440737afd2d924a3aa9e83c348338441fe607bc698332201bd27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ee36ef46ad8440737afd2d924a3aa9e83c348338441fe607bc698332201bd27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ee36ef46ad8440737afd2d924a3aa9e83c348338441fe607bc698332201bd27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/25_status_snapshot_spec.spl
mirror: doc/06_spec/integration/t32_hw/25_status_snapshot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/25_status_snapshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/25_status_snapshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/25_status_snapshot_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'STATE.RUN() returns boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/25_status_snapshot_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'STATE.TARGET() returns target info' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/25_status_snapshot_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DEBUGMODE() returns mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
