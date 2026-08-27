# 22 Action List Invoke Specification

> Tests covering T32 action list invoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 22 Action List Invoke Specification

## Scenarios

### T32 action list invoke

#### execution control

#### Go starts target

- Go starts target


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Go starts target")
val go_result = t32_hw_run_cmd(client, "Go")
match go_result:
    Ok(_): expect("go ok").to_contain("ok")
    Err(e): expect("Go failed: {e}").to_equal("")
val state = t32_hw_eval(client, "STATE.RUN()")
match state:
    Ok(v): expect(v).to_contain("TRUE")
    Err(e): expect("STATE.RUN() failed: {e}").to_equal("")
```

</details>

#### Break stops target

- Break stops target


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Break stops target")
t32_hw_run_cmd(client, "Go")
val brk_result = t32_hw_run_cmd(client, "Break")
match brk_result:
    Ok(_): expect("break ok").to_contain("ok")
    Err(e): expect("Break failed: {e}").to_equal("")
val state = t32_hw_eval(client, "STATE.RUN()")
match state:
    Ok(v): expect(v).to_contain("FALSE")
    Err(e): expect("STATE.RUN() failed: {e}").to_equal("")
```

</details>

#### Step executes one instruction

- Step executes one instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Step executes one instruction")
# Ensure target is stopped first
t32_hw_run_cmd(client, "Break")
val result = t32_hw_run_cmd(client, "Step")
match result:
    Ok(_):
        val state = t32_hw_eval(client, "STATE.RUN()")
        match state:
            Ok(v): expect(v).to_contain("FALSE")
            Err(e): expect("STATE.RUN() after Step failed: {e}").to_equal("")
    Err(e): expect("Step failed: {e}").to_equal("")
```

</details>

#### Step.Over executes

- Step.Over executes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Step.Over executes")
t32_hw_run_cmd(client, "Break")
val result = t32_hw_run_cmd(client, "Step.Over")
match result:
    Ok(_):
        val state = t32_hw_eval(client, "STATE.RUN()")
        match state:
            Ok(v): expect(v).to_contain("FALSE")
            Err(e): expect("STATE.RUN() after Step.Over failed: {e}").to_equal("")
    Err(e): expect("Step.Over failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/22_action_list_invoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 action list invoke.
- T32 action list invoke

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

- Canonical SPipe generation for source `eb70127163466c9e04474ebfe4d007eeab46d46292643f24b92c047896c51c13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb70127163466c9e04474ebfe4d007eeab46d46292643f24b92c047896c51c13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb70127163466c9e04474ebfe4d007eeab46d46292643f24b92c047896c51c13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/22_action_list_invoke_spec.spl
mirror: doc/06_spec/integration/t32_hw/22_action_list_invoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/22_action_list_invoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/22_action_list_invoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/22_action_list_invoke_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Go starts target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/22_action_list_invoke_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Break stops target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/22_action_list_invoke_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Step executes one instruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
