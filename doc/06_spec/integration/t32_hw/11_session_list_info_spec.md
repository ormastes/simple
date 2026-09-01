# 11 Session List Info Specification

> Tests covering T32 session list info.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 11 Session List Info Specification

## Scenarios

### T32 session list info

#### session responsiveness

#### session responds after open

- session responds after open


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("session responds after open")
val ping = t32_hw_run_cmd(client, "PING")
match ping:
    Ok(_): expect("ping ok").to_contain("ok")
    Err(e): expect("PING failed: {e}").to_equal("")
```

</details>

#### eval works on open session

- eval works on open session
   - Expected: "eval failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("eval works on open session")
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval failed: {e}").to_equal("")
```

</details>

#### can query system mode

- can query system mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can query system mode")
val result = t32_hw_eval(client, "SYStem.MODE()")
match result:
    Ok(_): expect("eval ok").to_contain("ok")
    Err(e): expect("SYStem.MODE failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/11_session_list_info_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 session list info.
- T32 session list info

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `4e799becab777ad8c3010d4b990b058fb993e053487c93545fccef5b4d2ddb6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e799becab777ad8c3010d4b990b058fb993e053487c93545fccef5b4d2ddb6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e799becab777ad8c3010d4b990b058fb993e053487c93545fccef5b4d2ddb6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/integration/t32_hw/11_session_list_info_spec.spl
mirror: doc/06_spec/integration/t32_hw/11_session_list_info_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/11_session_list_info_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/11_session_list_info_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/11_session_list_info_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session responds after open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/11_session_list_info_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eval works on open session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/11_session_list_info_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can query system mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/t32_hw/11_session_list_info_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can query system mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
