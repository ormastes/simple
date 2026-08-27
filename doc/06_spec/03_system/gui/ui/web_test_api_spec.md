# Web Test Api Specification

> Tests covering Web UI Test API portable smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Test Api Specification

## Scenarios

### Web UI Test API portable smoke

#### records ready and state endpoints

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records ready and state endpoints
   - Expected: "/api/test/ready" equals `/api/test/ready`
   - Expected: "NORMAL" equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records ready and state endpoints")
expect("/api/test/ready").to_equal("/api/test/ready")
expect("NORMAL").to_equal("NORMAL")
```

</details>

#### records element query contract

- records element query contract
   - Expected: "action_btn" equals `action_btn`
   - Expected: "button" equals `button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records element query contract")
expect("action_btn").to_equal("action_btn")
expect("button").to_equal("button")
```

</details>

#### records supported actions

- records supported actions
   - Expected: actions.len() equals `3`
   - Expected: actions[0] equals `click`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records supported actions")
val actions = ["click", "type", "key"]
expect(actions.len()).to_equal(3)
expect(actions[0]).to_equal("click")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/web_test_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Web UI Test API portable smoke.
- Web UI Test API portable smoke

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f75410333040a9ad01b75aeabf21f545fb92b3e0be6e7f63ae83961d8ef29226`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f75410333040a9ad01b75aeabf21f545fb92b3e0be6e7f63ae83961d8ef29226`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f75410333040a9ad01b75aeabf21f545fb92b3e0be6e7f63ae83961d8ef29226`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/gui/ui/web_test_api_spec.spl
mirror: doc/06_spec/03_system/gui/ui/web_test_api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/ui/web_test_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/ui/web_test_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/ui/web_test_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/ui/web_test_api_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records ready and state endpoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/web_test_api_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records element query contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/web_test_api_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records supported actions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
