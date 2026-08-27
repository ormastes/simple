# Shared Ui Contract Specification

> Tests covering Shared UI contract portable smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Ui Contract Specification

## Scenarios

### Shared UI contract portable smoke

#### records protocol version

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records protocol version
   - Expected: protocol_version equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records protocol version")
val protocol_version = "1"
expect(protocol_version).to_equal("1")
```

</details>

#### records shared element identity

- records shared element identity
   - Expected: element_id equals `action_btn`
   - Expected: element_kind equals `button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records shared element identity")
val element_id = "action_btn"
val element_kind = "button"
expect(element_id).to_equal("action_btn")
expect(element_kind).to_equal("button")
```

</details>

#### records structured error shape

- records structured error shape
   - Expected: error_code equals `not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records structured error shape")
val error_code = "not_found"
expect(error_code).to_equal("not_found")
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
val actions = ["click", "type", "submit"]
expect(actions.len()).to_equal(3)
expect(actions[0]).to_equal("click")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/shared_ui_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Shared UI contract portable smoke.
- Shared UI contract portable smoke

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b570a6512d57d3fd57801edd64b1ae9bd544d615b8c826b8e80955ed428ec338`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b570a6512d57d3fd57801edd64b1ae9bd544d615b8c826b8e80955ed428ec338`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b570a6512d57d3fd57801edd64b1ae9bd544d615b8c826b8e80955ed428ec338`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/gui/ui/shared_ui_contract_spec.spl
mirror: doc/06_spec/03_system/gui/ui/shared_ui_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/ui/shared_ui_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/ui/shared_ui_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/ui/shared_ui_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/ui/shared_ui_contract_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records protocol version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/shared_ui_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records shared element identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/shared_ui_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records structured error shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
