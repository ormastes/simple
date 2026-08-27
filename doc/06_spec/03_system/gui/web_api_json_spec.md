# Web Api Json Specification

> Tests covering state_to_json, widgets_to_json.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Api Json Specification

## Scenarios

### state_to_json

<details>
<summary>Advanced: serializes demo state to JSON with expected fields</summary>

#### serializes demo state to JSON with expected fields _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serializes demo state to JSON with expected fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes demo state to JSON with expected fields")
val json = web_api_state_json("examples/06_io/ui/demo.ui.sdn")
expect(json.len()).to_be_greater_than(0)
expect(json).to_contain("mode")
expect(json).to_contain("NORMAL")
expect(json).to_contain("title")
expect(json).to_contain("Simple UI Demo")
expect(json).to_contain("theme")
expect(json).to_contain("dark")
expect(json).to_contain("focused_id")
```

</details>


</details>

<details>
<summary>Advanced: serializes minimal state to JSON</summary>

#### serializes minimal state to JSON _(slow)_

- serializes minimal state to JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes minimal state to JSON")
val json = web_api_state_json("examples/06_io/ui/minimal.ui.sdn")
expect(json).to_contain("Minimal")
expect(json).to_contain("NORMAL")
```

</details>


</details>

### widgets_to_json

<details>
<summary>Advanced: serializes demo widgets to non-empty JSON array</summary>

#### serializes demo widgets to non-empty JSON array _(slow)_

- serializes demo widgets to non-empty JSON array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes demo widgets to non-empty JSON array")
val json = web_api_widgets_json("examples/06_io/ui/demo.ui.sdn")
expect(json.len()).to_be_greater_than(2)
expect(json).to_start_with("[")
expect(json).to_end_with("]")
expect(json).to_contain("sidebar")
expect(json).to_contain("content")
expect(json).to_contain("status")
```

</details>


</details>

<details>
<summary>Advanced: serializes minimal widgets to non-empty JSON array</summary>

#### serializes minimal widgets to non-empty JSON array _(slow)_

- serializes minimal widgets to non-empty JSON array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes minimal widgets to non-empty JSON array")
val json = web_api_widgets_json("examples/06_io/ui/minimal.ui.sdn")
expect(json.len()).to_be_greater_than(2)
expect(json).to_start_with("[")
expect(json).to_end_with("]")
expect(json).to_contain("main")
expect(json).to_contain("greeting")
expect(json).to_contain("status")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/web_api_json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering state_to_json, widgets_to_json.
- state_to_json
- widgets_to_json

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `774d7fff03d7115a2be48e9866a8a482219eb3a71bfc5eb71e6e599ff7b5e581`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `774d7fff03d7115a2be48e9866a8a482219eb3a71bfc5eb71e6e599ff7b5e581`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `774d7fff03d7115a2be48e9866a8a482219eb3a71bfc5eb71e6e599ff7b5e581`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/web_api_json_spec.spl
mirror: doc/06_spec/03_system/gui/web_api_json_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/web_api_json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_api_json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_api_json_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes demo state to JSON with expected fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_api_json_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes minimal state to JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_api_json_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes demo widgets to non-empty JSON array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
