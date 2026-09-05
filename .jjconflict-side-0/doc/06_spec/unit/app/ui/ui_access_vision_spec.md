# Ui Access Vision Specification

> Tests covering ui_access_vision sidecar contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Vision Specification

## Scenarios

### ui_access_vision sidecar contracts

#### stores bounds, marks, issues, and capture result fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores bounds, marks, issues, and capture result fields
   - Expected: result.bounds.len() equals `1`
   - Expected: result.bounds[0].canonical_id equals `main#submit_btn`
   - Expected: result.marks.len() equals `1`
   - Expected: result.marks[0].label equals `Submit`
   - Expected: result.issues.len() equals `1`
   - Expected: result.issues[0].code equals `vision.no_image`
   - Expected: result.captured is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores bounds, marks, issues, and capture result fields")
val bounds = _bounds("main#submit_btn", 10, 20, 80, 24)
val mark = UiAccessVisionMark(
    mark_id: "mark_1",
    surface_id: "main",
    canonical_id: "main#submit_btn",
    label: "Submit",
    kind: "button",
    bounds: bounds,
    confidence: 97,
    details: "primary action"
)
val issue = UiAccessVisionIssue(
    code: "vision.no_image",
    severity: "warning",
    message: "No image source was provided to the vision sidecar.",
    surface_id: "main",
    canonical_id: "main#submit_btn",
    bounds: Some(bounds),
    details: "Provide a screenshot or image reference before asking for pixel inspection."
)
val result = UiAccessVisionCaptureResult(
    snapshot_protocol_version: 1,
    snapshot_mode: "NORMAL",
    active_surface: "main",
    image_ref: "",
    bounds: [bounds],
    marks: [mark],
    issues: [issue],
    captured: false
)
expect(result.bounds.len()).to_equal(1)
expect(result.bounds[0].canonical_id).to_equal("main#submit_btn")
expect(result.marks.len()).to_equal(1)
expect(result.marks[0].label).to_equal("Submit")
expect(result.issues.len()).to_equal(1)
expect(result.issues[0].code).to_equal("vision.no_image")
expect(result.captured).to_equal(false)
```

</details>

#### returns structured issues from the no-image default provider

- returns structured issues from the no-image default provider
   - Expected: provider.provider_name() equals `no_image`
   - Expected: result.snapshot_protocol_version equals `1`
   - Expected: result.snapshot_mode equals `NORMAL`
   - Expected: result.active_surface equals `main`
   - Expected: result.captured is false
   - Expected: result.marks.len() equals `0`
   - Expected: result.issues.len() equals `1`
   - Expected: result.issues[0].code equals `vision.no_image`
   - Expected: result.issues[0].severity equals `warning`
   - Expected: result.issues[0].bounds != nil is true
   - Expected: issue_bounds.x equals `10`
   - Expected: issue_bounds.w equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns structured issues from the no-image default provider")
val provider = UiAccessNoImageVisionProvider.new()
expect(provider.provider_name()).to_equal("no_image")
val result = provider.capture(_snapshot(), "", [_bounds("main#submit_btn", 10, 20, 80, 24)])
expect(result.snapshot_protocol_version).to_equal(1)
expect(result.snapshot_mode).to_equal("NORMAL")
expect(result.active_surface).to_equal("main")
expect(result.captured).to_equal(false)
expect(result.marks.len()).to_equal(0)
expect(result.issues.len()).to_equal(1)
expect(result.issues[0].code).to_equal("vision.no_image")
expect(result.issues[0].severity).to_equal("warning")
expect(result.issues[0].bounds != nil).to_equal(true)
if val issue_bounds = result.issues[0].bounds:
    expect(issue_bounds.x).to_equal(10)
    expect(issue_bounds.w).to_equal(80)
```

</details>

#### reports unsupported-image issues instead of pretending to capture pixels

- reports unsupported-image issues instead of pretending to capture pixels
   - Expected: result.captured is false
   - Expected: result.marks.len() equals `0`
   - Expected: result.issues.len() equals `1`
   - Expected: result.issues[0].code equals `vision.unsupported_image`
   - Expected: result.issues[0].severity equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unsupported-image issues instead of pretending to capture pixels")
val provider = UiAccessNoImageVisionProvider.new()
val result = provider.capture(_snapshot(), "file:///tmp/screenshot.png", [])
expect(result.captured).to_equal(false)
expect(result.marks.len()).to_equal(0)
expect(result.issues.len()).to_equal(1)
expect(result.issues[0].code).to_equal("vision.unsupported_image")
expect(result.issues[0].severity).to_equal("info")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/ui_access_vision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_access_vision sidecar contracts.
- ui_access_vision sidecar contracts

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd5b64e969b77e8f44714cc679f451c6aec35e66c82b61547f61aaafa394f8b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd5b64e969b77e8f44714cc679f451c6aec35e66c82b61547f61aaafa394f8b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd5b64e969b77e8f44714cc679f451c6aec35e66c82b61547f61aaafa394f8b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/ui/ui_access_vision_spec.spl
mirror: doc/06_spec/unit/app/ui/ui_access_vision_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/ui_access_vision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/ui_access_vision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/ui_access_vision_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/ui_access_vision_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores bounds, marks, issues, and capture result fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ui_access_vision_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns structured issues from the no-image default provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ui_access_vision_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports unsupported-image issues instead of pretending to capture pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
