# Ui Access Vision Specification

> 1. bounds: Some

<!-- sdn-diagram:id=ui_access_vision_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_vision_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_vision_spec -> std
ui_access_vision_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_vision_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Vision Specification

## Scenarios

### ui_access_vision sidecar contracts

#### stores bounds, marks, issues, and capture result fields

1. bounds: Some
   - Expected: result.bounds.len() equals `1`
   - Expected: result.bounds[0].canonical_id equals `main#submit_btn`
   - Expected: result.marks.len() equals `1`
   - Expected: result.marks[0].label equals `Submit`
   - Expected: result.issues.len() equals `1`
   - Expected: result.issues[0].code equals `vision.no_image`
   - Expected: result.captured is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui/ui_access_vision_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
