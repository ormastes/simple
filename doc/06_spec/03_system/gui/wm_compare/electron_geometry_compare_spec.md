# Electron Geometry Compare Specification

> Tests covering wm_compare electron geometry compare.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Geometry Compare Specification

## Scenarios

### wm_compare electron geometry compare

#### converts Electron geometry JSON into structural layout boxes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts Electron geometry JSON into structural layout boxes
- Parse Electron Chromium geometry JSON
- Check exact labeled border-box geometry
   - Expected: boxes.len() equals `2`
   - Expected: boxes[0].label equals `header`
   - Expected: boxes[0].x equals `8`
   - Expected: boxes[0].width equals `120`
   - Expected: boxes[1].label equals `footer`
   - Expected: boxes[1].y equals `68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts Electron geometry JSON into structural layout boxes")
step("Parse Electron Chromium geometry JSON")
val geometry_json = "{\"producer\":\"electron-chromium-geometry\",\"viewport\":{\"width\":320,\"height\":240},\"items\":[{\"label\":\"header\",\"tag\":\"div\",\"x\":8,\"y\":8,\"width\":120,\"height\":20,\"text\":\"\"},{\"label\":\"footer\",\"tag\":\"div\",\"x\":8,\"y\":68,\"width\":120,\"height\":20,\"text\":\"\"}]}"
val boxes = electron_geometry_json_to_boxes(geometry_json)
step("Check exact labeled border-box geometry")
expect(boxes.len()).to_equal(2)
expect(boxes[0].label).to_equal("header")
expect(boxes[0].x).to_equal(8)
expect(boxes[0].width).to_equal(120)
expect(boxes[1].label).to_equal("footer")
expect(boxes[1].y).to_equal(68)
```

</details>

#### converts Chrome live geometry JSON using the same structural schema

- converts Chrome live geometry JSON using the same structural schema
- Parse Chrome headless geometry with computed style box fields
- Check exact border-box, padding, border, background, and text fields
   - Expected: boxes.len() equals `2`
   - Expected: boxes[0].label equals `box`
   - Expected: boxes[0].x equals `7`
   - Expected: boxes[0].y equals `9`
   - Expected: boxes[0].width equals `33`
   - Expected: boxes[0].height equals `17`
   - Expected: boxes[0].rect_left equals `7.125`
   - Expected: boxes[0].rect_top equals `9.500`
   - Expected: boxes[0].rect_width equals `33.250`
   - Expected: boxes[0].rect_height equals `17.750`
   - Expected: boxes[0].padding_left equals `4`
   - Expected: boxes[0].padding_top equals `5`
   - Expected: boxes[0].padding_right equals `6`
   - Expected: boxes[0].padding_bottom equals `7`
   - Expected: boxes[0].border_left equals `1`
   - Expected: boxes[0].border_top equals `2`
   - Expected: boxes[0].border_right equals `3`
   - Expected: boxes[0].border_bottom equals `4`
   - Expected: boxes[0].background_color equals `rgb(10, 20, 30)`
   - Expected: boxes[0].color equals `rgb(0, 0, 0)`
   - Expected: boxes[0].display equals `flex`
   - Expected: boxes[0].align_items equals `baseline`
   - Expected: boxes[0].font_size equals `32px`
   - Expected: boxes[0].line_height equals `32px`
   - Expected: boxes[0].font_family equals `Times New Roman`
   - Expected: boxes[0].font_weight equals `400`
   - Expected: boxes[0].text equals `Hello`
   - Expected: boxes[1].background_color equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts Chrome live geometry JSON using the same structural schema")
step("Parse Chrome headless geometry with computed style box fields")
val geometry_json = "{\"producer\":\"chrome-headless-geometry\",\"viewport\":{\"width\":80,\"height\":50},\"items\":[{\"index\":0,\"label\":\"box\",\"tag\":\"div\",\"x\":7,\"y\":9,\"width\":33,\"height\":17,\"rectLeft\":\"7.125\",\"rectTop\":\"9.500\",\"rectWidth\":\"33.250\",\"rectHeight\":\"17.750\",\"paddingLeft\":4,\"paddingTop\":5,\"paddingRight\":6,\"paddingBottom\":7,\"borderLeft\":1,\"borderTop\":2,\"borderRight\":3,\"borderBottom\":4,\"backgroundColor\":\"rgb(10, 20, 30)\",\"color\":\"rgb(0, 0, 0)\",\"display\":\"flex\",\"alignItems\":\"baseline\",\"fontSize\":\"32px\",\"lineHeight\":\"32px\",\"fontFamily\":\"Times New Roman\",\"fontWeight\":\"400\",\"text\":\"Hello\"},{\"index\":1,\"label\":\"transparent\",\"tag\":\"div\",\"x\":0,\"y\":0,\"width\":1,\"height\":1,\"backgroundColor\":\"rgba(0, 0, 0, 0)\",\"text\":\"\"}]}"
val boxes = electron_geometry_json_to_boxes(geometry_json)
step("Check exact border-box, padding, border, background, and text fields")
expect(boxes.len()).to_equal(2)
expect(boxes[0].label).to_equal("box")
expect(boxes[0].x).to_equal(7)
expect(boxes[0].y).to_equal(9)
expect(boxes[0].width).to_equal(33)
expect(boxes[0].height).to_equal(17)
expect(boxes[0].rect_left).to_equal("7.125")
expect(boxes[0].rect_top).to_equal("9.500")
expect(boxes[0].rect_width).to_equal("33.250")
expect(boxes[0].rect_height).to_equal("17.750")
expect(boxes[0].padding_left).to_equal(4)
expect(boxes[0].padding_top).to_equal(5)
expect(boxes[0].padding_right).to_equal(6)
expect(boxes[0].padding_bottom).to_equal(7)
expect(boxes[0].border_left).to_equal(1)
expect(boxes[0].border_top).to_equal(2)
expect(boxes[0].border_right).to_equal(3)
expect(boxes[0].border_bottom).to_equal(4)
expect(boxes[0].background_color).to_equal("rgb(10, 20, 30)")
expect(boxes[0].color).to_equal("rgb(0, 0, 0)")
expect(boxes[0].display).to_equal("flex")
expect(boxes[0].align_items).to_equal("baseline")
expect(boxes[0].font_size).to_equal("32px")
expect(boxes[0].line_height).to_equal("32px")
expect(boxes[0].font_family).to_equal("Times New Roman")
expect(boxes[0].font_weight).to_equal("400")
expect(boxes[0].text).to_equal("Hello")
expect(boxes[1].background_color).to_equal("")
```

</details>

#### compares Electron geometry JSON against Simple-side boxes

- compares Electron geometry JSON against Simple-side boxes
- Build Electron geometry and Simple structural boxes with a y mismatch
- Compare exact structural geometry without pixel tolerance
   - Expected: report.status equals `layout_mismatch`
   - Expected: report.mismatch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares Electron geometry JSON against Simple-side boxes")
step("Build Electron geometry and Simple structural boxes with a y mismatch")
val geometry_json = "{\"producer\":\"electron-chromium-geometry\",\"viewport\":{\"width\":320,\"height\":240},\"items\":[{\"label\":\"header\",\"tag\":\"div\",\"x\":8,\"y\":8,\"width\":120,\"height\":20,\"text\":\"\"},{\"label\":\"footer\",\"tag\":\"div\",\"x\":8,\"y\":68,\"width\":120,\"height\":20,\"text\":\"\"}]}"
val simple_boxes = [
    structural_layout_box("header", 8, 8, 120, 20, ""),
    structural_layout_box("footer", 8, 72, 120, 20, "")
]
step("Compare exact structural geometry without pixel tolerance")
val report = compare_electron_geometry_json(
    "electron_geometry", "simple_layout",
    320, 240,
    geometry_json, simple_boxes,
    "runtime_evidence selected=electron_geometry;status=Initialized",
    "test/09_baselines/html_compat/02_block_boxes/report.sdn"
)
expect(report.status).to_equal("layout_mismatch")
expect(report.mismatch_count).to_equal(1)
val sdn = structural_box_layout_report_sdn(report, electron_geometry_json_to_boxes(geometry_json), simple_boxes)
expect(sdn).to_contain("label: \"header\"")
expect(sdn).to_contain("label: \"footer\"")
expect(sdn).to_contain("y: 72")
```

</details>

#### compares Chromium style box fields without pixel tolerance

- compares Chromium style box fields without pixel tolerance
- Build Chrome geometry with padding, border, and background style fields
- Fail closed on an exact border-width mismatch
   - Expected: report.status equals `layout_mismatch`
   - Expected: report.mismatch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares Chromium style box fields without pixel tolerance")
step("Build Chrome geometry with padding, border, and background style fields")
val geometry_json = "{\"producer\":\"chrome-headless-geometry\",\"viewport\":{\"width\":80,\"height\":50},\"items\":[{\"index\":0,\"label\":\"panel\",\"tag\":\"div\",\"x\":4,\"y\":6,\"width\":40,\"height\":20,\"paddingLeft\":8,\"paddingTop\":6,\"paddingRight\":8,\"paddingBottom\":6,\"borderLeft\":2,\"borderTop\":2,\"borderRight\":2,\"borderBottom\":2,\"backgroundColor\":\"rgb(40, 50, 60)\",\"text\":\"\"}]}"
val simple_boxes = [
    structural_layout_style_box("panel", 4, 6, 40, 20, 8, 6, 8, 6, 1, 2, 2, 2, "rgb(40, 50, 60)", "")
]
step("Fail closed on an exact border-width mismatch")
val report = compare_electron_geometry_json(
    "chrome_geometry", "simple_layout",
    80, 50,
    geometry_json, simple_boxes,
    "runtime_evidence selected=chrome-headless-geometry;blur_or_tolerance=false",
    "build/test/chrome_geometry/panel.json"
)
expect(report.status).to_equal("layout_mismatch")
expect(report.mismatch_count).to_equal(1)
```

</details>

#### fails closed for malformed geometry JSON

- fails closed for malformed geometry JSON
- Parse malformed geometry JSON
- Confirm malformed geometry produces no structural boxes
   - Expected: boxes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed for malformed geometry JSON")
step("Parse malformed geometry JSON")
val boxes = electron_geometry_json_to_boxes("{\"items\": [}")
step("Confirm malformed geometry produces no structural boxes")
expect(boxes.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_compare electron geometry compare.
- wm_compare electron geometry compare

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `375aeed0f8fccf49900710f9c01412e4fcb47d1650ee7fff9682bf134dc38ebe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `375aeed0f8fccf49900710f9c01412e4fcb47d1650ee7fff9682bf134dc38ebe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `375aeed0f8fccf49900710f9c01412e4fcb47d1650ee7fff9682bf134dc38ebe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/electron_geometry_compare_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/electron_geometry_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/electron_geometry_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Electron geometry JSON into structural layout boxes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Chrome live geometry JSON using the same structural schema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares Electron geometry JSON against Simple-side boxes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
