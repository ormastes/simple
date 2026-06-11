# Structural Layout Report Specification

> <details>

<!-- sdn-diagram:id=structural_layout_report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=structural_layout_report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

structural_layout_report_spec -> std
structural_layout_report_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=structural_layout_report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Structural Layout Report Specification

## Scenarios

### wm_compare structural layout reports

#### reports matching TUI and GUI line structure before pixel comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui_lines = ["File Edit", "Status OK"]
val gui_lines = ["File Edit", "Status OK"]
val report = structural_layout_compare(
    "tui", "gui", 80, 24,
    tui_lines, gui_lines,
    "runtime_evidence selected=cpu_simd_x86;status=Initialized",
    "test/baselines/wm_compare/probe/diff.ppm"
)
expect(report.status).to_equal("layout_match")
expect(report.mismatch_count).to_equal(0)
val sdn = structural_layout_report_sdn(report, tui_lines, gui_lines)
expect(sdn).to_contain("structural_layout_report")
expect(sdn).to_contain("backend_evidence")
expect(sdn).to_contain("pixel_link")
```

</details>

#### separates geometry mismatch from capture or pixel failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = structural_layout_compare(
    "tui", "gui", 80, 24,
    ["Toolbar", "Body"],
    ["Toolbar", "Body shifted"],
    "runtime_evidence selected=vulkan;status=Unavailable",
    ""
)
expect(report.status).to_equal("layout_mismatch")
expect(report.mismatch_count).to_equal(1)
val sdn = structural_layout_report_sdn(report, ["Toolbar", "Body"], ["Toolbar", "Body shifted"])
expect(sdn).to_contain("layout_mismatch")
expect(sdn).to_contain("Body shifted")
expect(sdn).to_contain("status=Unavailable")
```

</details>

#### fails closed for invalid structural viewport dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = structural_layout_compare(
    "tui", "gui", 0, 24,
    [], [], "", ""
)
expect(report.status).to_equal("invalid_viewport")
expect(report.mismatch_count).to_equal(1)
```

</details>

#### exports TUI rows as stable cell geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = ["AB", "C"]
val cells_sdn = tui_cell_grid_sdn("tui", rows, 8, 16)
expect(cells_sdn).to_contain("tui_cell_grid")
expect(cells_sdn).to_contain("count: 3")
expect(cells_sdn).to_contain("row: 0 col: 1 x: 8 y: 0")
expect(cells_sdn).to_contain("row: 1 col: 0 x: 0 y: 16")
```

</details>

#### exports GUI layout boxes with stable node labels

- structural layout box
- structural layout box


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = [
    structural_layout_box("toolbar.save", 0, 0, 48, 24, "Save"),
    structural_layout_box("editor.body", 0, 24, 320, 200, "Body")
]
val sdn = structural_layout_boxes_sdn("gui", boxes)
expect(sdn).to_contain("layout_boxes")
expect(sdn).to_contain("source: \"gui\"")
expect(sdn).to_contain("label: \"toolbar.save\"")
expect(sdn).to_contain("x: 0 y: 24 width: 320 height: 200")
```

</details>

#### compares GUI layout box geometry before pixel comparison

- structural layout box
- structural layout box
- structural layout box
- structural layout box
   - Expected: report.status equals `layout_mismatch`
   - Expected: report.mismatch_count equals `1`
   - Expected: report.source_a_count equals `2`
   - Expected: report.source_b_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chrome_boxes = [
    structural_layout_box("toolbar.save", 0, 0, 48, 24, "Save"),
    structural_layout_box("editor.body", 0, 24, 320, 200, "Body")
]
val simple_boxes = [
    structural_layout_box("toolbar.save", 0, 0, 48, 24, "Save"),
    structural_layout_box("editor.body", 0, 32, 320, 200, "Body")
]
val report = structural_box_layout_compare(
    "chrome", "simple", 320, 240,
    chrome_boxes, simple_boxes,
    "runtime_evidence selected=metal;status=Unavailable",
    "test/baselines/wm_compare/gui/diff.ppm"
)
expect(report.status).to_equal("layout_mismatch")
expect(report.mismatch_count).to_equal(1)
expect(report.source_a_count).to_equal(2)
expect(report.source_b_count).to_equal(2)
val sdn = structural_box_layout_report_sdn(report, chrome_boxes, simple_boxes)
expect(sdn).to_contain("structural_box_layout_report")
expect(sdn).to_contain("backend_evidence: \"runtime_evidence selected=metal;status=Unavailable\"")
expect(sdn).to_contain("pixel_link: \"test/baselines/wm_compare/gui/diff.ppm\"")
expect(sdn).to_contain("source_a_boxes")
expect(sdn).to_contain("source_b_boxes")
expect(sdn).to_contain("y: 32")
```

</details>

#### attaches structural evidence to famous-site layout mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val metrics = rt_file_read_text(famous_site_sample_chrome_metrics_path(sample.id))
val report = build_site_corpus_structural_layout_report(sample, metrics, 132)
expect(report).to_contain("structural_layout_report")
expect(report).to_contain("source_a: \"chrome_metrics\"")
expect(report).to_contain("source_b: \"simple_layout\"")
```

</details>

#### compares famous-site corpus div geometry against Chrome metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = build_famous_site_sample_corpus()[0]
val metrics = rt_file_read_text(famous_site_sample_chrome_metrics_path(sample.id))
val report = build_site_corpus_div_geometry_report(sample, metrics, 160, 120)
expect(report).to_contain("structural_box_layout_report")
expect(report).to_contain("status: \"layout_match\"")
expect(report).to_contain("source_a: \"chrome_metrics_div\"")
expect(report).to_contain("source_b: \"simple_renderer_div\"")
expect(report).to_contain("width: 120")
expect(report).to_contain("height: 40")
expect(report).to_contain("background_color: \"rgb(37, 99, 235)\"")
```

</details>

#### summarizes exact div geometry for the first six famous-site corpus rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = build_site_corpus_div_geometry_summary(6, 160, 120)
expect(report).to_contain("famous_site_corpus_div_geometry_summary")
expect(report).to_contain("summary: (offset: 0 selected: 6 matched: 6 mismatched: 0 missing_metrics: 0")
expect(report).to_contain("sample id: \"site_0_google\" status: \"layout_match\"")
expect(report).to_contain("sample id: \"site_5_tiktok\" status: \"layout_match\"")
```

</details>

#### summarizes exact div geometry for the next six famous-site corpus rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = build_site_corpus_div_geometry_summary_range(6, 6, 160, 120)
expect(report).to_contain("famous_site_corpus_div_geometry_summary")
expect(report).to_contain("summary: (offset: 6 selected: 6 matched: 6 mismatched: 0 missing_metrics: 0")
expect(report).to_contain("sample id: \"site_6_wikipedia\" status: \"layout_match\"")
expect(report).to_contain("sample id: \"site_11_microsoft\" status: \"layout_match\"")
```

</details>

#### summarizes exact div geometry for the full famous-site corpus in one process

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = build_site_corpus_div_geometry_summary(0, 160, 120)
expect(report).to_contain("famous_site_corpus_div_geometry_summary")
expect(report).to_contain("summary: (offset: 0 selected: 132 matched: 132 mismatched: 0 missing_metrics: 0")
expect(report).to_contain("sample id: \"site_0_google\" status: \"layout_match\"")
expect(report).to_contain("sample id: \"site_131_epic_games\" status: \"layout_match\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/structural_layout_report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare structural layout reports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
