# GUI Widget Rendering Fixture Coverage Gate

> Validates that every current `WidgetKind.to_wire()` value is represented in the HTML widget renderer dispatch table, has an emitted renderer class marker, and is covered by the renderer spec corpus.

<!-- sdn-diagram:id=gui_widget_rendering_fixture_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_widget_rendering_fixture_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_widget_rendering_fixture_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_widget_rendering_fixture_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Widget Rendering Fixture Coverage Gate

Validates that every current `WidgetKind.to_wire()` value is represented in the HTML widget renderer dispatch table, has an emitted renderer class marker, and is covered by the renderer spec corpus.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_widget_rendering_fixture_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that every current `WidgetKind.to_wire()` value is represented in
the HTML widget renderer dispatch table, has an emitted renderer class marker,
and is covered by the renderer spec corpus.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** N/A
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-gui-widget-rendering-fixture-coverage \
REPORT_PATH=build/test-gui-widget-rendering-fixture-coverage/report.md \
sh scripts/check/check-gui-widget-rendering-fixture-coverage.shs
```

## Acceptance

- The gate derives the widget inventory from `WidgetKind.to_wire()`.
- All 43 widget wire kinds have `render_html_widget` dispatch coverage.
- All 43 widget wire kinds have renderer class marker coverage.
- All 43 widget wire kinds have renderer spec marker coverage.
- All 43 widget wire kinds have executable render fixture witness coverage:
  a spec source references the widget wire, calls `render_html_widget` or
  `render_html_tree`, and asserts the expected renderer class.
- All 43 widget wire kinds have canonical RenderDoc HTML fixture coverage:
  `generated_gui_vulkan_renderdoc_fixture.html` contains the expected renderer
  class and widget wire marker for each widget.

## Scenarios

### GUI widget rendering fixture coverage gate

#### covers every WidgetKind in HTML renderer specs

- Run the widget rendering fixture coverage gate
   - Expected: code equals `0`
- Read the emitted evidence contract
- Assert fail-closed 43/43 widget coverage
   - Expected: widget_count equals `43`
   - Expected: dispatch_count equals `43`
   - Expected: class_count equals `43`
   - Expected: spec_count equals `43`
   - Expected: render_fixture_count equals `43`
   - Expected: renderdoc_fixture_count equals `43`
   - Expected: renderdoc_fixture_feature_count equals `43`
   - Expected: missing_dispatch equals ``
   - Expected: missing_classes equals ``
   - Expected: missing_specs equals ``
   - Expected: missing_render_fixtures equals ``
   - Expected: missing_renderdoc_fixtures equals ``
   - Expected: missing_renderdoc_fixture_features equals ``
   - Expected: spec_widget_classes.split(",").len() equals `43`
   - Expected: render_fixture_widgets.split(",").len() equals `43`
   - Expected: render_fixture_widget_classes.split(",").len() equals `43`
   - Expected: renderdoc_fixture_widgets.split(",").len() equals `43`
   - Expected: renderdoc_fixture_widget_classes.split(",").len() equals `43`
   - Expected: renderdoc_fixture_widget_features.split(",").len() equals `43`
   - Expected: expected_renderdoc_fixture_features.split(",").len() equals `43`
- Verify representative newly covered widget classes are in the contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the widget rendering fixture coverage gate")
val command = "rm -rf build/test-gui-widget-rendering-fixture-coverage && BUILD_DIR=build/test-gui-widget-rendering-fixture-coverage REPORT_PATH=build/test-gui-widget-rendering-fixture-coverage/report.md sh scripts/check/check-gui-widget-rendering-fixture-coverage.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the emitted evidence contract")
val evidence = file_read("build/test-gui-widget-rendering-fixture-coverage/evidence.env")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_status=pass")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_reason=pass")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_widget_kind_source=src/lib/common/ui/widget_kind.spl")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_renderer_source=src/app/ui.render/html_widgets.spl")
expect(evidence).to_contain("gui_widget_rendering_fixture_coverage_renderdoc_fixture_source=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")

val widget_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_widget_kind_count")
val dispatch_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_dispatch_covered_count")
val class_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderer_class_covered_count")
val spec_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_spec_covered_count")
val render_fixture_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_render_fixture_covered_count")
val renderdoc_fixture_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_covered_count")
val renderdoc_fixture_feature_count = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_feature_covered_count")
val missing_dispatch = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_dispatch_widgets")
val missing_classes = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_renderer_classes")
val missing_specs = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_spec_widgets")
val missing_render_fixtures = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_render_fixture_widgets")
val missing_renderdoc_fixtures = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_renderdoc_fixture_widgets")
val missing_renderdoc_fixture_features = _value_of(evidence, "gui_widget_rendering_fixture_coverage_missing_renderdoc_fixture_features")
val spec_widget_classes = _value_of(evidence, "gui_widget_rendering_fixture_coverage_spec_widget_classes")
val render_fixture_widgets = _value_of(evidence, "gui_widget_rendering_fixture_coverage_render_fixture_widgets")
val render_fixture_widget_classes = _value_of(evidence, "gui_widget_rendering_fixture_coverage_render_fixture_widget_classes")
val renderdoc_fixture_widgets = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_widgets")
val renderdoc_fixture_widget_classes = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_classes")
val renderdoc_fixture_widget_features = _value_of(evidence, "gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_features")
val expected_renderdoc_fixture_features = _value_of(evidence, "gui_widget_rendering_fixture_coverage_expected_renderdoc_fixture_features")

step("Assert fail-closed 43/43 widget coverage")
expect(widget_count).to_equal("43")
expect(dispatch_count).to_equal("43")
expect(class_count).to_equal("43")
expect(spec_count).to_equal("43")
expect(render_fixture_count).to_equal("43")
expect(renderdoc_fixture_count).to_equal("43")
expect(renderdoc_fixture_feature_count).to_equal("43")
expect(missing_dispatch).to_equal("")
expect(missing_classes).to_equal("")
expect(missing_specs).to_equal("")
expect(missing_render_fixtures).to_equal("")
expect(missing_renderdoc_fixtures).to_equal("")
expect(missing_renderdoc_fixture_features).to_equal("")
expect(spec_widget_classes.split(",").len()).to_equal(43)
expect(render_fixture_widgets.split(",").len()).to_equal(43)
expect(render_fixture_widget_classes.split(",").len()).to_equal(43)
expect(renderdoc_fixture_widgets.split(",").len()).to_equal(43)
expect(renderdoc_fixture_widget_classes.split(",").len()).to_equal(43)
expect(renderdoc_fixture_widget_features.split(",").len()).to_equal(43)
expect(expected_renderdoc_fixture_features.split(",").len()).to_equal(43)

step("Verify representative newly covered widget classes are in the contract")
expect(evidence).to_contain("radio:widget-radio")
expect(evidence).to_contain("heading:widget-heading")
expect(evidence).to_contain("navigation_bar:widget-navigation-bar")
expect(evidence).to_contain("tab_bar:widget-tab-bar")
expect(evidence).to_contain("card:widget-card")
expect(evidence).to_contain("switch:widget-switch")
expect(evidence).to_contain("segmented_control:widget-segmented-control")
expect(evidence).to_contain("search_bar:widget-search-bar")
expect(renderdoc_fixture_widgets).to_contain("glass_title_bar")
expect(renderdoc_fixture_widgets).to_contain("command_palette")
expect(renderdoc_fixture_widgets).to_contain("empty_state")
expect(renderdoc_fixture_widget_classes).to_contain("glass_title_bar:widget-glass-title-bar")
expect(renderdoc_fixture_widget_classes).to_contain("command_palette:widget-command-palette")
expect(renderdoc_fixture_widget_classes).to_contain("empty_state:widget-empty-state")
expect(renderdoc_fixture_widget_features).to_contain("glass_title_bar:window-titlebar")
expect(renderdoc_fixture_widget_features).to_contain("command_palette:command-search")
expect(renderdoc_fixture_widget_features).to_contain("empty_state:empty-feedback")

val report = file_read("build/test-gui-widget-rendering-fixture-coverage/report.md")
expect(report).to_contain("# GUI Widget Rendering Fixture Coverage")
expect(report).to_contain("- spec markers covered: 43")
expect(report).to_contain("- render fixture witnesses covered: 43")
expect(report).to_contain("- RenderDoc HTML fixture widgets covered: 43")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
