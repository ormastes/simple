# Low Dependency UI dynSMF Dependency Gate System Specification

> Verifies the selected low_dependency_ui_dynsmf UI dependency boundary at the feature level. The system spec reads production adapter source files and checks that base TUI stays out of web/HTML/CSS implementation modules while HTML-capable adapters depend on explicit HTML widget and shared web-render contracts.

<!-- sdn-diagram:id=low_dependency_ui_dynsmf_dependency_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=low_dependency_ui_dynsmf_dependency_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

low_dependency_ui_dynsmf_dependency_gate_spec -> std
low_dependency_ui_dynsmf_dependency_gate_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=low_dependency_ui_dynsmf_dependency_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Low Dependency UI dynSMF Dependency Gate System Specification

Verifies the selected low_dependency_ui_dynsmf UI dependency boundary at the feature level. The system spec reads production adapter source files and checks that base TUI stays out of web/HTML/CSS implementation modules while HTML-capable adapters depend on explicit HTML widget and shared web-render contracts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the selected low_dependency_ui_dynsmf UI dependency boundary at the
feature level. The system spec reads production adapter source files and checks
that base TUI stays out of web/HTML/CSS implementation modules while
HTML-capable adapters depend on explicit HTML widget and shared web-render
contracts.

## Examples

The TUI backend closure may reach TUI renderer helpers, dashboard render
formatters, and common UI contracts. It must not reach sibling web, browser,
HTML widget, or CSS implementation modules. Web-capable adapters may import
HTML widgets directly and must retain the shared web-render contract.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-001, REQ-002, REQ-003, REQ-009, NFR-001, NFR-002, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### low dependency UI dynSMF dependency gate

#### keeps exact-prefix TUI closure out of web HTML browser and CSS modules

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_dependency_module_matches("app.ui.tui_web.backend", "app.ui.tui")).to_equal(false)
val report = ui_dependency_report(feature_tui_sources(), feature_tui_policy("app.ui.tui.backend"))
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps the shared widget compatibility shim out of HTML and CSS implementation

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ui_dependency_report(feature_tui_sources(), feature_tui_policy("app.ui.render.widgets"))
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps HTML-capable adapters on explicit HTML widgets and shared web-render contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sources = feature_html_adapter_sources()
val web_imports = ui_dependency_direct_imports(sources, "app.ui.web.backend")
expect(ui_dependency_imports_module(web_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(web_imports, "app.ui.render.widgets")).to_equal(false)
expect(ui_dependency_imports_module(web_imports, "common.ui.web_render_api")).to_equal(true)

val tauri_imports = ui_dependency_direct_imports(sources, "app.ui.tauri.backend")
expect(ui_dependency_imports_module(tauri_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(tauri_imports, "app.ui.render.widgets")).to_equal(false)
expect(ui_dependency_imports_module(tauri_imports, "common.ui.web_render_api")).to_equal(true)

val electron_imports = ui_dependency_direct_imports(sources, "app.ui.electron.backend")
expect(ui_dependency_imports_module(electron_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(electron_imports, "app.ui.render.widgets")).to_equal(false)
expect(ui_dependency_imports_module(electron_imports, "common.ui.web_render_api")).to_equal(true)

val browser_imports = ui_dependency_direct_imports(sources, "app.ui.browser.backend")
expect(ui_dependency_imports_module(browser_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(browser_imports, "app.ui.render.widgets")).to_equal(false)
expect(ui_dependency_imports_module(browser_imports, "common.ui.web_render_api")).to_equal(true)

val tui_web_imports = ui_dependency_direct_imports(sources, "app.ui.tui_web.backend")
expect(ui_dependency_imports_module(tui_web_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(tui_web_imports, "app.ui.render.widgets")).to_equal(false)
expect(ui_dependency_imports_module(tui_web_imports, "common.ui.web_render_api")).to_equal(true)
```

</details>

#### keeps HTML and CSS implementation behind explicit lazy renderer capabilities

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html_cap = renderer_capability_html_widgets()
val css_cap = renderer_capability_css_provider()
val tui_cap = renderer_capability_tui_widgets()
expect(html_cap.implementation_module).to_equal("app.ui.render.html_widgets")
expect(css_cap.implementation_module).to_equal("app.ui.render.css")
expect(renderer_capability_is_lazy(html_cap)).to_equal(true)
expect(renderer_capability_is_lazy(css_cap)).to_equal(true)
expect(tui_cap.default_autoload).to_equal(true)
```

</details>

#### selects CSS payload only for requested component styles

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val card_only = css_for_components(["card"])
expect(card_only).to_contain(".card")
expect(feature_contains_text(card_only, "table {")).to_equal(false)
expect(feature_contains_text(card_only, ".progress")).to_equal(false)
val card_and_progress = css_for_components(["card", "progress"])
expect(card_and_progress).to_contain(".card")
expect(card_and_progress).to_contain(".progress")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
