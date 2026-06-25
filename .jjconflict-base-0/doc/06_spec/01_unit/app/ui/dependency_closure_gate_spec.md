# Low Dependency UI Dependency Closure Gate

> Verifies exact-prefix UI dependency closure policy for the selected low_dependency_ui_dynsmf thin slice. The gate walks only reachable imports from the selected root and reports forbidden backend implementation dependencies.

<!-- sdn-diagram:id=dependency_closure_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dependency_closure_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dependency_closure_gate_spec -> std
dependency_closure_gate_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dependency_closure_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Low Dependency UI Dependency Closure Gate

Verifies exact-prefix UI dependency closure policy for the selected low_dependency_ui_dynsmf thin slice. The gate walks only reachable imports from the selected root and reports forbidden backend implementation dependencies.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/01_unit/app/ui/dependency_closure_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies exact-prefix UI dependency closure policy for the selected
low_dependency_ui_dynsmf thin slice. The gate walks only reachable imports from
the selected root and reports forbidden backend implementation dependencies.

## Examples

The TUI root fixture may depend on common UI widgets and TUI render helpers, but
must not match sibling names such as `app.ui.tui_web` or pull HTML renderer
modules through a shared renderer surface. The real-source case reads the
current `app.ui.tui.backend` closure from `src/` to keep the production TUI lane
inside TUI/common renderer modules.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-001, REQ-002, REQ-009, NFR-001, NFR-002, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### UI dependency exact-prefix gate

#### does not treat app.ui.tui_web as part of app.ui.tui

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_dependency_module_matches("app.ui.tui_web", "app.ui.tui")).to_equal(false)
expect(ui_dependency_module_matches("app.ui.tui.screen", "app.ui.tui")).to_equal(true)
```

</details>

#### extracts structured use imports without imported symbol braces

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imports = ui_dependency_extract_imports("use app.ui.render.html_widgets." + "{" + "render_html_tree" + "}\nuse app.ui.web.html\n")
expect(imports[0]).to_equal("app.ui.render.html_widgets")
expect(imports[1]).to_equal("app.ui.web.html")
```

</details>

#### keeps the base TUI fixture free of forbidden web and HTML modules

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ui_dependency_report(clean_tui_fixture(), tui_policy("app.ui.tui"))
expect(report.module_count).to_equal(4)
expect(report.violation_count).to_equal(0)
```

</details>

#### detects when common renderer widgets pull HTML implementation

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ui_dependency_report(html_leak_fixture(), tui_policy("app.ui.render"))
expect(report.module_count).to_equal(3)
expect(report.violation_count).to_equal(1)
```

</details>

#### counts unresolved forbidden imports as dependency violations

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ui_dependency_report(unresolved_html_leak_fixture(), tui_policy("app.ui.tui.backend"))
expect(report.violation_count).to_equal(1)
```

</details>

#### keeps the current app.ui.tui.backend source closure out of web HTML CSS and browser modules

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ui_dependency_report(real_tui_backend_sources(), tui_policy("app.ui.tui.backend"))
expect(report.module_count).to_equal(13)
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps the current app.ui.render.widgets shim free of HTML and CSS implementation imports

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ui_dependency_report(real_tui_backend_sources(), tui_policy("app.ui.render.widgets"))
expect(report.module_count).to_equal(12)
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps HTML-capable adapters on direct html_widgets imports instead of the shared widgets shim

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sources = real_html_adapter_sources()
val web_imports = ui_dependency_direct_imports(sources, "app.ui.web.backend")
expect(ui_dependency_imports_module(web_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(web_imports, "app.ui.render.widgets")).to_equal(false)
val tauri_imports = ui_dependency_direct_imports(sources, "app.ui.tauri.backend")
expect(ui_dependency_imports_module(tauri_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(tauri_imports, "app.ui.render.widgets")).to_equal(false)
val electron_imports = ui_dependency_direct_imports(sources, "app.ui.electron.backend")
expect(ui_dependency_imports_module(electron_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(electron_imports, "app.ui.render.widgets")).to_equal(false)
val browser_imports = ui_dependency_direct_imports(sources, "app.ui.browser.backend")
expect(ui_dependency_imports_module(browser_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(browser_imports, "app.ui.render.widgets")).to_equal(false)
val vscode_imports = ui_dependency_direct_imports(sources, "app.ui.vscode.backend")
expect(ui_dependency_imports_module(vscode_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(vscode_imports, "app.ui.render.widgets")).to_equal(false)
val tui_web_imports = ui_dependency_direct_imports(sources, "app.ui.tui_web.backend")
expect(ui_dependency_imports_module(tui_web_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(tui_web_imports, "app.ui.render.widgets")).to_equal(false)
val none_imports = ui_dependency_direct_imports(sources, "app.ui.none.backend")
expect(ui_dependency_imports_module(none_imports, "app.ui.render.html_widgets")).to_equal(true)
expect(ui_dependency_imports_module(none_imports, "app.ui.render.widgets")).to_equal(false)
```

</details>

#### keeps HTML-capable adapters on shared web render contracts where applicable

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sources = real_html_adapter_sources()
expect(ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.web.backend"), "common.ui.web_render_api")).to_equal(true)
expect(ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.tauri.backend"), "common.ui.web_render_api")).to_equal(true)
expect(ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.electron.backend"), "common.ui.web_render_api")).to_equal(true)
expect(ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.browser.backend"), "common.ui.web_render_api")).to_equal(true)
expect(ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.tui_web.backend"), "common.ui.web_render_api")).to_equal(true)
expect(ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.none.backend"), "common.ui.web_render_api")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
