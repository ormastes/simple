# UI Renderer Capability Boundary

> Verifies that HTML renderer and CSS provider implementation modules are exposed through explicit renderer capabilities. The capability registry itself must not import implementation modules, so non-HTML and TUI closures can inspect the boundary without retaining HTML/CSS code.

<!-- sdn-diagram:id=render_capability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_capability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_capability_spec -> std
render_capability_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_capability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Renderer Capability Boundary

Verifies that HTML renderer and CSS provider implementation modules are exposed through explicit renderer capabilities. The capability registry itself must not import implementation modules, so non-HTML and TUI closures can inspect the boundary without retaining HTML/CSS code.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/01_unit/app/ui/render_capability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that HTML renderer and CSS provider implementation modules are exposed
through explicit renderer capabilities. The capability registry itself must not
import implementation modules, so non-HTML and TUI closures can inspect the
boundary without retaining HTML/CSS code.

## Examples

The HTML widget renderer declares `html_renderer`, CSS declares `css_provider`,
and both are lazy capabilities. TUI rendering declares `tui_renderer` as a
default-autoload capability because it is part of the base terminal lane.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-002, REQ-003, REQ-009, NFR-001, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### UI renderer capability boundary

#### keeps the capability registry free of implementation imports

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = capability_source("src/app/ui.render/capability.spl")
val imports = ui_dependency_extract_imports(source.source)
expect(ui_dependency_imports_module(imports, "app.ui.render.html_widgets")).to_equal(false)
expect(ui_dependency_imports_module(imports, "app.ui.render.css")).to_equal(false)
```

</details>

#### declares HTML widgets as a lazy renderer capability

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = html_widget_renderer_capability()
expect(cap.id).to_equal("html_renderer")
expect(cap.implementation_module).to_equal("app.ui.render.html_widgets")
expect(cap.artifact_id).to_equal("web_renderer")
expect(renderer_capability_is_lazy(cap)).to_equal(true)
expect(renderer_capability_allows_module(cap, "app.ui.render.html_widgets")).to_equal(true)
```

</details>

#### declares CSS provider as a lazy renderer capability

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = css_provider_capability()
expect(cap.id).to_equal("css_provider")
expect(cap.implementation_module).to_equal("app.ui.render.css")
expect(cap.artifact_id).to_equal("web_renderer")
expect(renderer_capability_is_lazy(cap)).to_equal(true)
expect(renderer_capability_allows_module(cap, "app.ui.render.css.theme")).to_equal(true)
```

</details>

#### keeps TUI renderer as the base default capability

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = renderer_capability_tui_widgets()
expect(cap.id).to_equal("tui_renderer")
expect(cap.implementation_module).to_equal("app.ui.render.tui_widgets")
expect(cap.artifact_id).to_equal("tui_renderer")
expect(cap.default_autoload).to_equal(true)
expect(renderer_capability_allows_module(cap, "app.ui.render.html_widgets")).to_equal(false)
```

</details>

#### selects CSS only for requested component styles

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(css_component_known("card")).to_equal(true)
expect(css_component_known("not-a-component")).to_equal(false)
val card_only = css_for_components(["card"])
expect(card_only).to_contain(".card")
expect(contains_text(card_only, "table {")).to_equal(false)
expect(contains_text(card_only, ".progress")).to_equal(false)
```

</details>

#### deduplicates component CSS selections and skips unknown components

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selected = css_for_components(["card", "unknown", "card", "progress"])
expect(selected).to_contain(".card")
expect(selected).to_contain(".progress")
expect(css_for_component("unknown")).to_equal("")
val once = css_for_components(["card"])
expect(selected.len()).to_equal(once.len() + css_for_component("progress").len())
```

</details>

#### keeps render adapters on component-scoped CSS selection

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(uses_css_selector_only(adapter_source("src/app/test/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/app/repl/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/app/search/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/app/sim/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/app/tree/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/app/terminal/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/app/jupyter_kernel/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/lib/nogc_async_mut/lsp/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/lib/gc_async_mut/lsp/render_adapter.spl"))).to_equal(true)
expect(uses_css_selector_only(adapter_source("src/lib/nogc_sync_mut/lsp/render_adapter.spl"))).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
