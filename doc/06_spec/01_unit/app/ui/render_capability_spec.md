# UI Renderer Capability Boundary

> Verifies that HTML renderer and CSS provider implementation modules are exposed through explicit renderer capabilities. The capability registry itself must not use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Renderer Capability Boundary

Verifies that HTML renderer and CSS provider implementation modules are exposed through explicit renderer capabilities. The capability registry itself must not use std.spec.step

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that HTML renderer and CSS provider implementation modules are exposed
through explicit renderer capabilities. The capability registry itself must not
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the capability registry free of implementation imports
   - Expected: ui_dependency_imports_module(imports, "app.ui.render.html_widgets") is false
   - Expected: ui_dependency_imports_module(imports, "app.ui.render.css") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the capability registry free of implementation imports")
val source = capability_source("src/app/ui.render/capability.spl")
val imports = ui_dependency_extract_imports(source.source)
expect(ui_dependency_imports_module(imports, "app.ui.render.html_widgets")).to_equal(false)
expect(ui_dependency_imports_module(imports, "app.ui.render.css")).to_equal(false)
```

</details>

#### declares HTML widgets as a lazy renderer capability

- declares HTML widgets as a lazy renderer capability
   - Expected: cap.id equals `html_renderer`
   - Expected: cap.implementation_module equals `app.ui.render.html_widgets`
   - Expected: cap.artifact_id equals `web_renderer`
   - Expected: renderer_capability_is_lazy(cap) is true
   - Expected: renderer_capability_allows_module(cap, "app.ui.render.html_widgets") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HTML widgets as a lazy renderer capability")
val cap = html_widget_renderer_capability()
expect(cap.id).to_equal("html_renderer")
expect(cap.implementation_module).to_equal("app.ui.render.html_widgets")
expect(cap.artifact_id).to_equal("web_renderer")
expect(renderer_capability_is_lazy(cap)).to_equal(true)
expect(renderer_capability_allows_module(cap, "app.ui.render.html_widgets")).to_equal(true)
```

</details>

#### declares CSS provider as a lazy renderer capability

- declares CSS provider as a lazy renderer capability
   - Expected: cap.id equals `css_provider`
   - Expected: cap.implementation_module equals `app.ui.render.css`
   - Expected: cap.artifact_id equals `web_renderer`
   - Expected: renderer_capability_is_lazy(cap) is true
   - Expected: renderer_capability_allows_module(cap, "app.ui.render.css.theme") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares CSS provider as a lazy renderer capability")
val cap = css_provider_capability()
expect(cap.id).to_equal("css_provider")
expect(cap.implementation_module).to_equal("app.ui.render.css")
expect(cap.artifact_id).to_equal("web_renderer")
expect(renderer_capability_is_lazy(cap)).to_equal(true)
expect(renderer_capability_allows_module(cap, "app.ui.render.css.theme")).to_equal(true)
```

</details>

#### keeps TUI renderer as the base default capability

- keeps TUI renderer as the base default capability
   - Expected: cap.id equals `tui_renderer`
   - Expected: cap.implementation_module equals `app.ui.render.tui_widgets`
   - Expected: cap.artifact_id equals `tui_renderer`
   - Expected: cap.default_autoload is true
   - Expected: renderer_capability_allows_module(cap, "app.ui.render.html_widgets") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps TUI renderer as the base default capability")
val cap = renderer_capability_tui_widgets()
expect(cap.id).to_equal("tui_renderer")
expect(cap.implementation_module).to_equal("app.ui.render.tui_widgets")
expect(cap.artifact_id).to_equal("tui_renderer")
expect(cap.default_autoload).to_equal(true)
expect(renderer_capability_allows_module(cap, "app.ui.render.html_widgets")).to_equal(false)
```

</details>

#### selects CSS only for requested component styles

- selects CSS only for requested component styles
   - Expected: css_component_known("card") is true
   - Expected: css_component_known("not-a-component") is false
   - Expected: contains_text(card_only, "table {") is false
   - Expected: contains_text(card_only, ".progress") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects CSS only for requested component styles")
expect(css_component_known("card")).to_equal(true)
expect(css_component_known("not-a-component")).to_equal(false)
val card_only = css_for_components(["card"])
expect(card_only).to_contain(".card")
expect(contains_text(card_only, "table {")).to_equal(false)
expect(contains_text(card_only, ".progress")).to_equal(false)
```

</details>

#### deduplicates component CSS selections and skips unknown components

- deduplicates component CSS selections and skips unknown components
   - Expected: css_for_component("unknown") equals ``
   - Expected: selected.len() equals `once.len() + css_for_component("progress").len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deduplicates component CSS selections and skips unknown components")
val selected = css_for_components(["card", "unknown", "card", "progress"])
expect(selected).to_contain(".card")
expect(selected).to_contain(".progress")
expect(css_for_component("unknown")).to_equal("")
val once = css_for_components(["card"])
expect(selected.len()).to_equal(once.len() + css_for_component("progress").len())
```

</details>

#### keeps render adapters on component-scoped CSS selection

- keeps render adapters on component-scoped CSS selection
   - Expected: uses_css_selector_only(adapter_source("src/app/test/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/app/repl/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/app/search/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/app/sim/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/app/tree/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/app/terminal/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/app/jupyter_kernel/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/lib/nogc_async_mut/lsp/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/lib/gc_async_mut/lsp/render_adapter.spl")) is true
   - Expected: uses_css_selector_only(adapter_source("src/lib/nogc_sync_mut/lsp/render_adapter.spl")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps render adapters on component-scoped CSS selection")
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

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-002`
- `REQ-003`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `10d56e8c16ed809d6d5b50e957539f3105fc12373909742b7b916914d6c1e694`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10d56e8c16ed809d6d5b50e957539f3105fc12373909742b7b916914d6c1e694`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10d56e8c16ed809d6d5b50e957539f3105fc12373909742b7b916914d6c1e694`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ui/render_capability_spec.spl
mirror: doc/06_spec/01_unit/app/ui/render_capability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/render_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/render_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/render_capability_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the capability registry free of implementation imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/render_capability_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares HTML widgets as a lazy renderer capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/render_capability_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares CSS provider as a lazy renderer capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
