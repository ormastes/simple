# Low Dependency UI dynSMF Dependency Gate System Specification

> Verifies the selected low_dependency_ui_dynsmf UI dependency boundary at the feature level. The system spec reads production adapter source files and checks that base TUI stays out of web/HTML/CSS implementation modules while HTML-capable adapters depend on explicit HTML widget and shared web-render contracts.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps exact-prefix TUI closure out of web HTML browser and CSS modules
   - Expected: ui_dependency_module_matches("app.ui.tui_web.backend", "app.ui.tui") is false
   - Expected: report.violation_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps exact-prefix TUI closure out of web HTML browser and CSS modules")
expect(ui_dependency_module_matches("app.ui.tui_web.backend", "app.ui.tui")).to_equal(false)
val report = ui_dependency_report(feature_tui_sources(), feature_tui_policy("app.ui.tui.backend"))
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps the shared widget compatibility shim out of HTML and CSS implementation

- keeps the shared widget compatibility shim out of HTML and CSS implementation
   - Expected: report.violation_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the shared widget compatibility shim out of HTML and CSS implementation")
val report = ui_dependency_report(feature_tui_sources(), feature_tui_policy("app.ui.render.widgets"))
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps HTML-capable adapters on explicit HTML widgets and shared web-render contracts

- keeps HTML-capable adapters on explicit HTML widgets and shared web-render contracts
   - Expected: ui_dependency_imports_module(web_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(web_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(web_imports, "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(tauri_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(tauri_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(tauri_imports, "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(electron_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(electron_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(electron_imports, "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(browser_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(browser_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(browser_imports, "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(tui_web_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(tui_web_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(tui_web_imports, "common.ui.web_render_api") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps HTML-capable adapters on explicit HTML widgets and shared web-render contracts")
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

- keeps HTML and CSS implementation behind explicit lazy renderer capabilities
   - Expected: html_cap.implementation_module equals `app.ui.render.html_widgets`
   - Expected: css_cap.implementation_module equals `app.ui.render.css`
   - Expected: renderer_capability_is_lazy(html_cap) is true
   - Expected: renderer_capability_is_lazy(css_cap) is true
   - Expected: tui_cap.default_autoload is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps HTML and CSS implementation behind explicit lazy renderer capabilities")
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

- selects CSS payload only for requested component styles
   - Expected: feature_contains_text(card_only, "table {") is false
   - Expected: feature_contains_text(card_only, ".progress") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects CSS payload only for requested component styles")
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

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8aa9d932be510c3399580692aea8ddc0577723225e35251e16f841d52cc9aa7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8aa9d932be510c3399580692aea8ddc0577723225e35251e16f841d52cc9aa7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8aa9d932be510c3399580692aea8ddc0577723225e35251e16f841d52cc9aa7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl
mirror: doc/06_spec/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps exact-prefix TUI closure out of web HTML browser and CSS modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the shared widget compatibility shim out of HTML and CSS implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps HTML-capable adapters on explicit HTML widgets and shared web-render contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
