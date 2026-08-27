# Low Dependency UI Dependency Closure Gate

> Verifies exact-prefix UI dependency closure policy for the selected low_dependency_ui_dynsmf thin slice. The gate walks only reachable imports from the selected root and reports forbidden backend implementation dependencies.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not treat app.ui.tui_web as part of app.ui.tui
   - Expected: ui_dependency_module_matches("app.ui.tui_web", "app.ui.tui") is false
   - Expected: ui_dependency_module_matches("app.ui.tui.screen", "app.ui.tui") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not treat app.ui.tui_web as part of app.ui.tui")
expect(ui_dependency_module_matches("app.ui.tui_web", "app.ui.tui")).to_equal(false)
expect(ui_dependency_module_matches("app.ui.tui.screen", "app.ui.tui")).to_equal(true)
```

</details>

#### extracts structured use imports without imported symbol braces

- extracts structured use imports without imported symbol braces
   - Expected: imports[0] equals `app.ui.render.html_widgets`
   - Expected: imports[1] equals `app.ui.web.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts structured use imports without imported symbol braces")
val imports = ui_dependency_extract_imports("use app.ui.render.html_widgets." + "{" + "render_html_tree" + "}\nuse app.ui.web.html\n")
expect(imports[0]).to_equal("app.ui.render.html_widgets")
expect(imports[1]).to_equal("app.ui.web.html")
```

</details>

#### keeps the base TUI fixture free of forbidden web and HTML modules

- keeps the base TUI fixture free of forbidden web and HTML modules
   - Expected: report.module_count equals `4`
   - Expected: report.violation_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the base TUI fixture free of forbidden web and HTML modules")
val report = ui_dependency_report(clean_tui_fixture(), tui_policy("app.ui.tui"))
expect(report.module_count).to_equal(4)
expect(report.violation_count).to_equal(0)
```

</details>

#### detects when common renderer widgets pull HTML implementation

- detects when common renderer widgets pull HTML implementation
   - Expected: report.module_count equals `3`
   - Expected: report.violation_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects when common renderer widgets pull HTML implementation")
val report = ui_dependency_report(html_leak_fixture(), tui_policy("app.ui.render"))
expect(report.module_count).to_equal(3)
expect(report.violation_count).to_equal(1)
```

</details>

#### counts unresolved forbidden imports as dependency violations

- counts unresolved forbidden imports as dependency violations
   - Expected: report.violation_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts unresolved forbidden imports as dependency violations")
val report = ui_dependency_report(unresolved_html_leak_fixture(), tui_policy("app.ui.tui.backend"))
expect(report.violation_count).to_equal(1)
```

</details>

#### keeps the current app.ui.tui.backend source closure out of web HTML CSS and browser modules

- keeps the current app.ui.tui.backend source closure out of web HTML CSS and browser modules
   - Expected: report.module_count equals `13`
   - Expected: report.violation_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the current app.ui.tui.backend source closure out of web HTML CSS and browser modules")
val report = ui_dependency_report(real_tui_backend_sources(), tui_policy("app.ui.tui.backend"))
expect(report.module_count).to_equal(13)
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps the current app.ui.render.widgets shim free of HTML and CSS implementation imports

- keeps the current app.ui.render.widgets shim free of HTML and CSS implementation imports
   - Expected: report.module_count equals `12`
   - Expected: report.violation_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the current app.ui.render.widgets shim free of HTML and CSS implementation imports")
val report = ui_dependency_report(real_tui_backend_sources(), tui_policy("app.ui.render.widgets"))
expect(report.module_count).to_equal(12)
expect(report.violation_count).to_equal(0)
```

</details>

#### keeps HTML-capable adapters on direct html_widgets imports instead of the shared widgets shim

- keeps HTML-capable adapters on direct html_widgets imports instead of the shared widgets shim
   - Expected: ui_dependency_imports_module(web_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(web_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(tauri_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(tauri_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(electron_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(electron_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(browser_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(browser_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(vscode_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(vscode_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(tui_web_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(tui_web_imports, "app.ui.render.widgets") is false
   - Expected: ui_dependency_imports_module(none_imports, "app.ui.render.html_widgets") is true
   - Expected: ui_dependency_imports_module(none_imports, "app.ui.render.widgets") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps HTML-capable adapters on direct html_widgets imports instead of the shared widgets shim")
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

- keeps HTML-capable adapters on shared web render contracts where applicable
   - Expected: ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.web.backend"), "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.tauri.backend"), "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.electron.backend"), "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.browser.backend"), "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.tui_web.backend"), "common.ui.web_render_api") is true
   - Expected: ui_dependency_imports_module(ui_dependency_direct_imports(sources, "app.ui.none.backend"), "common.ui.web_render_api") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps HTML-capable adapters on shared web render contracts where applicable")
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

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-001`
- `REQ-002`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61d49a50bdc28b23eac53e2348138b7bab469130a4671de93c37f43a51e2924e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61d49a50bdc28b23eac53e2348138b7bab469130a4671de93c37f43a51e2924e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61d49a50bdc28b23eac53e2348138b7bab469130a4671de93c37f43a51e2924e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/ui/dependency_closure_gate_spec.spl
mirror: doc/06_spec/01_unit/app/ui/dependency_closure_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/dependency_closure_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/dependency_closure_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/dependency_closure_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/dependency_closure_gate_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat app.ui.tui_web as part of app.ui.tui' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/dependency_closure_gate_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts structured use imports without imported symbol braces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/dependency_closure_gate_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the base TUI fixture free of forbidden web and HTML modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
