# Low Dependency UI dynSMF Dependency Gate — System Test Plan

## Scope

- exact-prefix import closure checks for UI lanes;
- base TUI proof that it does not import GUI, web, TUI-web, browser, HTML
  renderer, or CSS implementation modules;
- common renderer proof that generic widgets do not force HTML widget closure;
- adapter proof that web-capable lanes route through shared web-render contracts;
- generated manual evidence for dependency policy and failure diagnostics.

## Execution

Candidate executable specs after requirement selection:

- `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`
- `test/01_unit/app/ui/dependency_closure_gate_spec.spl`

Candidate generated manuals:

- `doc/06_spec/test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md`
- `doc/06_spec/test/01_unit/app/ui/dependency_closure_gate_spec.md`

## Pass Criteria

- Specs use real assertions and built-in matchers only.
- Import closure matching is exact-prefix, so `app.ui.tui` does not accidentally
  match `app.ui.tui_web`.
- Base `app.ui.tui` closure contains zero forbidden implementation modules:
  `app.ui.web`, `app.ui.tui_web`, `app.ui.browser`, HTML widgets, CSS
  implementation modules, and GUI implementation modules.
- Common `app.ui.render` does not pull `app.ui.render.html_widgets` unless an
  explicit selected requirement allows a widget capability boundary there.
- Host web adapters may use HTML/CSS implementation only behind
  `common.ui.web_render_api` or a selected widget capability.
- HTML-capable adapters import `app.ui.render.html_widgets` directly and do not
  route through the legacy `app.ui.render.widgets` compatibility shim.
- Web, Tauri, Electron, browser, TUI-web, and headless web-render adapters keep
  direct imports of `common.ui.web_render_api` for shared render contracts.
- HTML and CSS implementations declare explicit lazy renderer capabilities
  through `app.ui.render.capability`; the capability registry itself must not
  import HTML widget or CSS implementation modules.
- Render adapters compose CSS through `css_for_components([...])` so each
  adapter names the exact component style payload it needs.
- Failure diagnostics name the source module, forbidden dependency, and import
  path.
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Candidate Traceability

| Candidate | Description | Executable Spec | Generated Spec | Coverage |
|-----------|-------------|-----------------|----------------|----------|
| AC-3 | TUI depends only on common UI/TUI renderer code | `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`; `test/01_unit/app/ui/dependency_closure_gate_spec.spl` | `doc/06_spec/test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md`; `doc/06_spec/test/01_unit/app/ui/dependency_closure_gate_spec.md` | Covered |
| AC-4 | Host adapters consume shared web-render contracts | `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`; `test/01_unit/app/ui/dependency_closure_gate_spec.spl` | `doc/06_spec/test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md`; `doc/06_spec/test/01_unit/app/ui/dependency_closure_gate_spec.md` | Covered |
| AC-5 | HTML/CSS implementation loads only where needed | `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`; `test/01_unit/app/ui/render_capability_spec.spl`; `test/01_unit/app/ui/dependency_closure_gate_spec.spl` | `doc/06_spec/test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md`; `doc/06_spec/test/01_unit/app/ui/render_capability_spec.md`; `doc/06_spec/test/01_unit/app/ui/dependency_closure_gate_spec.md` | Covered |
| NFR-A | Static dependency gate | `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`; `test/01_unit/app/ui/dependency_closure_gate_spec.spl` | `doc/06_spec/test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md`; `doc/06_spec/test/01_unit/app/ui/dependency_closure_gate_spec.md` | Covered |

## Current Baseline

Corrected local scan on 2026-06-05:

- `app.ui.tui`: 93 closure modules; zero forbidden web/TUI-web/HTML/browser/CSS/GUI modules.
- `app.ui.render`: 34 closure modules; currently includes
  no `app.ui.render.html_widgets` module through the compatibility shim.
- `app.ui.web`, `app.ui.tauri`, `app.ui.electron`, `app.ui.browser`,
  `app.ui.vscode`, `app.ui.tui_web`, and `app.ui.none` directly import
  `app.ui.render.html_widgets` instead of `app.ui.render.widgets`.
- Web-render adapters keep shared contract imports through
  `common.ui.web_render_api` where applicable.
- `app.ui.render.capability` names the `html_renderer`, `css_provider`, and
  `tui_renderer` capability boundaries without importing the implementation
  modules.
- Test/repl/search/sim/tree/terminal/Jupyter/LSP render adapters now use
  component-scoped CSS selection instead of direct CSS function concatenation.

## Implementation Notes

- The analyzer should parse Simple `use` statements and resolve module prefixes
  using the repo source layout.
- The gate should ignore vendored paths listed in `AGENTS.md`.
- Diagnostics must be deterministic so generated manuals can show the exact
  failing import path.
