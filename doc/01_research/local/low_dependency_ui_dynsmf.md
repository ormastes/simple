# Low Dependency UI dynSMF Local Research

Date: 2026-06-05

## Scope

This research covers the current Simple UI dependency shape and existing SMF
dynlib support relevant to the requested refactor.

## Existing UI Dependency Shape

Observed dependency hot spots:

- `app.ui.web` appears in 27 files, including `src/app/ui.web/backend.spl`,
  server/session modules, and bridge modules.
- `app.ui.render.html_widgets` appears in 11 files, including web, browser,
  Electron, Tauri, VSCode, TUI-web, and `ui.none` adapters.
- `app.ui.web.html` appears in 10 files, including web servers and host web
  adapters.
- `app.ui.browser` appears in 5 files.
- `app.ui.tui` appears in 17 files.

Potential boundary issues found by local scan:

- `src/app/ui.tui/backend.spl` and `src/app/ui.tui/app.spl` mention HTML/CSS/web
  terms. The backend already documents that standalone TUI lanes avoid the HTML
  renderer closure, but the boundary needs executable proof.
- `src/app/ui.vscode/backend.spl` imports HTML widget/CSS helpers directly.
- `src/app/ui.browser/renderer.spl` and `src/app/ui.browser/dom_bridge.spl`
  consume `std.common.render_scene.css_types`; this is likely acceptable only if
  the CSS type contract is separated from CSS implementation.

## Existing Shared Renderer Work

Relevant prior requirements:

- `doc/02_requirements/ui/misc/shared_wm_renderer_unification.md` requires one
  Simple-owned web render API used by `ui.web`, `ui.electron`, `ui.tauri`, and
  the pure Simple browser path.
- `doc/04_architecture/ui/simple_gui_stack.md` is the canonical GUI stack doc
  for UI, GUI, MDI/window-manager, Draw IR, Simple 2D, and backend-lane changes.
- `src/lib/common/ui/draw_ir.spl` and
  `src/lib/common/ui/window_scene_draw_ir.spl` are named canonical shared UI
  contracts in the SPipe guidance.

## Existing dynlib Support

Local dynlib files already exist:

- `src/os/posix/dynlib.spl`: OOP dynlib facade; includes close/unload and SMF
  awareness.
- `src/os/posix/dylib_async.spl`: async dynamic library pipeline; includes
  close/unload and SMF awareness.
- `src/os/kernel/loader/dylib_registry.spl`: registry path; includes close and
  SMF support.
- `src/app/gui_perf/smf_dynlib_probe_core.spl`: GUI SMF dynlib probe support.
- `src/os/smf/smf_dynlib.spl`: standalone SMF `dlopen`/`dlsym`/`dlclose`
  primitives.

Relevant tests and manuals already exist:

- `test/01_unit/os/posix/dynlib_spec.spl`
- `test/03_system/stdlib/dynload/dynload_simpleos_smf_system_spec.spl`
- `test/03_system/gui/linux_smf_dynlib_e2e_gate_system_spec.spl`
- `test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl`
- `doc/06_spec/unit/os/posix/dynlib_spec.md`
- `doc/06_spec/system/gui/linux_smf_dynlib_e2e_gate_system_spec.md`

More detailed loader/session handoff:

- `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_loader_handoff.md`

## Gaps

- There is no combined requirements/design artifact for low-dependency UI plus
  stdlib-like precompiled dynSMF loading.
- Existing dynlib support proves artifact/probe scenarios, but this feature
  needs session-scoped unload/reload semantics usable by interpreter-mode tests.
- Existing UI adapters share HTML renderer helpers directly in several places;
  selected requirements should define which imports are contracts and which are
  implementation closures.
- There is no current proof that TUI avoids GUI/web/HTML/CSS implementation
  dependency closure.
- No existing stdlib-like dynSMF autoload manifest was found for `file_io`,
  `net_io`, `render2d`, `web_renderer`, `gui_renderer`, or `tui_renderer`.

## Corrected Import Closure Snapshot

The import closure scan must use exact module-prefix matching. A naive
`app.ui.tui*` prefix incorrectly includes `app.ui.tui_web`.

Corrected snapshot:

- Base `app.ui.tui`: 93 closure modules; `app.ui.web=0`,
  `app.ui.tui_web=0`, `app.ui.render.html=0`, `app.ui.browser=0`,
  `css_impl_terms=0`, `gui_terms=0`. This supports the user's TUI boundary
  goal, but it still needs an executable regression gate.
- `app.ui.tui_web`: 120 closure modules; pulls 14 `app.ui.web` modules and one
  HTML widget module. This is acceptable only as the explicit TUI-to-web adapter
  lane.
- `app.ui.render`: 34 closure modules; pulls one HTML widget module through
  `app.ui.render.widgets -> app.ui.render.html_widgets`. This is the main common
  renderer boundary to split or capability-gate.
- `app.ui.vscode`: 10 closure modules; directly imports
  `app.ui.render.html_widgets` and `app.ui.web.html`.
- `app.ui.electron` and `app.ui.tauri`: each pull web/HTML modules through their
  adapters. This likely belongs behind the web-render adapter contract, not in
  shared base UI.

Current UI app directories include `ui`, `ui.browser`, `ui.chromium`,
`ui.electron`, `ui.none`, `ui.render`, `ui.standalone`, `ui.tauri`, `ui.tui`,
`ui.tui_web`, `ui.vscode`, `ui.web`, and `ui_shared_mdi`. There is no
`src/app/ui.gui` directory in this checkout; GUI behavior appears split across
common UI contracts, host adapters, renderer modules, and GUI/perf apps.

## Candidate Implementation Areas

- Shared contracts: `src/lib/common/ui/`
- Web-render API: `src/lib/common/ui/web_render_api.spl`
- UI adapters: `src/app/ui.*`
- Dynlib facade: `src/os/posix/dynlib.spl`
- Loader registry: `src/os/kernel/loader/dylib_registry.spl`
- DynSMF stdlib manifest/startup policy: likely app startup/build modules under
  `src/app/build`, `src/app/cli`, and loader/startup docs.
