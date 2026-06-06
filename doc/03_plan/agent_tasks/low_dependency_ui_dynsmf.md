# Low Dependency UI dynSMF Parallel Agent Plan

Date: 2026-06-05

## Coordination Rules

- Owned lane: `.spipe/low-dependency-ui-dynsmf`, `doc/01_research/*/low_dependency_ui_dynsmf.md`,
  `doc/02_requirements/*/low_dependency_ui_dynsmf*`, and future matching
  architecture/design/spec files.
- Preserve unrelated dirty files in thread-enhancement and compiler Rust lanes.
- No final requirements until the user selects feature and NFR options.
- No executable `.spl` specs under `doc/06_spec`.

## Parallel Agents

### Agent A: UI Dependency Boundary

Inputs:

- `doc/01_research/local/low_dependency_ui_dynsmf.md`
- `src/app/ui.tui`, `src/app/ui.gui`, `src/app/ui.render`, `src/app/ui.web`,
  `src/app/ui.browser`, `src/app/ui.electron`, `src/app/ui.tauri`,
  `src/app/ui.vscode`

Outputs:

- Static dependency closure report.
- Proposed allowed/forbidden import matrix.
- Boundary specs proving TUI and base GUI do not import HTML/CSS/web
  implementation closures.
- First target: preserve the corrected `app.ui.tui` closure baseline of zero
  web/TUI-web/HTML/browser/CSS/GUI implementation modules.
- Second target: split or capability-gate
  `app.ui.render.widgets -> app.ui.render.html_widgets` so common renderer
  widgets do not force HTML renderer closure.

Conflict boundary:

- Does not edit dynlib loader internals.

### Agent B: dynSMF Loader and Session Unload

Inputs:

- `src/os/posix/dynlib.spl`
- `src/os/posix/dylib_async.spl`
- `src/os/kernel/loader/dylib_registry.spl`
- existing dynlib specs under `test/01_unit/os/posix` and
  `test/03_system/stdlib/dynload`

Outputs:

- Session-scoped dynSMF handle API design.
- Interpreter-mode unload/reload specs.
- Error contract for stale handles after unload.
- Loader handoff reference:
  `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_loader_handoff.md`

Conflict boundary:

- Does not move UI adapter imports.

### Agent C: stdlib-like dynSMF Manifests

Inputs:

- build/startup docs and `src/app/build`, `src/app/cli`
- selected library list: file IO, net IO, 2D renderer, web renderer, GUI
  renderer, TUI renderer

Outputs:

- dynSMF manifest schema and default autoload policy.
- CLI/env opt-out matrix for all libraries and per-library disable.
- Build integration plan for precompiled artifacts.
- Provisional control names from the loader handoff:
  `--no-dynsmf`, `--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, and
  `SIMPLE_DYNSMF_DISABLE=<ids>`.

Conflict boundary:

- Does not implement renderer internals.

### Agent D: HTML/CSS Component Loading

Inputs:

- `src/app/ui.render/html_widgets*`
- `src/app/ui.web/html.spl`
- `src/app/ui.browser/dom_bridge.spl`
- `src/lib/common/ui/web_render_api.spl`

Outputs:

- Widget capability map for HTML renderer and CSS provider use.
- Lazy component loading plan for HTML/CSS implementation modules.
- Negative tests showing non-HTML widgets do not load CSS/HTML dynSMF modules.
- Adapter migration notes for `ui.vscode`, `ui.electron`, `ui.tauri`,
  `ui.tui_web`, and `ui.browser` so each consumes `common.ui.web_render_api`
  rather than direct HTML/CSS implementation imports where possible.

Conflict boundary:

- Does not change base TUI behavior except through shared contracts.

### Agent E: Verification and Evidence

Inputs:

- outputs from Agents A-D
- `doc/04_architecture/ui/simple_gui_stack.md`
- SPipe docgen guidance

Outputs:

- SPipe system/unit spec matrix.
- Generated `doc/06_spec` manuals after specs exist.
- Verification checklist including layout guard:
  `find doc/06_spec -name '*_spec.spl' | wc -l`.

Conflict boundary:

- Does not write production implementation except small test helpers.

## Sequencing

1. User selects feature and NFR options.
2. Agents A and B run in parallel.
3. Agent C starts after B defines the session handle contract.
4. Agent D starts after A defines the allowed UI import matrix.
5. Agent E writes specs once A-D outputs stabilize.
6. Implementation proceeds as a thin vertical slice or full migration depending
   on selected requirements.

## First Recommended Work Slice

Use Option C plus NFR-A/NFR-B:

- TUI proves no GUI/HTML/CSS implementation dependency.
- One GUI widget loads an HTML renderer component and CSS provider only when
  needed.
- One dynSMF library loads by default, can be skipped by arg/env, unloads from a
  session, and reloads in interpreter mode.

## Import Boundary Matrix

| Lane | Allowed imports | Forbidden base imports | Current evidence |
|------|-----------------|------------------------|------------------|
| `app.ui.tui` | `std.common.ui`, `app.ui.render` TUI/core modules, terminal screen modules | `app.ui.web`, `app.ui.tui_web`, `app.ui.browser`, HTML widgets, CSS impl, GUI impl | Corrected closure currently has zero forbidden modules |
| `app.ui.render` common | renderer core/types/layout/ANSI/table/progress plus declared widget capabilities | direct HTML renderer implementation from generic widgets | Currently `widgets -> html_widgets` |
| host web adapters | `common.ui.web_render_api`, adapter-local bridge code | imports that bypass the shared web-render API from non-widget base code | Electron/Tauri/VSCode currently import HTML helpers directly |
| HTML-capable widget | `html_widgets`, CSS provider, web render API | global/base loading of CSS/HTML closure | Needs capability gate and runtime evidence |
| dynSMF startup | manifest metadata, selected library handles | unconditional load when arg/env disables all or named lib | Needs implementation and tests |

## Agent Handoff Packets

- Agent A should produce `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
  and the initial SPipe dependency-boundary spec path proposal.
- Agent B should produce the dynSMF session-handle API sketch and stale-handle
  behavior table before implementation.
- Agent C should define manifest keys for `file_io`, `net_io`, `render2d`,
  `web_renderer`, `gui_renderer`, and `tui_renderer`.
- Agent D should produce an adapter-by-adapter migration table with direct
  import removals and allowed replacement APIs.
- Agent E should own docgen/readback quality and must keep
  `doc/06_spec/**/*_spec.spl` count at zero.

Completed option-independent handoff plans:

- `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
- `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`
- `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_parallel_work_orders.md`
- `doc/04_architecture/ui/low_dependency_ui_dynsmf.md`
- `doc/05_design/low_dependency_ui_dynsmf.md`
- `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_selection_audit.md`
