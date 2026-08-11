# Low Dependency UI dynSMF Parallel Work Orders

Date: 2026-06-05

## Coordination Contract

- Final requirements are selected: Feature Option C and NFR-A+B. These work
  orders now apply to the selected thin slice, not all former options.
- Each agent owns only the files listed in its work order unless a handoff
  explicitly grants another path.
- Agents must preserve unrelated dirty files, especially active thread and
  compiler Rust work outside this lane.
- Executable SPipe specs go under `test/`; generated/manual docs go under
  `doc/06_spec`; `doc/06_spec/**/*_spec.spl` must remain zero.

## Shared Inputs

- `.spipe/low-dependency-ui-dynsmf/state.md`
- `doc/01_research/local/low_dependency_ui_dynsmf.md`
- `doc/01_research/domain/low_dependency_ui_dynsmf.md`
- `doc/02_requirements/feature/low_dependency_ui_dynsmf.md`
- `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf.md`
- `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_loader_handoff.md`
- `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
- `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`

## Agent A: UI Dependency Boundary

Goal: produce the import-closure analyzer and dependency-boundary specs after
requirements are selected.

Primary paths:

- `src/app/ui*`
- `src/lib/common/ui/*`
- candidate tests under `test/01_unit/app/ui/` and
  `test/03_system/app/ui/feature/`

Do not edit:

- `src/os/**`
- dynSMF loader/session implementation files

Deliverables:

- exact-prefix `use` closure analyzer;
- allow/deny matrix for base TUI, common renderer, host web adapters, and
  HTML-capable widgets;
- failing specs first, then implementation;
- generated manuals from SPipe docgen after specs exist.

Acceptance evidence:

- base `app.ui.tui` closure has zero forbidden modules;
- common renderer no longer pulls HTML widgets without explicit capability;
- diagnostics show source module, forbidden dependency, and import path.

## Agent B: dynSMF Session Lifecycle

Goal: add or design the session-owned dynSMF handle layer.

Primary paths:

- `src/os/posix/dynlib.spl`
- `src/os/posix/dylib_async.spl`
- `src/os/kernel/loader/dylib_registry.spl`
- `src/os/smf/smf_dynlib.spl`
- candidate tests under `test/01_unit/os/smf/` and
  `test/03_system/stdlib/dynload/`

Do not edit:

- UI adapter imports or renderer internals

Deliverables:

- session handle and generation model;
- stale-handle diagnostics;
- unload/reload tests in interpreter mode;
- proof that existing registry refcount behavior still passes.

Acceptance evidence:

- load, symbol, unload, stale lookup failure, reload, fresh lookup success;
- stale raw handles are not silently reused inside a generation;
- tests can construct policy without process-global env mutation.

## Agent C: stdlib-like dynSMF Manifest And Policy

Goal: define manifest entries and startup policy for requested standard
library-like dynSMF libraries.

Primary paths:

- startup/build policy files selected during design;
- new manifest/policy modules under `src/lib` or `src/os/smf` after design;
- candidate tests under `test/02_integration/app/simple/`

Requested library ids:

- `file_io`
- `net_io`
- `render2d`
- `web_renderer`
- `gui_renderer`
- `tui_renderer`

Deliverables:

- manifest schema;
- default autoload policy;
- `--no-dynsmf`, `--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, and
  `SIMPLE_DYNSMF_DISABLE=<ids>` behavior;
- evidence row format.

Acceptance evidence:

- skip-all suppresses all default loads;
- per-id disable suppresses only named libraries;
- load evidence names library id, policy source, status, handle generation, and
  skip/unload reason.

## Agent D: HTML/CSS Component Loading

Goal: split HTML renderer and CSS implementation closure behind component or
adapter capabilities.

Primary paths:

- `src/app/ui.render/html_widgets.spl`
- `src/app/ui.render/widgets.spl`
- `src/app/ui.web/html.spl`
- `src/app/ui.browser/*`
- `src/app/ui.electron/*`
- `src/app/ui.tauri/*`
- `src/app/ui.vscode/*`
- `src/lib/common/ui/web_render_api.spl`

Do not edit:

- loader/session internals

Deliverables:

- adapter-by-adapter import migration table;
- capability API for HTML/CSS component loading;
- negative evidence that non-HTML widgets do not load HTML/CSS closures.

Acceptance evidence:

- host web adapters route through shared web-render contracts;
- only HTML-capable widgets load HTML renderer/CSS implementation;
- non-web/non-HTML lanes retain clean dependency closure.

## Agent E: Verification And Manuals

Goal: own SPipe quality, generated manuals, and release-blocking evidence.

Primary paths:

- `test/**/low_dependency_ui_dynsmf*_spec.spl`
- `doc/06_spec/**/low_dependency_ui_dynsmf*_spec.md`
- `doc/03_plan/sys_test/low_dependency_ui_dynsmf*.md`
- relevant guide/architecture docs after implementation changes

Deliverables:

- SPipe specs with real assertions only;
- generated/manual scenario docs usable without source test files;
- verification report with pass/fail evidence;
- doc layout guard result.

Acceptance evidence:

- no placeholder specs;
- no executable specs under `doc/06_spec`;
- requirements trace to specs and implementation after final requirements exist.

## Merge Sequencing

1. User selects feature and NFR options.
2. Agent E turns selected requirements into trace IDs and spec skeleton names.
3. Agents A and B write failing tests in parallel.
4. Agent C starts after Agent B freezes the session handle contract.
5. Agent D starts after Agent A freezes the import allow/deny matrix.
6. Agents A-D implement against their specs.
7. Agent E regenerates manuals, runs verification gates, and updates tracking.

## Conflict Rules

- If Agent A and D both need `src/app/ui.render/widgets.spl`, Agent A owns the
  dependency gate and Agent D owns the implementation split; merge through a
  short shared patch plan before editing.
- If Agent B and C both need startup policy, Agent B owns lifecycle semantics
  and Agent C owns manifest/policy parsing.
- Any change to `doc/04_architecture/ui/simple_gui_stack.md` must be coordinated
  with Agent E because SPipe guidance requires stack architecture freshness for
  UI/render work.

## Required Handoff Commands

Each agent reports:

- `git status --short -- <owned paths>`
- focused spec/check commands run;
- `find doc/06_spec -name '*_spec.spl' | wc -l`
- unresolved blockers or files intentionally left untouched.
