# Low Dependency UI dynSMF Architecture

Date: 2026-06-05

## Selection

Selected architecture: thin vertical slice using common UI contracts, explicit
HTML/CSS renderer capabilities, and a session-owned dynSMF runtime.

Default dynSMF libraries: `file_io`, `net_io`, `render2d`, `web_renderer`,
`gui_renderer`, and `tui_renderer`.

## Stable Constraints

- Base TUI must depend on common UI/TUI renderer contracts only.
- HTML renderer and CSS implementation must load only for capable widgets or
  adapters.
- The stdlib-like `file_io`, `net_io`, `render2d`, `web_renderer`,
  `gui_renderer`, and `tui_renderer` ids must use one dynSMF
  manifest/session pattern.
- dynSMF session behavior must support default load, skip-all, per-id skip,
  unload, stale-handle diagnostics, and reload.

## Architecture Shape

```sdn
low_dependency_ui_dynsmf {
  common_ui_contracts -> tui_base
  common_ui_contracts -> renderer_capability_registry
  renderer_capability_registry -> html_renderer_capability
  renderer_capability_registry -> css_provider_capability
  app_startup -> dynsmf_policy
  dynsmf_manifest_registry -> dynsmf_session
  dynsmf_session -> stdlib_like_dynsmf
  verifier -> dependency_gate_evidence
  verifier -> dynsmf_session_evidence
}
```

## Layers

### Common UI Contracts

`src/lib/common/ui` remains the contract layer. Base TUI may depend on common UI
types and TUI renderer contracts, but not GUI/web/HTML/CSS implementations.

### Renderer Capabilities

HTML renderer and CSS provider are explicit capabilities. Generic renderer
widgets do not import the HTML implementation directly; HTML-capable widgets or
host web adapters request the capability. The current verified slice keeps
`app.ui.render.widgets` as a TUI-only compatibility wrapper; HTML callers import
`app.ui.render.html_widgets` directly. The dependency gate reads the real
HTML-capable adapter source files and requires direct `html_widgets` imports
instead of the shared widget shim, plus shared `common.ui.web_render_api`
imports for adapters that render through the common web contract.

`src/app/ui.render/capability.spl` is the capability registry for renderer
implementation modules. It declares the `html_renderer`, `css_provider`, and
`tui_renderer` boundaries without importing HTML or CSS implementations.
`html_widgets.spl` and `css.spl` declare their own lazy capabilities, while TUI
renderer capability remains default-autoload for the base terminal lane.
`css.spl` also exposes `css_for_components([...])`; render adapters use that
selector to name their component style payloads instead of pulling an opaque
bundle.

### dynSMF Manifest Registry

The manifest registry declares stable ids for precompiled SMF artifacts:

- `file_io`
- `net_io`
- `render2d`
- `web_renderer`
- `gui_renderer`
- `tui_renderer`
- `ui_html`

All seven entries carry `precompiled_smf` artifact metadata, a source module, an
SMF artifact path, ABI version, exports, default-autoload policy, and a
deterministic `bin/simple compile <source> -o build/dynsmf/<id>.smf` build
plan. The runtime artifact gate reads each enabled artifact, requires the
`SMF\0` magic prefix, and fails missing, short, or invalid artifacts before
calling the lower checked SMF dynlib open path.

### dynSMF Session

The session owns library handles and generation counters. It applies policy
from args/env or test-provided policy structs, records evidence, and routes
symbols to the lower dynlib facade (`smf_dlopen_checked` for checked loads,
`smf_dlopen` for compatibility loads, plus `smf_dlsym` and `smf_dlclose`).
Evidence rows are persisted for load, skip, symbol lookup, stale lookup,
unload, and reload actions so interpreter-mode tests can inspect the full
session lifecycle without relying on process-global state.
Startup and system-boundary paths use the checked autoload variant; unit tests
also keep a pure byte-level validator so invalid-artifact handling is covered
without requiring filesystem fixtures.

## Policy

Supported controls:

- `--no-dynsmf`
- `--disable-dynsmf=<ids>`
- `SIMPLE_DYNSMF=0`
- `SIMPLE_DYNSMF_DISABLE=<ids>`

Tests must be able to construct the policy directly without mutating
process-global environment variables.

### App Startup

`src/app/startup/dynsmf_autoload.spl` constructs a startup dynSMF session from
CLI args plus `SIMPLE_DYNSMF` and `SIMPLE_DYNSMF_DISABLE`. The app-root
entrypoint first records general background compile requests for enabled
manifest entries whose `.smf` artifacts are missing or invalid, then calls the
checked autoload path silently on startup and exposes `--dynsmf-status` for
deterministic operator/test evidence. The compile request is general dynSMF
infrastructure, not GUI-only: every manifest entry maps a source path to a
`build/dynsmf/<id>.smf` output and the canonical wrapper materializes those
plans with `bin/simple compile <source> -o <artifact>.smf`. dynSMF control flags
are treated as shared app-root startup options so `--no-dynsmf` and
`--disable-dynsmf=<ids>` can control loading without becoming unknown commands.

## Verification Hooks

- `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dependency_gate.md`
- `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`
- `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_parallel_work_orders.md`
- `test/01_unit/app/ui/dependency_closure_gate_spec.spl` reads the real
  `app.ui.tui.backend`, `app.ui.render.widgets`, and HTML-capable adapter
  sources.
- `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`
  verifies the selected UI dependency acceptance criteria at the feature level.
- `test/01_unit/app/ui/render_capability_spec.spl` verifies the renderer
  capability registry, lazy HTML/CSS capability declarations, component-scoped
  CSS selection, and real render-adapter CSS selector usage.
- `test/01_unit/os/smf/dynsmf_session_spec.spl` verifies dynSMF artifact
  readiness, general background compile evidence for non-GUI and GUI manifest
  entries, missing/invalid artifact failure, and evidence through the existing
  SMF dynlib facade.
- `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl` verifies
  checked startup autoload policy, missing-artifact background compile queue
  evidence, and app-root dynSMF status evidence.
- `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl`
  verifies generated artifact readiness, default checked dynSMF autoload,
  per-id disable, stale symbol evidence, and reload generation at the system
  boundary.
- `scripts/check/check-low-dependency-dynsmf-build-plans.shs` materializes the
  seven planned `build/dynsmf/*.smf` artifacts and records package-build
  evidence.

## Follow-Up Migration

After this slice, later work can connect the resulting artifacts to deeper
kernel/user-space mapping without changing the startup, session, or policy
contract.
