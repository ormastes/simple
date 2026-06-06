# Feature: low-dependency-ui-dynsmf

## Raw Request
$sp_dev
refactor ui dependency and add smf dynlib feature.  research web about similar situations. and research local. and detail plans for multiple agents in pherallel.
Tui dependency minimize and no dependency to gui but ui.
Gui, web renderer, minimize dependency, let only gui widget depend html renderer component and css only used components to loaded. Refactor to highly low dependency arch.
lets make common libs, which are std lib like, file io, net io, 2d renderer, web renderer, gui renderer, tui renderer, be precompiled dynsmf. unless specify to not to load all or specific lib by arg or env. Load them as smf dynlib. however there should be way to unload from session to test lib itself in test in interpreter mode.

## Task Type
feature

## Refined Goal
Refactor the Simple UI and renderer stack into low-dependency UI contracts and loadable precompiled SMF dynlibs for standard library-like capabilities, with explicit opt-in/opt-out controls and interpreter-testable unload support.

## Acceptance Criteria
- AC-1: Local and web research artifacts identify the current dependency hot spots, prior repo work, and comparable dynamic loading/lazy component patterns.
- AC-2: Requirement options and NFR options exist with pros, cons, and effort estimates, and final requirements are not written until the user selects options.
- AC-3: TUI imports depend only on common UI contracts and TUI renderer code; they do not import GUI, HTML renderer, browser, or CSS implementation modules.
- AC-4: GUI, web, Tauri, Electron, VSCode, browser, and TUI-web adapters consume shared UI/web-render contracts while implementation modules remain behind adapter or widget boundaries.
- AC-5: HTML renderer and CSS implementation modules are loaded only for components or adapters that need them; non-web/non-HTML lanes can prove they do not pull the HTML/CSS closure.
- AC-6: File IO, net IO, 2D renderer, web renderer, GUI renderer, and TUI renderer libraries have precompiled dynSMF manifest entries and load through the SMF dynlib path by default.
- AC-7: CLI arguments and environment variables can disable all auto dynSMF loading or disable specific dynSMF libraries.
- AC-8: A session-scoped dynSMF handle can unload a library and then reload it in interpreter-mode tests so the library can test itself without stale session state.
- AC-9: System and unit SPipe specs cover dependency boundaries, dynSMF default loading, opt-out controls, and unload/reload behavior without placeholder assertions.
- AC-10: Parallel agent plan assigns independent work lanes with inputs, outputs, sequencing, conflict boundaries, and verification gates.

## Scope Exclusions
- No automatic final requirement selection.
- No release or push until verify produces `STATUS: PASS`.
- No edits to unrelated dirty thread-enhancement or compiler Rust work unless required by selected requirements.

## Phase
focused-implementation-verified

## Log
- dev: Created combined SPipe lane with 10 acceptance criteria for UI dependency minimization and SMF dynlib loading.
- research: Added local and domain research plus TLDR companions.
- requirements: User selected Feature Option C and NFR-A+B. Added final feature/NFR requirements and deleted option docs.
- plan: Added parallel multi-agent task plan with conflict boundaries and sequencing.
- research: Added corrected exact-prefix import closure evidence. Base `app.ui.tui` currently has zero web/TUI-web/HTML/browser/CSS/GUI implementation modules in closure; common `app.ui.render.widgets -> app.ui.render.html_widgets` is the first split target.
- plan: Added loader/session handoff for Agents B/C covering current dynlib APIs, missing dynSMF session contract, provisional arg/env policy, stale-handle behavior, and post-selection tests.
- plan: Added option-independent system-test plans for UI dependency gates and dynSMF session lifecycle. Executable specs remain pending final requirement selection.
- plan: Added parallel work-order packet with per-agent file ownership, deliverables, merge sequencing, conflict rules, and handoff commands.
- architecture: Promoted selected thin-slice architecture to final architecture doc.
- design: Promoted selected thin-slice detail design to final design doc.
- audit: Replaced preselection audit and selection packet with selection audit for Feature Option C, NFR-A+B, and `tui_renderer`.
- implementation: Added `src/app/ui/dependency_closure_gate.spl` for exact-prefix reachable-import dependency closure reports and `src/os/smf/dynsmf_session.spl` for the first `tui_renderer` dynSMF manifest/session/policy slice.
- tests: Added `test/01_unit/app/ui/dependency_closure_gate_spec.spl` and `test/01_unit/os/smf/dynsmf_session_spec.spl`; generated manuals under `doc/06_spec/01_unit/...`.
- verification: `bin/simple check` passed for the two implementation modules and two specs; focused interpreter specs passed 4/4 and 6/6; `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- tracking: Updated `LOW_DEPENDENCY_UI_DYNSMF_2026_06_05` in `doc/08_tracking/feature/feature_db.sdn` with spec docs, implementation modules, and unit specs.
- implementation: Migrated HTML render callers off `app.ui.render.widgets` to `app.ui.render.html_widgets`, kept `app.ui.render.widgets` as a TUI-only compatibility wrapper, and routed `DynSmfSession` load/symbol/unload through `smf_dlopen`, `smf_dlsym`, and `smf_dlclose`.
- tests: Extended dependency gate coverage to follow `export use`, catch unresolved forbidden imports, and read the real `app.ui.tui.backend` plus `app.ui.render.widgets` source closures. Dependency gate now passes 7/7; dynSMF session remains 6/6 with SMF dynlib facade assertions; `html_render_spec` passes 26/26 and `widget_menu_tooltip_spec` passes 33/33 after import migration.
- docs: Updated architecture, detail design, TLDRs, generated manuals, and `doc/07_guide/app/ui/ui_render.md` with the backend-specific renderer import rule.
- verification: Focused `bin/simple check` passed for the shim, dependency/dynSMF modules, migrated production caller, key migrated tests, split backend matrix specs, and generated specs. `backend_matrix_spec` now passes 3/3 after using a viewport wide enough for the sample UI; the web, Tauri, Electron, and browser backend matrix slices pass 1/1 each.
- tracking: Expanded the feature row with the TUI-only shim, migrated production caller, focused migrated tests, and UI render guide.
- tests: Split backend-specific matrix assertions into focused specs so each file stays below the test runner timeout; browser matrix coverage intentionally asserts shared body HTML/target/viewport while existing browser pixel-path specs retain `render_frame` artifact coverage.
- implementation: Strengthened dynSMF session evidence so `DynSmfEvidenceRow.to_text()` includes policy source, symbol/stale lookups can be appended to session evidence, and reloads are recorded with a distinct `reload` action.
- tests: Extended `dynsmf_session_spec` to 9/9 with explicit `--no-dynsmf`, `--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, and `SIMPLE_DYNSMF_DISABLE=<ids>` policy coverage plus persisted symbol evidence, stale lookup evidence, and reload action assertions.
- docs: Updated dynSMF architecture/detail design docs and regenerated `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md`.
- implementation: Advanced AC-6 by marking all six requested stdlib-like ids as `precompiled_smf` manifest entries with source modules and `build/dynsmf/*.smf` artifact paths, and made default autoload attempt all enabled entries through `smf_dlopen`.
- tests: Extended `dynsmf_session_spec` to 10/10 with all-six precompiled manifest validation, all-default autoload evidence, skip-all evidence for every default entry, and no duplicate already-loaded handles on repeated autoload before a `tui_renderer` reload.
- docs: Updated requirements, architecture, detail design, loader handoff, system-test plan, TLDRs, and regenerated `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md`.
- implementation: Added `DynSmfBuildPlan` plus `dynsmf_build_plans` helpers so every default dynSMF manifest entry maps to a concrete repo source and deterministic `bin/simple compile <source> -o build/dynsmf/<id>.smf` command.
- tests: Extended `dynsmf_session_spec` to 11/11 with compile-plan assertions for file IO, 2D renderer, HTML web renderer, and TUI renderer outputs.
- docs: Updated requirements, architecture, detail design, loader handoff, system-test plan, TLDRs, and regenerated `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md` for build-plan coverage.
- implementation: Added `scripts/check/check-low-dependency-dynsmf-build-plans.shs`; it reads the canonical build plans, compiles all six `build/dynsmf/*.smf` artifacts by default, and emits `build/low_dependency_ui_dynsmf/build_plans/evidence.env` plus a Markdown report.
- verification: The new dynSMF build wrapper passed with 6/6 compiled artifacts and `SMF\0` magic (`534d4600`) for each output.
- implementation: Extended the UI dependency closure gate with direct import helpers and real adapter-source checks for web, Tauri, Electron, browser, VSCode, TUI-web, and headless web-render adapters.
- tests: Dependency gate now passes 9/9, including direct `app.ui.render.html_widgets` imports for HTML-capable adapters, no legacy `app.ui.render.widgets` shim imports in those adapters, and shared `common.ui.web_render_api` imports where applicable.
- docs: Regenerated `doc/06_spec/01_unit/app/ui/dependency_closure_gate_spec.md` and updated dependency-gate traceability for AC-3, AC-4, AC-5, and NFR-A to covered.
- tests: Added system specs `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl` and `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl`; both pass 3/3 in interpreter mode and have generated manuals under `doc/06_spec/03_system/...`.
- tracking: Added the new system specs and manuals to `LOW_DEPENDENCY_UI_DYNSMF_2026_06_05` in the feature database.
- implementation: Added `src/app/startup/dynsmf_autoload.spl` and wired `src/app/main.spl` to silently construct a dynSMF startup session by default, with `--dynsmf-status` evidence and `--no-dynsmf` / `--disable-dynsmf=<ids>` app-root controls.
- tests: Added `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`; it passes 5/5 and verifies default six-library autoload, arg/env skip-all, per-id disable, quiet plain app-root startup, and app-root status evidence.
- docs: Generated `doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md` and updated dynSMF plan, architecture/design docs, TLDRs, and `doc/07_guide/lib/api/dynlib_api.md` for the startup path.
- implementation: Added implementation-free `src/app/ui.render/capability.spl`; `html_widgets.spl` declares the lazy `html_renderer` capability and `css.spl` declares the lazy `css_provider` capability while TUI remains the default renderer capability.
- tests: Added `test/01_unit/app/ui/render_capability_spec.spl` and extended the feature-level dependency system spec to cover explicit lazy HTML/CSS renderer capabilities. Capability spec passes 4/4; feature-level dependency gate passes 4/4; existing `html_render_spec` and `widget_menu_tooltip_spec` remain green.
- docs: Regenerated `doc/06_spec/01_unit/app/ui/render_capability_spec.md` and `doc/06_spec/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.md`; updated UI render guide and traceability docs for renderer capability metadata.
- implementation: Added `css_for_components([...])` to `src/app/ui.render/css.spl` and migrated test/repl/search/sim/tree/terminal/Jupyter/LSP render adapters to component-scoped CSS selection.
- tests: `render_capability_spec` now passes 7/7 and gates real adapter sources so they use `css_for_components` without direct shared CSS function concatenation. The feature-level dependency system spec now passes 5/5 with CSS payload selection evidence.
- docs: Regenerated the capability and feature-level manuals again and updated architecture/design/guide text for component-scoped CSS payload selection.
- implementation: Added `DynSmfArtifactStatus`, pure byte-level SMF magic validation, filesystem artifact readiness checks, and checked dynSMF load/autoload helpers. App startup now uses checked autoload, so enabled entries must have generated `.smf` artifacts before `smf_dlopen`.
- tests: Extended `dynsmf_session_spec` to 14/14 with artifact-readiness validation and missing-artifact checked-load failure. Strengthened the dynSMF system spec to require `dynsmf_artifacts_ready(manifest)` and checked default autoload; the unit, startup integration, and system dynload specs pass in interpreter mode with current `build/dynsmf/*.smf` artifacts.
- docs: Updated canonical `doc/04_architecture/ui/simple_gui_stack.md` and TLDR with the low-dependency renderer capability boundary, component-scoped CSS selection, checked dynSMF startup libraries, verification requirements, and source-map entries; feature tracking now references the stack docs as architecture evidence.
- tracking: Split `LOW_DEPENDENCY_UI_DYNSMF_2026_06_05` feature DB evidence into populated `system_spec`, `spec_doc`, `unit_tests`, and `integration_tests` fields so SPipe handoff checks can find the executable specs and generated manuals by phase.
- tests: Strengthened `dynsmf_session_unload_reload_spec` to 4/4 by unloading, checking stale symbol evidence, and checked-reloading all six default dynSMF ids (`file_io`, `net_io`, `render2d`, `web_renderer`, `gui_renderer`, `tui_renderer`). Regenerated the system manual and updated the dynSMF system-test plan/TLDR for all-library unload/reload evidence.
- verify: Removed placeholder pass assertions from `startup_argparse_mmap_perf_spec`, added its generated-manual doc block, added missing tracked manuals for `html_render_spec` and `widget_menu_tooltip_spec`, and wrote focused verification report `doc/09_report/verify_low_dependency_ui_dynsmf_2026-06-05.md` with `STATUS: WARN` pending full release verification.
- requirements: Updated final feature requirements and TLDR to remove stale first-slice/`tui_renderer`-only language. REQ-005, REQ-006, REQ-008, and REQ-010 now require all six requested default dynSMF ids to be build-ready, startup-checked, policy-controlled, and unload/reload verified.
- plan: Refreshed the selection audit and TLDR so they no longer describe specs, implementation, or manuals as pending and now point to all-six dynSMF evidence plus full `$verify` as the next release gate.
- tests: Made `dynsmf_autoload_policy_spec` fresh-workspace robust by invoking `scripts/check/check-low-dependency-dynsmf-build-plans.shs` when checked startup cannot see generated `build/dynsmf/*.smf` artifacts; regenerated its manual and updated the dynSMF system-test plan/report.
- implementation: Added `smf_dlopen_checked` to `src/os/smf/smf_dynlib.spl` and routed checked dynSMF session loads through it. The lower checked open validates `.smf` extension, file existence, and `SMF\0` magic before returning a handle while preserving compatibility `smf_dlopen` request-shape behavior.
- tests: Added `test/01_unit/os/smf/smf_dynlib_spec.spl` plus generated manual to cover lower checked SMF dynlib open success/failure paths, and added the new source/spec/manual to feature tracking.
- docs: Aligned architecture/design TLDRs and detail design with `smf_dlopen_checked` as the checked startup/session load path. Focused guards passed for lower SMF dynlib, dynSMF session, startup policy, unload/reload, `check-dbs`, feature-row path/manual mirroring, placeholder scan, and `doc/06_spec` layout.
- verify: Added explicit REQ/NFR trace IDs to the executable dependency, renderer capability, dynSMF session, checked dynlib, startup policy, and system specs; regenerated mirrored manuals. Trace audit now covers REQ-001 through REQ-010 and NFR-001 through NFR-006 in both executable specs and `doc/06_spec` manuals.
- verify: Completed the feature-lane verification sweep: numbered artifact guard passed for working/staged views, feature DB lint and `check-dbs` passed, all 37 tracked `.spl` files passed `bin/simple check`, all 16 tracked specs passed in interpreter mode, all six dynSMF artifacts compiled with `SMF\0` magic, and required core/lib/MCP smoke gates passed. Updated `doc/09_report/verify_low_dependency_ui_dynsmf_2026-06-05.md` to `STATUS: PASS`.
- next: Feature-lane implementation and verification are complete. Prepare a scoped commit/release handoff only after reviewing the shared dirty worktree and excluding unrelated lanes.
