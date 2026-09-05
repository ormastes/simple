# Low Dependency UI dynSMF Session — System Test Plan

## Scope

- stdlib-like dynSMF manifest entries for file IO, net IO, 2D renderer, web
  renderer, GUI renderer, and TUI renderer;
- default dynSMF autoload policy;
- app startup policy wiring and app-root status evidence;
- deterministic compile-to-SMF build plans for default dynSMF artifacts;
- interpreter-startup background compile request evidence for missing dynSMF
  artifacts, using the same general build-plan contract for non-GUI and GUI
  libraries;
- runtime artifact readiness validation for generated `build/dynsmf/*.smf`
  outputs;
- arg/env skip-all and per-library disable policy;
- session-owned dynSMF handles;
- unload, stale-handle diagnostics, and reload with fresh generation for each
  selected default dynSMF library;
- interpreter-mode self-test support for unloading any selected default library
  under test.

## Execution

Candidate executable specs after requirement selection:

- `test/01_unit/os/smf/dynsmf_session_spec.spl`
- `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`
- `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl`

Candidate generated manuals:

- `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md`
- `doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md`
- `doc/06_spec/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.md`

## Pass Criteria

- Specs use real assertions and built-in matchers only.
- Default policy attempts to load selected dynSMF manifest entries.
- App startup constructs a dynSMF session from CLI args and
  `SIMPLE_DYNSMF`/`SIMPLE_DYNSMF_DISABLE` environment values.
- Startup and system-boundary checked autoload reject missing, short, or invalid
  SMF artifacts before `smf_dlopen`.
- Startup records `compile_background` queued evidence for enabled missing
  artifacts before checked autoload fails closed; this evidence is general to
  all dynSMF manifest entries and is not GUI-only.
- `src/app/main.spl --dynsmf-status` emits deterministic startup evidence while
  plain app-root startup remains quiet.
- Every precompiled manifest entry has a ready build plan with a concrete source
  path and `build/dynsmf/<id>.smf` output.
- `scripts/check/check-low-dependency-dynsmf-build-plans.shs` materializes the
  six planned artifacts and records compile evidence; the system spec validates
  those artifacts with `dynsmf_artifacts_ready`.
- Startup integration evidence can run in a fresh workspace by invoking the
  canonical build wrapper when checked autoload cannot see the generated
  `build/dynsmf/*.smf` artifacts.
- `--no-dynsmf` and `SIMPLE_DYNSMF=0` suppress all default dynSMF autoload.
- `--disable-dynsmf=<id>` and `SIMPLE_DYNSMF_DISABLE=<id>` suppress only named
  libraries.
- Unload invalidates session symbols for each selected default dynSMF id with a
  deterministic stale/unloaded diagnostic.
- Reload increments generation and returns fresh handle metadata for every
  selected default dynSMF library.
- Interpreter-mode tests can unload and reload every selected default library
  under test without retaining stale exported state.
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Candidate Traceability

| Candidate | Description | Executable Spec | Generated Spec | Coverage |
|-----------|-------------|-----------------|----------------|----------|
| AC-6 | Requested stdlib-like libraries have precompiled dynSMF manifest entries | `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`; `test/01_unit/os/smf/dynsmf_session_spec.spl`; `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl`; `scripts/check/check-low-dependency-dynsmf-build-plans.shs` | `doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md`; `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md`; `doc/06_spec/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.md`; `build/low_dependency_ui_dynsmf/build_plans/report.md` | Covered |
| AC-7 | Arg/env controls disable all or named dynSMF libraries | `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`; `test/01_unit/os/smf/dynsmf_session_spec.spl` | `doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md`; `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md` | Covered |
| AC-8 | Session unload/reload works in interpreter-mode tests for every selected default library | `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl` | `doc/06_spec/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.md` | Covered |
| NFR-B | Runtime load/unload evidence is inspectable | `test/01_unit/os/smf/dynsmf_session_spec.spl` | `doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md` | Covered |

## Current Baseline

Existing loader APIs:

- `dylib_registry_register`, `dylib_registry_open`, `dylib_registry_close`,
  `dylib_registry_symbol`;
- `dylib_open`, `dylib_symbol`, `dylib_close`;
- `dynlib_open`, `dynlib_symbol`, `dynlib_close`;
- `smf_dlopen`, `smf_dlsym`, `smf_dlclose`.

Existing loader tests cover registry close/refcount and SMF wrapper loading.
The low-dependency dynSMF unit spec now covers artifact-readiness validation,
general background compile evidence, session-owned stdlib dynSMF autoload,
skip-all, per-id disable, unload, stale lookup, and reload policy. The
integration spec now covers checked `app.startup.dynsmf_autoload`, missing
artifact background compile queue evidence, and the
`src/app/main.spl --dynsmf-status` app-root path. The system spec now exercises
unload, stale symbol evidence, and checked reload for all six selected default
library ids.

## Implementation Notes

- Session policy should be constructible in tests without mutating process env.
- Raw handles should not be reused silently inside the same session generation.
- Evidence rows should include library id, policy source, load status, handle
  generation, and skip/unload reason.
