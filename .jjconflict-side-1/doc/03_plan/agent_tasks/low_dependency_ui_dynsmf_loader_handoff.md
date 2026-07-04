# Low Dependency UI dynSMF Loader Handoff

Date: 2026-06-05

## Purpose

This handoff gives Agents B and C concrete loader/session facts to use after
feature and NFR options are selected. It does not select final requirements.

## Current Loader Surface

Existing source APIs:

- `src/os/kernel/loader/dylib_registry.spl`
  - `dylib_registry_reset_for_test()`
  - `dylib_registry_register(path, bytes) -> i64`
  - `dylib_registry_open(path) -> i64`
  - `dylib_registry_close(handle) -> i64`
  - `dylib_registry_symbol(handle, name) -> i64`
  - `dylib_registry_mark_mapped(handle) -> i64`
  - `dylib_registry_symbol_is_process_callable(handle, name) -> bool`
- `src/os/posix/dylib_async.spl`
  - `dylib_async_open(path, mode) -> u64`
  - `dylib_async_symbol(handle, name) -> u64`
  - `dylib_async_close(handle) -> u64`
  - sync wrappers: `dylib_open`, `dylib_symbol`, `dylib_close`
- `src/os/posix/dynlib.spl`
  - OOP facade with `DynLibKind.{Elf, Smf, Pe, Invalid}`
  - `dynlib_open`, `dynlib_symbol`, `dynlib_symbol_is_process_callable`,
    `dynlib_close`, `dynlib_is_valid`, `dynlib_path`, `dynlib_format_name`
- `src/os/smf/smf_dynlib.spl`
  - `smf_dlopen`, `smf_dlsym`, `smf_dlclose`

Existing tests:

- `test/01_unit/os/kernel/loader/dylib_registry_spec.spl`
  - covers registration, SMF wrappers, role-2 SMF wrappers, path-backed open
    refcounting, invalid blobs, symbol lookup, and process-callable checks.
- `test/01_unit/os/posix/dylib_async_spec.spl`
  - covers self handle routing, SMF/absolute path routing, relative path
    rejection, known self symbols, and sync wrappers.
- `test/01_unit/os/posix/dynlib_spec.spl`
  - covers facade format/path/validity and invalid close/symbol behavior.
- `test/03_system/stdlib/dynload/dynload_simpleos_smf_system_spec.spl`
  - covers SimpleOS SMF registration, independent SMF libraries, invalid SMF,
    and mixed ELF/SMF registry behavior.

## Missing Contract For This Feature

The current loader can register, open, resolve, and close handles. The requested
feature needs a higher-level session contract:

- session-owned dynSMF handle table;
- default library autoload list;
- arg/env skip-all and skip-specific policy;
- unload from the active session;
- stale-handle behavior after unload;
- reload with fresh session state in interpreter-mode tests.

Current implementation now provides a stdlib-like dynSMF autoload manifest for
`file_io`, `net_io`, `render2d`, `web_renderer`, `gui_renderer`, and
`tui_renderer` in `src/os/smf/dynsmf_session.spl`.

## Implemented Session API Sketch

- `DynSmfManifestEntry`: id, precompiled SMF path, source module,
  artifact kind, default autoload flag, ABI version, and exported symbols.
- `DynSmfBuildPlan`: deterministic source path, output path, and
  `bin/simple compile <source> -o <output>` command for each precompiled
  manifest entry.
- `DynSmfSession`: session id, loaded entries, disabled ids, source of policy
  decisions, and handle generation counter.
- `dynsmf_policy_from_args_env(args, env_dynsmf, env_disable) -> DynSmfPolicy`
- `dynsmf_session_load(session, manifest, id) -> DynSmfSession`
- `dynsmf_session_unload(session, id) -> DynSmfSession`
- `dynsmf_session_symbol(session, id, symbol) -> DynSmfEvidenceRow`
- `dynsmf_session_record_symbol(session, id, symbol) -> DynSmfSession`
- `dynsmf_build_plans(manifest) -> [DynSmfBuildPlan]`

## Policy Inputs

Proposed control names:

- Arg: `--no-dynsmf`
- Arg: `--disable-dynsmf=<id>[,<id>...]`
- Env: `SIMPLE_DYNSMF=0`
- Env: `SIMPLE_DYNSMF_DISABLE=<id>[,<id>...]`

Policy precedence:

1. explicit skip-all disables all default autoload;
2. explicit per-id disable suppresses only matching ids;
3. explicit component demand may load a non-default library unless skip-all or
   that id is disabled;
4. tests can construct a session policy directly without mutating process env.

## Stale Handle Contract

After `dynsmf_session_unload(session, id)`:

- symbols resolved through the unloaded id return a stale/unloaded diagnostic;
- old raw handles are not reused silently inside the same session generation;
- a reload increments the generation and returns fresh handle metadata;
- tests can assert that state initialized by the previous load is absent after
  unload/reload.

This mirrors POSIX/Qt style lifetime rules while keeping interpreter tests
deterministic.

## Covered Test Contracts

- Dependency policy unit test: `--no-dynsmf` and `SIMPLE_DYNSMF=0` suppress all
  default autoload ids.
- Per-id policy unit test: disabling `web_renderer` still autoloads `file_io`
  and `tui_renderer`.
- Session lifecycle unit test: load, resolve symbol, unload, stale lookup fails,
  reload, fresh lookup succeeds.
- Interpreter-mode unit test: the session can unload `tui_renderer` and reload
  it without stale exported state.
- Unit smoke: default session records load evidence for all six enabled
  stdlib-like precompiled manifest entries.
- Unit smoke: every precompiled manifest entry has a ready compile-to-SMF build
  plan pointing at a concrete repo source and `build/dynsmf/<id>.smf` output.
- Build smoke: `scripts/check/check-low-dependency-dynsmf-build-plans.shs`
  executes the six compile plans and emits
  `build/low_dependency_ui_dynsmf/build_plans/evidence.env`.

## Agent B Tasks

1. Decide whether session state wraps `dynlib.spl` or the lower
   `dylib_registry` handles directly.
2. Define generation-aware stale-handle diagnostics.
3. Write failing unit specs before implementation.
4. Preserve existing registry refcount tests.

## Agent C Tasks

1. Define the manifest schema.
2. Add the six requested stdlib-like ids.
3. Implement arg/env policy parsing without process-global mutation.
4. Produce evidence rows that verification can inspect.
