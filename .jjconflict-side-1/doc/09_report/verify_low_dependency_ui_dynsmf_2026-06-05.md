# Verification Report: low_dependency_ui_dynsmf

Date: 2026-06-05

Scope: focused verification of the low-dependency UI/dynSMF feature lane,
including feature tracking links, mirrored SPipe manuals, placeholder-test
guards, requirement/NFR traceability, dynSMF lifecycle specs,
startup-sensitive integration evidence, generated-spec layout, and the
core/lib/MCP smoke gates required by the tracked LSP adapter changes.

## Findings

[PASS] `doc/08_tracking/feature/feature_db.sdn` — the
`LOW_DEPENDENCY_UI_DYNSMF_2026_06_05` row has populated requirement, research,
plan, architecture, design, system spec, generated spec, implementation, unit
test, integration test, and guide fields.

[PASS] `doc/02_requirements/feature/low_dependency_ui_dynsmf.md` — final
requirements now match the expanded implementation scope: all six requested
default dynSMF ids must be build-ready, checked at startup, policy-controlled,
and unload/reload verified.

[PASS] `doc/03_plan/agent_tasks/low_dependency_ui_dynsmf_selection_audit.md` —
the selected-plan audit is current with focused implementation evidence and no
longer describes executable specs, implementation, or manuals as pending.

[PASS] tracked feature row paths — every path referenced by the feature row
exists in the current worktree.

[PASS] mirrored SPipe manuals — every tracked executable `*_spec.spl` under
`test/` has a corresponding tracked and existing generated manual under
`doc/06_spec/`.

[PASS] requirement traceability — every `REQ-001` through `REQ-010` and every
`NFR-001` through `NFR-006` appears in executable SPipe specs and mirrored
generated manuals.

[PASS] placeholder scan — no tracked lane source/spec/manual path contains
placeholder passes, trivial always-true expectations, weak no-op helpers,
open todo markers, or fixme markers.

[PASS] `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` —
startup-sensitive subprocess failures are hard failures with diagnostics
instead of placeholder passes.

[PASS] `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl` —
checked startup evidence can materialize missing `build/dynsmf/*.smf` artifacts
through `scripts/check/check-low-dependency-dynsmf-build-plans.shs` before
asserting default loaded libraries.

[PASS] `test/01_unit/os/smf/smf_dynlib_spec.spl` — lower checked SMF dynlib
open validates `.smf` extension, file existence, and `SMF\0` magic before
returning a handle, while compatibility `smf_dlopen` keeps request-shape
behavior stable.

[PASS] `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl` —
system coverage unloads, checks stale symbol evidence, and checked-reloads all
six selected default dynSMF ids.

[PASS] architecture/design docs — feature architecture and detail design now
describe checked startup/session loads as using `smf_dlopen_checked`, with
plain `smf_dlopen` retained as the compatibility load facade.

[PASS] tracked `.spl` check sweep — all 37 tracked implementation and spec
files pass `bin/simple check`.

[PASS] tracked executable specs — all 16 tracked unit, integration, and system
specs pass in interpreter mode.

[PASS] dynSMF artifact build evidence —
`scripts/check/check-low-dependency-dynsmf-build-plans.shs` compiled all six
`build/dynsmf/*.smf` artifacts with `SMF\0` magic and reported
`low_dependency_dynsmf_build_status=pass`.

[PASS] core/lib/MCP smoke gates — `bin/simple check src/compiler`,
`bin/simple check src/lib`, `bin/simple check src/app/mcp`,
`bin/simple check src/app/simple_lsp_mcp`, and
`SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
all pass. Full logs are under `build/low_dependency_ui_dynsmf/verify/`.

[PASS] `find doc/06_spec -name '*_spec.spl' | wc -l` — result is `0`.

## Commands

```sh
bin/simple check test/02_integration/app/startup_argparse_mmap_perf_spec.spl
bin/simple test test/02_integration/app/startup_argparse_mmap_perf_spec.spl --mode=interpreter
bin/simple spipe-docgen test/02_integration/app/startup_argparse_mmap_perf_spec.spl --output doc/06_spec
bin/simple check test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl
bin/simple test test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl --mode=interpreter
bin/simple check src/os/smf/smf_dynlib.spl
bin/simple check src/os/smf/dynsmf_session.spl
bin/simple check test/01_unit/os/smf/smf_dynlib_spec.spl
bin/simple test test/01_unit/os/smf/smf_dynlib_spec.spl --mode=interpreter
bin/simple spipe-docgen test/01_unit/os/smf/smf_dynlib_spec.spl --output doc/06_spec
bin/simple test test/01_unit/os/smf/dynsmf_session_spec.spl --mode=interpreter
bin/simple test test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl --mode=interpreter
bin/simple spipe-docgen test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/app/ui/dependency_closure_gate_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/app/ui/render_capability_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/os/smf/dynsmf_session_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl --output doc/06_spec
sh scripts/check/check-low-dependency-dynsmf-build-plans.shs
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
bin/simple lint doc/08_tracking/feature/feature_db.sdn
bin/simple check-dbs
bin/simple check src/compiler
bin/simple check src/lib
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Status

STATUS: PASS (0 failures, 0 warnings)
