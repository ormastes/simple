# Stage4 full-CLI link: undefined peer-code symbols (link stage reached)

- **Date:** 2026-07-28
- **Lane:** stage4 one-binary link (core-c-bootstrap), after all compile + archive blockers cleared
- **Status:** open — link-stage; peer app-code symbol bugs

## Progress
Every earlier blocker is fixed and at origin: compile 1584/1584 green (closefrom,
gui_backend import, formula split), archive fingerprint (runtime_contracts.c added,
a7ac45b7), archive symbol audit (duplicate simple_contract_check removed, f3c4b9d6).
The build now reaches the final LINK and fails on 2 undefined symbols:

```
"_resolved_theme_fingerprint", referenced from
    _ui_dot_web__html_css__generate_css (mod_251.o)
"_run_test_api_server_with_inject", referenced from
    _office__sheets__access_server__run_calc_access_server (mod_165.o)
```

## Root (genuine missing/renamed defs, NOT compiler)
1. **resolved_theme_fingerprint** — `src/app/ui.web/html_css.spl:8` imports it from
   `nogc_sync_mut.ui.theme_package`, but that module defines/exports
   `theme_package_fingerprint` (theme_package.spl:113,1088), NOT
   `resolved_theme_fingerprint`. Stale caller from the glass-theme work — likely a
   rename the caller didn't follow (html_css.spl:26 calls it). Fix owner: theme/UI.
2. **run_test_api_server_with_inject** — defined `src/app/ui.standalone/bootstrap.spl:36`,
   imported+called by `src/app/office/sheets/access_server.spl:7,23`. A test-api
   server referenced from the office/sheets production closure; either the definition
   isn't reaching the linked set (module not in closure / not exported from the
   package mod) or the office→ui.standalone dependency shouldn't be in the prod lane.

## Note
These are the last-known link errors; there may be more behind them. The stage4
full-CLI closure has an open tail of peer app-code linkage issues across sessions.
The autonomous deploy loop will produce a clean build + deploy the O(1) runtime
perf fix once the tip links cleanly.

## Update 2026-07-28 (triaged)
1. **resolved_theme_fingerprint — FIXED (this session).** Genuine missing symbol:
   `theme_package` exports `theme_package_fingerprint(theme_id) -> text` (loads +
   resolves the package internally), not `resolved_theme_fingerprint`. Repointed
   `html_css.spl` import + call to `theme_package_fingerprint` (signature-identical,
   semantically the resolved fingerprint).
2. **run_test_api_server_with_inject — MANGLER BUG, not a source issue.** Defined
   (bootstrap.spl:36), exported (__init__.spl:2), explicitly imported
   (access_server.spl:7), NO competing wildcard, NO other def/extern — yet emitted as
   a BARE extern. The function takes a `fn(UIEvent)` closure parameter; the mangler
   appears to bare-extern calls to functions with fn-type params (same family as the
   _text_index_len bare-extern, mangle.rs). Needs the compiler-side mangler fix
   (Codex), not a per-site source change — the call site is already correct.

## Refinement 2026-07-28 (after theme fix landed)
Rebuild with the theme fix pushed: `resolved_theme_fingerprint` is GONE, leaving
EXACTLY ONE undefined symbol — `_run_test_api_server_with_inject`. So the
bare-extern is NOT broadly systemic (a general fn-param mangler bug would leave
many undefined symbols); it is specific to this single call. Narrows the Codex
investigation: not "all fn-param calls" but something particular to this
function/callsite (candidates: the `ui.standalone` dotted package-name path, the
specific fn-type param signature `fn(UIEvent)`, or this module's discovery/export
into the closure). One symbol from a clean full-CLI link + deploy.

## Update 2026-07-30 (new pair, same mangler class — worked around)

Two more undefined symbols surfaced at the link stage, same bare-extern class:

```
"_extract_compiler_coverage_manifest_sdn", referenced from:
    _nogc_sync_mut__test_runner__test_runner_execute__run_test_file_interpreter (mod_1370.o)
    _nogc_sync_mut__test_runner__test_runner_execute__run_test_file_native (mod_1370.o)
"_strip_compiler_coverage_manifest_blocks", referenced from:
    _nogc_sync_mut__test_runner__test_runner_execute__run_test_file_interpreter (mod_1370.o)
```

Both are called from `run_test_file_interpreter` / `run_test_file_native` in
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`, and both are
genuinely defined and exported in the sibling module
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` (lines 489 and
511; exported at line 585/592). Not a stale reference — both names exist with
matching signatures.

Root: `test_runner_execute.spl` imported them (among many other names) via the
`std.test_runner.test_executor_parsing` variant-resolution facade (`std.` strips
to a per-family lookup rather than the concrete `nogc_sync_mut` tree), the same
facade-indirection shape as the already-fixed
`run_test_api_server_with_inject` case (`app.ui.standalone` → `app.ui.standalone.bootstrap`,
commit `b51e19436d`). Applied the same source-level workaround: pulled these two
symbols out of the `std.test_runner.test_executor_parsing` import block and out
of the file's `export use std.test_runner.test_executor_parsing.{...}`
re-export line, and added a dedicated
`export use nogc_sync_mut.test_runner.test_executor_parsing.{extract_compiler_coverage_manifest_sdn, strip_compiler_coverage_manifest_blocks}`
pointing straight at the concrete defining module (also preserves the existing
re-export of these two names to consumers of `test_runner_execute.spl`). This is
a workaround for the Rust-seed mangler bare-extern-on-facade-re-export defect in
`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`, not a
source-level bug fix — the underlying mangler defect is still open and will
presumably recur for the next facade-crossing peer call.
