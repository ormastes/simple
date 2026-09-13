# Browser jail: seccomp is a deny-list and in-process browsers are unjailed

- **Date**: 2026-08-15
- **Status**: OPEN (tracked; out of scope of the 2026-08-15 engine-gate change)
- **Area**: runtime (C), app/browser, os/hosted
- **Research**: `doc/01_research/app/browser/browser_sandbox_model_research_2026-08-15.md`

## Problems

1. **seccomp deny-list**: `rt_browser_renderer_sandbox_enter`
   (`src/runtime/runtime_process.c:2384`) installs a seccomp-BPF filter whose
   default action is `SECCOMP_RET_ALLOW` (`:2372`) with a list of denied
   syscalls. Any syscall not on the list — including future kernel additions —
   is allowed. Standard browser practice is an ALLOW-list with default
   `SECCOMP_RET_KILL_PROCESS`.
2. **No namespaces / privilege drop**: the jail sets rlimits, `no_new_privs`,
   and Landlock, but does not unshare user/net/PID namespaces or drop uid, so
   a compromised renderer retains direct network reach unless every net
   syscall stays on the deny-list.
3. **In-process browsers bypass the jail**: only the hosted renderer worker
   (`src/os/hosted/hosted_browser_renderer_worker.spl:1249`, broker
   `hosted_browser_renderer_process.spl:1595`) enters the jail. The
   in-process browsers under `src/app/browser/**` and `src/os/apps/*browser*`
   evaluate page script in the host process with no OS confinement.

## Required fix (Phase 2 of the research doc)

- Convert the seccomp filter to an ALLOW-list with `KILL_PROCESS` default;
  enumerate the worker's actual syscall set (strace under the spec suite).
- Unshare user+net (+PID where possible) namespaces before entering the jail.
- Route the in-process browsers' page-script execution through the jailed
  renderer worker instead of the host process.

## Interim mitigation (landed 2026-08-15)

Engine-level capability gate: untrusted page script
(`JsRuntime.new_browser`) is denied `require("process"/"os"/…)` and
`process.exit/cwd/nextTick` at native dispatch —
`src/lib/{gc_async_mut,nogc_sync_mut}/js/engine/interpreter_native.spl`,
spec `test/01_unit/lib/js/js_native_confinement_spec.spl`.

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/01_unit/lib/js/js_native_confinement_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-12 — reproduced, left OPEN

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust bootstrap seed,
`Simple Language v1.0.0-rc.1`), sha256 prefix `3d120a6f`.

```
SIMPLE_RUST_SEED_WARNING=0 timeout 420 bin/simple test \
  test/01_unit/lib/js/js_native_confinement_spec.spl --no-session-daemon
SPEC FILE VERDICT: test/01_unit/lib/js/js_native_confinement_spec.spl outcome=ERROR declared>=6 executed=6 passed=2 failed=4 skipped=0 dropped=0
```

4 of 6 examples red, reproduced on the deployed seed. The primary file
`src/runtime/runtime_process.c` is **fenced** by this fan-out (it appears in
`egl_offlimits_v2.txt`), and it is C runtime rather than pure Simple, so no edit
was attempted.

## Fix 2026-09-13 (BUGFIX-6 lane) — js_native_confinement_spec.spl unblocked (adjacent, not the C jail itself)

The 4/6 red examples in `test/01_unit/lib/js/js_native_confinement_spec.spl`
were NOT the seccomp/namespace/in-process-jail defects this row tracks (those
remain OPEN — `src/runtime/runtime_process.c` is fenced and C runtime, not
touched). The actual failure was an unrelated construction defect: the spec
builds `Logger(name: "confinement-spec", level: LogLevel.Error)` as a struct
literal, but `class Logger` in `src/lib/common/js/engine/js_error.spl` (and
its `src/lib/nogc_sync_mut/js/engine/js_error.spl` twin) had no `level` field
— `static fn new(name, level)` accepted the argument and threw it away, the
same defect pattern already fixed once for a sibling Logger in
`doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md`
(OPEN 4). `semantic: class 'Logger' has no field named 'level'` failed the
spec at construction, before any confinement assertion ran.

RED (base `a6450c9d6f5`, seed sha256 prefix `3d120a6f9ab5704b`):
`Results: 6 total, 2 passed, 4 failed` (`class 'Logger' has no field named
'level'` on all four).

Fix: added a real `level: LogLevel` field to both `Logger` classes,
`should_log` now rank-compares against it (previously always `true`,
identical "inert filter" defect as the already-fixed sibling), and updated
the three other bare `Logger(name: ...)` construction sites
(`src/lib/{common,nogc_sync_mut}/js/engine/runtime.spl`'s
`js_runtime_with_default_logger`, and
`test/01_unit/lib/common/js_async_fetch_spec.spl`) to pass an explicit
`level: LogLevel.Info`.

GREEN: `js_native_confinement_spec.spl` 6/6; `js_async_fetch_spec.spl` 1/1.
Suite check `bin/simple test test/01_unit/lib/js` (60 total, 47 passed, 13
failed, 13 skipped) — the 13 failures
(`function_scope_chain_and_global_constructors_spec.spl`,
`statement_dispatch_class_spec.spl`, `statement_dispatch_regression_spec.spl`)
are pre-existing JS-engine gaps (classic `for` statement, global
String/Number/Boolean conversions, class statement dispatch) with no mention
of `Logger`/`LogLevel` in their failures — confirmed unrelated to this change,
no regression introduced.

This row (`browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15`) stays
OPEN — the actual seccomp deny-list/namespace/in-process-jail defects are
untouched, C runtime, fenced.
