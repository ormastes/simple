# Browser jail: seccomp is a deny-list and in-process browsers are unjailed
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

**Revalidated 2026-11-02: still plausible because OPEN (tracked; out of scope of the 2026-08-15 engine-gate change); no merged fix commit with a passing regression is cited in this doc.**

## Update 2026-11-03 (fixlane): all three problems are fixed in code; row was stale

Evidence on release/1.0.0 (symbol/commit checked, not assumed):
1. seccomp deny-list -> allow-list: `browser_renderer_apply_seccomp` (`src/runtime/runtime_process.c`, ~2886) ends in `SECCOMP_RET_KILL_PROCESS` (arch mismatch also KILL); the only `SECCOMP_RET_ALLOW` rows are the per-syscall allow entries and the startup pre-filter. The old deny-list filter at ~1932 belongs to the separate dynlib/`unshare`-denying profile, not the renderer.
2. namespaces: `ae5a67a6ad0` "jail the browser renderer in user/net/IPC namespaces" -> `browser_renderer_enter_namespaces()` runs before landlock and seccomp in `browser_renderer_preinit`; posture published via `rt_browser_renderer_namespaces_active()`. uid drop is not applicable (user namespace maps to an unprivileged overflow identity).
3. in-process browsers: `e15384f4571` (fail-closed capability probe) + `34ec570cb22` ("Closes problem 3 ... in code": `sandbox_render.spl` broker -> jailed worker -> Draw IR -> software raster; `render_adapter.spl` takes that route whenever a sandbox is requested; `main.spl` refuses `SIMPLE_BROWSER_SANDBOX=1` rather than rendering unjailed) + `0ffdcdd958f` (one jailed-render session).
Re-run 2026-11-03 on Windows host: `browser_sandbox_routing_spec.spl` 5/5, `browser_sandbox_status_spec.spl` 3/3 PASS. The Linux seccomp/landlock self-check (`sh scripts/check/check-browser-renderer-sandbox-seccomp.shs`) exits `ERROR — nothing was checked` here (non-Linux) and is NOT claimed.
Honest residual (not part of the three listed problems): sandboxed rendering is opt-in (`SIMPLE_BROWSER_SANDBOX=1`), not the default, and `src/os/apps/*browser*` were not audited here.
VERIFY on Linux with a kernel that has seccomp+Landlock: `sh scripts/check/check-browser-renderer-sandbox-seccomp.shs` (expect PASS verdict), `bin/simple test test/01_unit/app/browser/browser_sandbox_routing_spec.spl`, and `SIMPLE_BROWSER_SANDBOX=1 bin/simple run src/app/browser/main.spl --sandbox-status` (expect jailed).
