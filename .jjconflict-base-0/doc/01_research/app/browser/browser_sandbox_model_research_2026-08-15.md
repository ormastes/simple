# Browser Sandbox Model — Current State vs Standard Architecture (2026-08-15)

## 1. Reference model (Chromium-style)

A production browser sandbox is layered:

1. **Process split**: a privileged *broker* (browser process) and unprivileged
   *renderer* processes. Renderers never open sockets/files directly; every
   privileged operation is an IPC request the broker policy-checks.
2. **Kernel confinement per renderer**: seccomp-BPF **ALLOW-list** (default
   `SECCOMP_RET_KILL_PROCESS`, not a deny-list), `no_new_privs`, user/PID/net
   namespaces (empty net ns = no direct network), chroot/Landlock to an empty
   FS view, rlimits.
3. **Site isolation**: one renderer per site/origin group, so a compromised or
   Spectre-leaking renderer only holds one origin's data.
4. **Capability brokering**: net, fs, GPU, fonts are separate brokered
   services; the GPU process has its own (weaker) sandbox.
5. **Engine-level confinement**: the JS/Wasm engine exposes only the web
   platform API to page script; host bindings (Node-style `require`,
   `process`) are never reachable from web content (Electron's history shows
   why: `nodeIntegration` in a renderer is a known RCE pattern).

## 2. What exists in this repo today

| Layer | Status | Evidence |
|---|---|---|
| OS jail (hosted renderer worker) | EXISTS, Linux-only | `src/runtime/runtime_process.c:2384` `rt_browser_renderer_sandbox_enter`: rlimits + `no_new_privs` + Landlock deny-all FS + seccomp-BPF |
| Broker/renderer split | EXISTS for hosted browser only | worker entry `src/os/hosted/hosted_browser_renderer_worker.spl:1249`; broker `src/os/hosted/hosted_browser_renderer_process.spl:1595` |
| seccomp policy | **DENY-list**, default `SECCOMP_RET_ALLOW` | `src/runtime/runtime_process.c:2372` |
| Namespaces / uid drop | ABSENT | no `unshare`/`clone(CLONE_NEWUSER…)`/`setuid` in the jail path |
| Site isolation (per-origin process) | ABSENT | one renderer worker regardless of origin |
| In-process browsers | UNJAILED | `src/app/browser/**`, `src/os/apps/*browser*` never call the jail entry |
| JS engine host-API confinement | was LEAKY, now capability-gated (see §4) | `src/lib/gc_async_mut/js/engine/interpreter_native.spl` (`fetch` :32/:1098; `require` :77/:153-207 exposing path/buffer/os/process; process.cwd/exit/nextTick :14/:145-150; other modules denied via `_native_node_denied_module` :479) |
| Per-origin capability gating in engine | ABSENT | no origin identity attached to an interpreter |

Additional note: the repo's Electron/Chrome Vulkan evidence harnesses launch
Chromium with `--no-sandbox` / GPU-sandbox disabled
(`scripts/lib/renderdoc-evidence-common.shs`,
`scripts/check/check-electron-*-evidence.shs`; environment prepared by
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`). That is acceptable only as an
evidence-harness setting and must never leak into product launch defaults.

## 3. Gap analysis

1. **seccomp is a deny-list** (`runtime_process.c:2372`): any new/unlisted
   syscall is allowed by default. Standard practice is an allow-list with
   `KILL_PROCESS`. Highest-impact C-runtime change.
2. **No namespaces / privilege drop**: renderer keeps uid, net access is cut
   only by the seccomp deny-list, not by an empty net namespace.
3. **No site isolation**: one jailed worker serves all origins; cross-origin
   data lives in one address space.
4. **In-process browsers bypass the jail entirely**: `src/app/browser` and
   `src/os/apps/*browser*` execute page script in the host process with no OS
   confinement.
5. **Engine host-API leak (fixed 2026-08-15, this change)**: page script could
   `require("process")`/`require("os")` and call `process.exit`/`cwd` in the
   gc_async_mut engine because the native dispatch ignored the existing
   `node_compat_enabled` capability field; the nogc_sync_mut engine's require
   path additionally serves fs/net/http/child_process modules when the flag is
   on. See §4.
6. **Linux-only**: no macOS (sandbox_init/App Sandbox) or Windows
   (restricted-token/AppContainer) jail.

## 4. Fix landed with this research (pure Simple)

Capability = the existing host-granted `node_compat_enabled` field
(`src/lib/nogc_sync_mut/js/engine/interpreter.spl:426`; untrusted page script
gets `JsRuntime.new_browser`, which sets it false; trusted embedders — the
Electron backend `src/app/ui.electron/{main,backend}.spl` and default
`JsRuntime.new` — keep it true). Enforced at native **dispatch**, closing the
bypass:

- `src/lib/gc_async_mut/js/engine/interpreter_native.spl`: `NATIVE_NODE_PROCESS_CWD/NEXT_TICK/EXIT` return `Undefined` when untrusted; `require("process")`/`require("os")` return the denied-module object.
- `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`: same process-native gate; **all** node builtin modules (incl. fs/net/http/child_process) are denied via `_native_node_denied_module` when untrusted. Explicit per-module host grants (`node_credential_grant_*` / granted-module source keys) still work — they are host-issued capabilities by definition.
- `src/lib/nogc_sync_mut/js/engine/runtime.spl` `new_browser`: rewritten to set the flag on a local (chained field assignment fails under the interpreter — this silently threw and left specs unable to build a browser-mode runtime).

Spec: `test/01_unit/lib/js/js_native_confinement_spec.spl` (6 examples, green).

## 5. Phased recommendation

- **Phase 1 (done here)**: engine capability gate, default DENY for page script.
- **Phase 2 (C runtime, tracked)**: convert seccomp to ALLOW-list +
  `KILL_PROCESS`; add user/net/PID namespaces and uid drop where available;
  make in-process browsers spawn the jailed renderer worker instead of
  evaluating page script in-process. Tracked:
  `doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md`.
- **Phase 3**: site isolation — one jailed worker per origin group; attach an
  origin identity to each interpreter and key capability grants on it.
- **Phase 4**: brokered net/fs/gpu services (renderer loses `fetch`-direct
  paths; broker enforces CORS/CSP centrally); non-Linux jails.
