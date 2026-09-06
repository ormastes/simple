# TLDR — Browser Sandbox Model (2026-08-15)

Only the hosted renderer worker has an OS jail (`runtime_process.c:2384`):
rlimits + no_new_privs + Landlock + seccomp. But the seccomp filter is a
DENY-list (default ALLOW, `:2372`), there are no namespaces/uid-drop, no
per-origin isolation, and the in-process browsers never enter the jail.
The JS engine leaked host APIs (`require("process"/"os")`, `process.exit/cwd`)
to page script — fixed today via the `node_compat_enabled` capability gate
(default DENY for `JsRuntime.new_browser`), spec-covered.

```
  standard model                     this repo (before fix)
  --------------                     ----------------------
  broker ──IPC──> renderer           hosted broker ──> jailed worker   [only lane]
             │  seccomp ALLOW-list              │  seccomp DENY-list
             │  user/net/pid ns                 │  no namespaces
             │  1 process / origin              │  1 process, all origins
  page JS ──> web API only           page JS ──> require/process leak  [FIXED]
                                     in-process browsers: NO jail      [tracked]
```

Phases: 1) engine capability gate (DONE) → 2) seccomp ALLOW-list + namespaces
+ jail the in-process browsers (tracked bug) → 3) per-origin renderer processes
→ 4) brokered net/fs/gpu, non-Linux jails.

Full doc: browser_sandbox_model_research_2026-08-15.md
