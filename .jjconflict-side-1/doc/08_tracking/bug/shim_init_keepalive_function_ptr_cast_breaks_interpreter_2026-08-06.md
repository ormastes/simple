# `shim_init()` cannot run under the tree-walk interpreter — `_shim_keepalive()`'s function-pointer-to-u64 casts fail at runtime

**Date:** 2026-08-06
**Status:** OPEN
**Severity:** Medium (blocks unit-spec coverage of the C-ABI syscall shim
layer's real boot entrypoint; does not affect native/board behavior)

## Symptom

Any `.spl` spec that calls `os.kernel.abi.syscall_shim.shim_init(sched, ipc,
klog)` fails every example with:

```
semantic: type mismatch: cannot cast function to u64
```

Reproduced in isolation — a minimal spec with a single `it` block that does
nothing but `shim_init(Scheduler.new(), IpcManager.new(), KernelLog.new(16))`
then calls `spl_handle_getpid(...)` fails the same way. Removing the
`shim_init()` call (and instead assigning `g_shim_scheduler`/`g_shim_ipc`/
`g_shim_klog` directly — they are ordinary module-level `var`s, already
imported and mutated this way by the shim's own sibling files) makes the
identical test pass.

## Root cause

`shim_init()` (`src/os/kernel/abi/syscall_shim.spl:232`) unconditionally
calls `_shim_keepalive()` at line 239:

```
fn shim_init(sched: Scheduler, ipc: IpcManager, klog: KernelLog):
    g_shim_scheduler = sched
    g_shim_ipc = ipc
    g_shim_klog = klog
    # Keep the keepalive reference alive under DCE. ...
    val _keepalive = _shim_keepalive()
```

`_shim_keepalive()` (line 139) sums `spl_handle_* as u64` — casting each
`spl_handle_*` function to a `u64` (its address), purely to give the DCE pass
a reachability edge from `shim_init` to every shim function. This is a
documented, load-bearing pattern for the **native/board build path**: the
comment says the function "is never called at runtime" there, since DCE only
needs the cast to exist statically.

But `bin/simple test` (per `.claude/rules/testing.md` — "`run` and `test` are
DIFFERENT ENGINES") hard-defaults to the tree-walk **interpreter**, which
*does* execute `shim_init()`'s body when a spec calls it, including the
`_shim_keepalive()` call this time (previously nothing called `shim_init` in
any spec). The interpreter has no runtime representation for "function value
cast to u64" and raises the semantic error above.

`test/01_unit/os/kernel/abi/syscall_shim_spec.spl` (pre-existing,
compile-only) never trips this, because it only checks function
name/arity/return-type reflection — it never calls `shim_init()` or any
`spl_handle_*` function, so `_shim_keepalive()`'s body is never executed
under that spec.

## Workaround applied

`test/01_unit/os/kernel/abi/syscall_shim_process_state_spec.spl` (new,
2026-08-06) seeds `g_shim_scheduler`/`g_shim_ipc`/`g_shim_klog` by direct
assignment instead of calling `shim_init()`. This exercises the actual
`@export("C")` shim functions and their state-threading back into the
module-global `g_shim_scheduler` (the thing under test), while sidestepping
the interpreter's inability to execute `_shim_keepalive()`.

## What's still not covered

- `shim_init()` itself — the real boot entrypoint — has zero interpreter-run
  coverage. It can only be verified by (a) a native/JIT-run harness (outside
  `bin/simple test`'s engine), or (b) a real QEMU boot, where boot code
  already calls it.
- No fix attempted here: the `as u64` function-pointer cast is a legitimate,
  intentional native-codegen pattern (function address arithmetic for DCE
  retention) — teaching the interpreter to no-op/stub it out is a
  interpreter-engine change (`src/compiler_rust/`), out of scope for a spec
  coverage pass and against "Fix .spl not Rust" / "No bootstrap unless
  essential" defaults.

## Suggested follow-up

Either (a) give the interpreter a runtime value for a function-to-u64 cast
(e.g. a stable synthetic id, since the *result* is provably unused at
runtime — `_keepalive` is discarded), or (b) gate `_shim_keepalive()`'s call
site behind a compile-time/native-only condition so `shim_init()` itself
becomes interpreter-safe without weakening the DCE guarantee for the native
build.

## Re-verification (2026-08-10)

Status confirmed unchanged: `_shim_keepalive()` in
`src/os/kernel/abi/syscall_shim.spl` still performs six `spl_handle_* as u64`
function-pointer-to-integer casts, called unconditionally from `shim_init()`
(lines ~139-145, ~232-239 unchanged). This is a `.spl`-source-visible
construct, but the failure is in the **tree-walk interpreter's runtime**
(`src/compiler_rust/` — the interpreter has no runtime representation for a
function-value-to-`u64` cast), which is out of scope per this sweep's hard
constraint against editing `src/compiler_rust/**`. No `@cfg`/conditional-
compilation primitive exists in the `.spl` language today to gate the
`_shim_keepalive()` call site behind "native-only" at the source level
(checked `src/compiler/10.frontend/core/cfg_platform.spl` and
`parser_preprocessor.spl` — these implement OS/arch target `cfg()`, not an
engine-selector such as interpreter-vs-native), so suggested fix (b) is also
currently blocked without new frontend work, itself out of this sweep's
scope (broad language-feature addition, not a narrow bug fix).
`test/01_unit/os/kernel/abi/syscall_shim_process_state_spec.spl`'s workaround
(direct `g_shim_scheduler`/`g_shim_ipc`/`g_shim_klog` assignment, bypassing
`shim_init()`) remains the correct mitigation and still passes. Leaving
**OPEN — ARCHITECTURAL** (requires Rust-seed interpreter runtime work, out of
scope for this sweep).
