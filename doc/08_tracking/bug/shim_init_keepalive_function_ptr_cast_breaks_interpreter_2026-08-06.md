# `shim_init()` cannot run under the tree-walk interpreter — `_shim_keepalive()`'s function-pointer-to-u64 casts fail at runtime
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: needs interpreter support for function-pointer-to-u64 casts, an interpreter semantic gap, not a bounded local fix. No change made.


## Update 2026-11-06 (work/fx-os-kernel-20261106)

`syscall_shim_spec.spl` was 72/75. The "-1 where -22/-95/-14 expected" case
("network shims bound copied buffers and reject unsupported address output")
is FIXED: `spl_handle_net_accept/send_to/recv_from` ran the descriptor capability
check first, so malformed arguments on an unauthorised caller returned EPERM (-1).
New pure `portable_net_args_precheck_v1` (`src/os/kernel/ipc/syscall_net_portable_v1.spl`)
validates size (EINVAL), unsupported address output (EOPNOTSUPP) and kernel-range
buffer (EFAULT) before the authority check, matching bind's
copy-errors-before-authorization policy. No caller memory is read, so authority
semantics are unchanged. Now 73/75. Still open, seed-interpreter limits, not ABI:
- "spl_handle_debug_write return type is i64": real `mmio_write8` recursion overflow.
- "network shims reject null and short sockaddr inputs before MMIO":
  `user_copyin_bytes` `[0u8; len]` with u64 len ("array repeat count must be an
  integer, got u64", `src/os/kernel/memory/user_copy.spl:24`).

## 2026-11-10: boot initializer repair; runtime verification pending

The source repair retains `_shim_keepalive` in a typed mutable module function
slot and assigns that slot from `shim_init`. It no longer calls the helper:
interpreters can install the function value without evaluating native function
address arithmetic. The complete native provider-address graph is unchanged.
A module slot is used rather than an unused local expression that optimization
could discard. Native retention remains an explicit verification requirement.

Executable regressions:

- Exact boot-entry reproduction:
  `test/01_unit/os/kernel/abi/syscall_shim_init_spec.spl` initializes the real
  shim and checks supplied log sizes and getpid behavior. A no-op initializer
  fails the nondefault log-size checks.
- Generalization:
  `test/01_unit/os/kernel/abi/syscall_shim_process_state_spec.spl` now calls
  `shim_init` instead of directly assigning globals; it checks real spawn state,
  resetting that state, and ECHILD through the C-ABI wrapper.
- Native production-import probe:
  `test/fixtures/os/syscall_shim_init_keepalive/main.spl` initializes twice,
  checks supplied state, and requires `SHIM_INIT_KEEPALIVE_PASS` on exit 0.
- `sh scripts/check/check-syscall-shim-keepalive-symbols.shs --artifact <binary>`
  requires every production keepalive provider to have a strong text definition.
  Weak C fallbacks, missing providers, and unreadable artifacts cannot pass.

Executed here: the symbol gate's `--selftest` passed five controls using actual
Clang-generated ELF objects (strong providers, weak fallback, missing provider,
invalid artifact, missing artifact). This checks the gate, **not** Simple code
execution or native retention.

Required before this bug can close:

1. Use the recovered self-hosted runtime to execute both specs above, retaining
   nonzero executed assertion counts and exact producer/source identities.
2. Native-build the production-import probe with the ordinary optimized
   `--entry-closure` path, keeping symbols available; run the strong-symbol gate
   and then run the output with exit 0 and the expected marker.
3. Check the retention mechanism with an isolated callback-root removal control.
   If supported exported roots already retain all providers independently,
   investigate removing the obsolete graph rather than treating the redundant
   callback as necessary. Do not weaken the provider or boot-behavior checks.

Current state is **fix implemented, verification pending**. No interpreter,
native-link, QEMU, or board pass is claimed by the symbol-gate controls.
