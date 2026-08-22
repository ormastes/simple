# JIT de-JITs whole stage1: `rt_process_read_stdout_checked` unresolved (2026-08-22)

**Status:** FIXED (pending stage1 re-verification)
**Class:** runtime-symbol registration gap — the same defect class as
`jit_runtime_symbol_unregistered_rt_value_unbox_int_2026-08-11.md` and the
`rt_process_run_owned_bounded_value` lane, one layer lower.

## Symptom

```
[jit-fallback] unresolved external symbol 'rt_process_read_stdout_checked':
 whole module dropped to the interpreter (expect ~100-1000x slowdown).
```

Emitted by `codegen/jit.rs::first_unresolved_import`. One unresolvable name
fails the *whole* `compile_module`, so every function in stage1 interprets.

## What it was NOT

The task hypothesis was "commit `4aa4918803a` added Simple-side `extern`
declarations with no runtime definition". That is false, and worth recording so
the next investigation does not re-tread it. At `origin/main` the symbol is:

- declared: `src/lib/nogc_sync_mut/io/process_ops.spl:33`
- prototyped: `src/runtime/runtime.h:898`
- **defined in C**: `src/runtime/runtime_process.c` (both `_WIN32` and POSIX branches)
- dispatched by the interpreter: `interpreter_extern/system.rs:1432`
- listed in `RUNTIME_SYMBOL_NAMES`: `common/src/runtime_symbols.rs:800`
- covered by codegen signatures (`codegen/runtime_sffi.rs`) and by
  `stage4_symbol_closure.spl`

Every check that exists passed, because every one of them checks a *list* or a
*text*. `check-unbacked-extern-ratchet.shs` reads `nm` on link artifacts and so
would see it — but only for artifacts that link the C runtime.

## Root cause

`src/compiler_rust/runtime/build.rs` is the entire registration mechanism: it
text-scans `RUNTIME_SYMBOL_NAMES`, intersects it with
`collect_defined_runtime_symbols()`, and emits `RUNTIME_SYMBOL_ENTRIES` — what
`register_static_runtime_symbols` publishes and what the JIT's `JITBuilder`
resolves against.

`collect_defined_runtime_symbols` scans the Rust runtime's `src/**.rs` plus a
**hardcoded** `LINKED_C_SOURCES` list, and `compile_c_runtime_sources` compiles
a matching hardcoded `c_sources` list. **`runtime_process.c` was in neither.**
So the symbol was listed-but-not-defined *from build.rs's point of view*, got no
`RuntimeSymbolEntry`, was never registered, and `dlsym` could not find it either
because the object was never linked into the seed. Cranelift then binds the
import to a NULL GOT slot — exactly the failure mode the guard exists to catch.

The whole C-only piped family shared the defect
(`rt_process_spawn_piped`, `rt_process_read_stdout`, `rt_process_write_stdin`,
`rt_process_close_piped`, `rt_process_is_alive`, `rt_process_is_alive_checked`,
`rt_browser_renderer_*`, `rt_editor_*_simple_dap`);
`rt_process_read_stdout_checked` was merely the first one the guard reported.

## Fix

1. `src/compiler_rust/runtime/build.rs`: add `runtime_process.c` and its
   fork/exec helper `runtime_fork.c` to `c_sources`, `LINKED_C_SOURCES`, and the
   `rerun-if-changed` set.
2. `src/runtime/runtime_process.c`: three symbols
   (`rt_process_run_timeout`, `rt_process_run_bounded`, `rt_process_wait`) have
   Rust twins in `value/sffi/env_process.rs` and would duplicate at link. They
   are compiled out — together with their private `win_/posix_process_run_capture`
   helpers — under a new `SIMPLE_RUNTIME_PROCESS_RUST_CORE`, defined *only* by
   that build.rs. Every other lane (native product build, SimpleOS sysroot,
   standalone) is byte-unchanged. `rt_process_is_running` / `rt_process_kill`
   also have Rust twins but already sit behind `SIMPLE_CORE_C_STANDALONE`, which
   this build does not define.
3. build.rs's export scan cannot see the `#ifndef`, so the three names are
   filtered out of `runtime_process.c`'s scanned exports explicitly (same shape
   as the existing `runtime_simd_dispatch.c` special case).

No new function was written: the "checked" ABI was already implemented
faithfully in C. This is purely a link/registration repair.

## Reproduce / regression gate

`src/compiler_rust/compiler/tests/process_checked_symbols_registered.rs` —
asserts every C-only `rt_process_*_checked` name listed in
`RUNTIME_SYMBOL_NAMES` resolves through the static provider, plus a
non-vacuity test (a live symbol must resolve, a nonexistent one must not) so an
inert registry cannot fake a pass. Fails pre-fix, passes post-fix.

## Lesson for the guards

`check-no-unresolved-runtime-symbols.shs` is the right guard for this class but
is ADVISORY and currently RED; it also checks the *C runtime archive*, not the
seed's own registration table. A seed-side variant — "every name in
`RUNTIME_SYMBOL_NAMES` that has a definition anywhere in `src/runtime/*.c` must
be in a C source list build.rs actually compiles" — would have caught this
statically. Filed as follow-up, not implemented here.

## Measured evidence (2026-08-22)

Symbol export in the seed binary, `nm -D <bin> | grep -c "T rt_process_read_stdout_checked"`:

| binary | count |
|---|---|
| `/mnt/data/seedperf/simple.ed4694134a0` (deployed seed, pre-fix) | **0** |
| `/mnt/data/worktrees/goal-main-1/bin/simple` (deployed seed, pre-fix) | **0** |
| this tree's `cargo build --release --bin simple` | **1** |

That zero is the whole defect: `jit_import_resolves` misses both the registry
and the `dlsym` fallback, so the GOT slot is NULL and `first_unresolved_import`
returns the name. Also verified in the generated artifacts:
`RUNTIME_SYMBOL_ENTRIES` now carries `rt_process_read_stdout_checked` and
`rt_process_is_alive_checked`, and `libruntime_sffi_c.a` defines the whole
`rt_process_*_piped` family (18 `rt_process_*` `T` symbols) while defining
**none** of the three Rust-owned names — the `SIMPLE_RUNTIME_PROCESS_RUST_CORE`
guard works and there is no duplicate-symbol risk. `cargo build --release --bin
simple` finishes clean.

Gates: `sh scripts/check/check-c-runtime-compiles-push.shs` -> `PASS — 115
file(s) compiled, 0 errors (2 skipped)`.
`sh scripts/check/check-no-unresolved-runtime-symbols.shs` -> `ERROR — nothing
was checked (no tracked bootstrap stage binary found)`; origin/main no longer
tracks any `bootstrap/**/simple` blob, so that guard cannot observe this fix
either way. Unchanged by this commit.
