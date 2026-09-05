# BUG: std.process.process_run crashes with "field access on nil receiver" on trivial command

- **Date:** 2026-07-17
- **Status:** fixed (2026-07-17)
- **Area:** standard library (std.process module wrapper around rt_process_run)
- **Severity:** high (crashes test/integration code; blocks repro of other bugs)

## Symptom

Calling `std.process.process_run` with a trivial, working command (e.g.
`/bin/echo "hello"`) crashes with:

```
runtime error: field access on nil receiver
Illegal Instruction (core dumped)
```

This occurs even outside any class method or complex context — a standalone
call in `main()` crashes immediately.

The raw underlying `extern fn rt_process_run` primitive (used directly, without
the std.process wrapper) works correctly for the same commands, suggesting the
wrapper layer has a nil-dereference bug.

## Minimal repro

```simple
use std.process.{process_run}

fn main() -> i32:
    val result = process_run("/bin/echo", ["hello"])
    print "result={result}"
    0
```

Probe: `probe06_debug_procrun.spl` (from repro session)

Expected: prints result info or runs command successfully
Actual: crashes with nil-receiver field access + SIGILL

## Workaround

Use the raw `extern fn rt_process_run` primitive directly instead of the wrapper:

```simple
extern fn rt_process_run(cmd: text, args: [text]) -> (i32, text, text):
    none

fn main() -> i32:
    val (exit_code, stdout, stderr) = rt_process_run("/bin/echo", ["hello"])
    print "exit={exit_code}"
    0
```

Verified working: `probe06_debug_rawproc.spl`

## Impact

- Blocks all test/integration code using the documented std.process API
- Blocks repro of other nested-interpreter bugs that rely on spawning subprocesses
  via the clean API (e.g., verification of `interp_method_call_result_as_arg_corruption_nested_2026-06-30`)
- Existing workaround is internal: only the raw extern is usable in practice

## Root cause (confirmed 2026-07-17)

Not a Result/Option unwrap bug. `process_run` itself (`src/lib/nogc_sync_mut/io/process_ops.spl:43`)
returns a plain `(text, text, i64)` tuple and never touches an Option/Result.

The crash is in `proc_slot_acquire()` /
`src/lib/nogc_sync_mut/io/process_governor.spl`, which `process_run` calls
before/after every `rt_process_run`. That module previously declared:

```
val _active_procs: AtomicI64 = atomic_i64_new(0)
```

`AtomicI64` is a `class` defined in a *different* module
(`std.nogc_sync_mut.atomic`). Isolated repro (bisected with a dozen minimal
probes, see the fix's verification transcript) showed a general interpreter
landmine in the bootstrap seed:

> A module-level `val`/`var` whose declared type is a `class` imported from
> another module resolves to a **nil receiver** when that value is read via a
> method call from inside a function body — regardless of whether the
> initializer runs eagerly (top-level `val`) or lazily (assigned inside a
> function on first use). Plain scalar globals (i64, bool, text) and classes
> defined in the *same file* as the global do not trigger it.

Minimal repro that reproduces the crash with no process/atomic code at all:

```simple
use test.tmp_probe.counter_mod.counter.{Counter, counter_new}  # class defined elsewhere

val _c: Counter = counter_new(42)

fn main() -> i32:
    val v = _c.get()   # crashes: "runtime error: field access on nil receiver"
    0
```

`process_governor.spl` was the only module in `src/lib`/`src/app`/`src/compiler`
using this exact pattern (`val _x: AtomicI64 = atomic_i64_new(...)` as a
module global), so the fix was scoped to that one file rather than the
general interpreter defect (which would require a Rust-seed change, out of
scope for a stdlib-only fix).

## Fix

`src/lib/nogc_sync_mut/io/process_governor.spl`: replaced the module-level
`AtomicI64` instance with a lazily-created raw `i64` atomic *handle*
(`rt_atomic_int_new`/`rt_atomic_int_load`/`rt_atomic_int_compare_exchange`
called directly, bypassing the `AtomicI64` class wrapper). The handle is
stored in a module-level `var` and created on first use inside a function
(`_active_procs_h()`), which does not hit the landmine (module globals of
plain scalar type, written from inside a function, work correctly). Public
API (`proc_slot_max/active/acquire/release/reset`) and behavior are
unchanged.

## Verification (2026-07-17)

- Standalone repro (`std.process.process_run("/bin/echo", ["hello"])` from a
  plain `fn main()`, no test harness): crashes at baseline
  (`runtime error: field access on nil receiver`, SIGILL/core dump); no
  crash after the fix, `process_run("echo", ["hi"])` returns
  `("hi\n", "", 0)`.
- Nonexistent command: returns `exit_code=-1`, empty stdout/stderr — loud
  sentinel, not a crash.
- Non-zero exit command (`/bin/sh -c "exit 7"`): returns `exit_code=7`.
- Existing specs (`process_ops_ext_spec.spl`,
  `process_limits_enforcement_spec.spl`, `io_numeric_guard_spec.spl`,
  `timeout_spec.spl`, `signal_stubs_spec.spl`): identical pass/fail counts
  before and after the fix (the 2 `timeout_spec.spl` failures and the 1
  `signal_stubs_spec.spl` failure are pre-existing and unrelated —
  confirmed via `git stash`/`stash pop` A/B on the unmodified tree).
- `sh scripts/check/native-smoke-matrix.shs`: 15/15 PASS (process_governor.spl
  is reachable from `src/app/io/process_ops.spl`, documented as part of the
  interpreted CLI closure).
- Native-build of a process_run probe fails, but for pre-existing, unrelated
  reasons (`MIR lowering error: unresolved method call: join`,
  `for-in over non-array iterables is not supported by native codegen yet
  (#143)` — hit by `for ch in trimmed:` string iteration already present in
  `process_governor.spl`/`process_ops.spl` before this fix). Not attempted to
  force; native-build of `std.process` remains unsupported today,
  independent of this change.

## Side finding — not fixed here, worth separate attention

The general interpreter defect above (module-level global of a
cross-module-imported class type -> nil receiver in function scope) is
broader than `process_governor.spl`. It was NOT reproducible through the
SSpec test harness (`describe`/`it` blocks) — e.g.
`process_ops_ext_spec.spl`'s `process_run` tests passed even against the
*unfixed* `process_governor.spl`, because the harness's own call path
apparently keeps the interpreter in a state where the landmine doesn't
trigger. Only a genuine standalone `fn main()` invoked via `bin/simple run`
hits it. This means SSpec-style specs cannot catch a regression of this bug
class; any future stdlib code using a module-level global typed as a
cross-module class should avoid that pattern (use a lazily-initialized raw
handle/scalar instead, as done here) until the underlying seed interpreter
behavior is fixed.
