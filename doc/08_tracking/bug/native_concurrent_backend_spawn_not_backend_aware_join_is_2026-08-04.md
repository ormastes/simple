# BUG: with the "native" concurrent backend, spawn stores the result in the pure_std map but join reads the native registry — every join returns nil

**Status:** ARCHITECTURAL-OPEN (re-confirmed 2026-08-10; fix requires editing src/compiler_rust, out of scope for a .spl-lane pass)
**Found:** 2026-08-04
**Severity:** high — every thread spawned while the concurrent backend is
`"native"` joins to `nil`, silently. No error, no warning; the value is simply
gone.
**Files:**
- `src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:207`
  (`rt_thread_spawn_isolated_with_context`)
- `src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:272`
  (`rt_thread_spawn_isolated_with_args_context`)
- `src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:339`
  (`rt_thread_join`)
- failing spec: `test/01_unit/std/perf_optimization_spec.spl` (+ legacy duplicate
  `test/unit/std/perf_optimization_spec.spl`)

## Symptom

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/std/perf_optimization_spec.spl
  ✗ spawns thread after switching to native          expected nil to equal 42
  ✗ spawn_isolated_with_args works in native mode    expected nil to equal 5
  ✗ completes work switches continues                expected nil to equal native_result
  ✗ alternates backends 10 times with spawns         expected nil to equal 9
Results: 51 total, 47 passed, 4 failed
```

Minimal shape, from `perf_optimization_spec.spl:280-285`:

```
rt_set_concurrent_backend("native")
val handle = spawn_thread(\: 42)
val result = handle.join()
expect result == 42            # actual: nil
```

The discriminator is clean: **all four failures, and only those four, are the
cases where `"native"` is the active backend at the moment of the spawn.** The
`pure_std` spawns in the very same examples pass — in "completes work switches
continues" (`:397`) `h1` (pure_std) and `h3` (pure_std) both join correctly, and
only `h2`, spawned between the two `rt_set_concurrent_backend` calls, returns
nil. In "alternates backends 10 times" (`:487`) the even (pure_std) rounds pass
and it dies on an odd (native) round.

This spec is not a shim: it declares `extern fn rt_thread_spawn_isolated`,
`rt_thread_join`, `rt_set_concurrent_backend` etc. directly at lines 27-43, so it
is exercising the real runtime entry points.

## Root cause

`rt_thread_join` is backend-aware. The spawn functions are not.

`concurrency.rs:339` — join dispatches on the backend first:

```
pub fn rt_thread_join(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle_id = ...;
        return registry.thread.thread_join(handle_id);      // native provider
    }
    ...
    let result = THREAD_RESULTS.lock().unwrap().remove(&handle_id)
        .unwrap_or(Value::Int(0));                          // pure_std map
    Ok(result)
}
```

`concurrency.rs:207` — spawn has **no `get_concurrent_registry()` call and no
backend branch at all**. It unconditionally takes the pure_std path: it
allocates a handle from `NEXT_HANDLE_ID`, runs the closure inline, and stores
the result in the process-global `THREAD_RESULTS` map. Same for the
`_with_args_context` variant at `:272`.

So under `"native"`:

1. spawn writes result → `THREAD_RESULTS[handle_id]` (pure_std storage),
2. join reads → `registry.thread.thread_join(handle_id)` (native provider),
   which has never heard of `handle_id`,
3. join yields nil.

The two halves of one operation are reading and writing different stores. Note
also that the pure_std join path defaults a miss to `Value::Int(0)` rather than
erroring, so a handle mix-up in that direction would surface as a silent `0` —
the same class of fault, opposite value.

## Why not fixed now

The fix belongs in `src/compiler_rust/`, and this repo's standing rule is
**fix `.spl`, not Rust** (`.claude/memory/feedback_fix_spl_not_rust.md`); the
Rust tree here is the bootstrap seed, which is explicitly not the normal tool.
Landing a seed change from a test-repair lane would also require a bootstrap
rebuild to be verifiable, which is out of scope for this pass.

The correct fix is small and worth doing in the right lane: give the two spawn
functions the same `get_concurrent_registry()` / `backend()` branch that
`rt_thread_join` already has at `:341`, routing to
`registry.thread.thread_spawn*` when the backend is not `PureStd`, so spawn and
join always share one store. While there, consider making the pure_std join
miss at `:369` an error instead of `unwrap_or(Value::Int(0))` — the silent `0`
default would have hidden this defect in the other direction.

**Do not "fix" the spec** by removing the `rt_set_concurrent_backend("native")`
calls: those four examples are the only coverage the native backend has.

## Re-confirmed 2026-08-09

Re-inspected `src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs`
fresh: `rt_thread_join` (line 339-340) still opens with
`let registry = get_concurrent_registry();` and branches on
`registry.backend()`, while `rt_thread_spawn_isolated_with_context` (line 207)
and `rt_thread_spawn_isolated_with_args_context` (line 272) still have **no**
`get_concurrent_registry()` call at all — grep of every `get_concurrent_registry`
call site in the file confirms spawn is absent from that list while join and
nine other functions have it. Root cause and fix location are unchanged from
the original report.

Characterized as **ARCHITECTURAL-OPEN**: the fix must land in
`src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs`, which is
explicitly out of scope for `.spl`-lane fixes per
`.claude/memory/feedback_fix_spl_not_rust.md` (Rust tree = bootstrap seed, not
the normal tool), and a verifiable landing would additionally require a
bootstrap rebuild, out of scope for this pass. No `.spl`/`.shs` source change
is possible here without touching the Rust seed. Left OPEN as originally
scoped; no spec changes made.

## Re-confirmed 2026-08-10

Re-ran the failing spec fresh:

```
$ bin/simple test test/01_unit/std/perf_optimization_spec.spl
  expected nil to equal 42
  expected nil to equal 5
  expected nil to equal native_result
  expected nil to equal 9
Results: 51 total, 47 passed, 4 failed
```

Identical four failures, identical shape, as originally documented. Root
cause location (`concurrency.rs:207`/`:272` spawn missing the
`get_concurrent_registry()` backend branch that `:339` join has) is unchanged
and remains in `src/compiler_rust/`, which this session's hard constraints
forbid editing. Status remains ARCHITECTURAL-OPEN; no code or spec changed.
