# Mutex/RwLock lose `text` (and any non-int/float/bool/heap-tagged) values under the default `PureStd` concurrent backend

- **Filed:** 2026-07-28
- **Severity:** high — silent data loss, no error, no warning
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Found via:** SF4 mutex/rwlock guard-lane redo (generics), while writing a
  round-trip proof spec per the task's explicit "prove i64 AND text" requirement

## Symptom

`mutex_new("hello")` followed immediately by `rt_mutex_lock` (no `with_lock`,
no user code involved) returns `nil`, not `"hello"`. i64-valued mutexes round-trip
correctly. This reproduces with the plain, non-guarded extern-level API
(`mutex_lock`/`mutex_unlock`), so it is **not** caused by, or specific to, the
`with_lock` guard pattern or the just-retracted `Any`-typed-closure bug
(`any_typed_closure_param_destroys_value_2026-07-28.md`) — it is a separate,
lower-layer defect in the mutex/rwlock runtime bridge itself.

Minimal repro (`bin/simple test`, seed binary `bin/release/x86_64-unknown-linux-gnu/simple`):

```simple
use std.nogc_sync_mut.concurrent.mutex.{mutex_new, mutex_lock, mutex_unlock}

val m = mutex_new("hello")
val v = mutex_lock(m)
print(v)              # -> nil, not "hello"
mutex_unlock(m, v)
```

```simple
val m2 = mutex_new(41)
val v2 = mutex_lock(m2)
print(v2)              # -> 41, correct
```

## Root cause

`ConcurrentBackend::PureStd` is the `#[default]` backend
(`src/compiler_rust/compiler/src/concurrent_providers/mod.rs:20-27`). With this
backend, `rt_mutex_new_fn`/`rt_mutex_lock_fn`/`rt_mutex_unlock_fn`
(`src/compiler_rust/compiler/src/interpreter_extern/atomic.rs`) skip the
`registry.lock` delegation (`if registry.backend() != ConcurrentBackend::PureStd`
is false) and instead marshal the interpreter's `Value` through
`simple_runtime::value::RuntimeValue` via the local helpers at
`interpreter_extern/atomic.rs:486-527`:

```rust
fn value_to_runtime(v: &Value) -> RuntimeValue {
    match v {
        ...
        Value::Str(s) => {
            // For now, convert string to NIL (proper implementation would create RuntimeString)
            RuntimeValue::NIL
        }
        _ => RuntimeValue::NIL,
    }
}
```

Every `Value::Str` (and every other variant not Int/Float/Bool/Nil/heap-tagged-Int)
is silently converted to `RuntimeValue::NIL` on the way *in* to
`rt_mutex_new`/`rt_mutex_lock`/`rt_mutex_unlock`, and `runtime_to_value` has no
path back to `Value::Str` either (`interpreter_extern/atomic.rs:511-527`) — the
comment ("For now... proper implementation would create RuntimeString") marks
this as a known placeholder, not an oversight, but it is undocumented outside
the source and has no filed bug or test coverage.

Confirmed workaround (verification only, not applied): switching the backend to
`Native` (`rt_set_concurrent_backend("native")`) routes through
`NativeLockProvider` (`concurrent_providers/native_impl.rs:858+`), which stores
the interpreter's `Value` directly in a `parking_lot::Mutex<Value>`/`RwLock<Value>`
with no `RuntimeValue` conversion — `text` round-trips correctly under that
backend. This was NOT wired into the shipped fix: flipping the global
concurrency backend from inside a leaf spec/library file is a process-wide,
non-local side effect (it would change Map/Channel/Thread backend behavior for
every other spec sharing the process too), out of scope for a guard-API rewrite
and risky to land without its own review.

## Impact

Any `Mutex`/`RwLock` protecting a `text` value (or any struct/class/enum/array
that isn't routed through the heap-tagged-`Int` path) silently loses its data
under the default backend — independent of whether the caller uses the
guard-pattern (`with_lock`/`with_read`/`with_write`) or the raw
`lock()`/`unlock()` API. `i64` (and presumably `f64`/`bool`, unverified) are
unaffected.

## Fix direction

Either:
1. Implement `Value::Str -> RuntimeValue` properly (box the string on the heap
   as the comment suggests, "create RuntimeString"), and the corresponding
   `RuntimeValue -> Value::Str` unboxing in `runtime_to_value`; or
2. Make `PureStd`'s mutex/rwlock/atomic paths delegate to `registry.lock`
   (`StdLockProvider`) unconditionally instead of only when backend `!=
   PureStd` — `StdLockProvider::mutex_new` itself just calls back into the same
   buggy `rt_mutex_new_fn`, so `StdLockProvider` also needs to stop routing
   through the lossy `RuntimeValue` bridge, not just be called more often.

Either fix is Rust-runtime work in `src/compiler_rust/`, outside the `.spl`
guard-lane files this bug was found while working on.

## Related

- `any_typed_closure_param_destroys_value_2026-07-28.md` — a different, already
  retracted `Any`-typed-closure-parameter bug in the *guard API signature*; that
  one is now fixed by making `with_lock`/`with_read`/`with_write` generic over
  `T`. This bug is underneath that fix, in the extern SFFI bridge, and is
  unaffected by the generics rewrite.
- `interpreter_extern/atomic.rs:486-527` (`value_to_runtime`/`runtime_to_value`)
- `concurrent_providers/native_impl.rs:858+` (`NativeLockProvider`, unaffected)
