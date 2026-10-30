# Interpreter: Barrier.wait() across thread_spawn_with_args never releases

- Date: 2026-10-30
- Status: OPEN
- Area: Rust seed interpreter, isolated thread spawn (`interpreter_extern/concurrency.rs`)

## Symptom

Once `rt_par_atomic_i64_is_lock_free` / `rt_par_atomic_load_i64` were registered
in the interpreter, `test/01_unit/lib/nogc_async_mut/lockless_map_i64_spec.spl`
gets past its first 8 examples (previously 1 pass / 11 "unknown extern
function" failures), then hangs in
"serves three thousand distinct keys from synchronized native requesters"
(line 187) until the runner timeout.

Minimal repro (seed interpreter, hangs; no output):

```simple
use std.nogc_async_mut.concurrent.{Barrier, barrier_new}
use std.concurrent.thread.{thread_spawn_with_args}

fn main():
    val gate = barrier_new(2)
    val h = thread_spawn_with_args(1, 2, \a, b:
        gate.wait()
        a + b
    )
    gate.wait()
    print("main passed barrier")
```

`sample` of the hung process shows the worker spinning in `thread_yield`
inside `Barrier.wait` (`src/lib/nogc_async_mut/concurrent.spl:230`): the
generation counter bumped by one side is never seen by the other. The
captured `Barrier` (its `AtomicI64` fields) is evidently not shared between
the interpreter's isolated thread and the spawner.

## Unblock condition

Interpreter isolated threads must share the atomic handles a captured
`Barrier` holds, so `lockless_map_i64_spec.spl` lines 187, 225, 257 and 292
complete. The spec is left as-is (not pending).
