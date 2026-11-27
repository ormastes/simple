# Interpreter: Barrier.wait() across thread_spawn_with_args never releases

- Date: 2026-10-30
- Status: FIXED (see Resolution)
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

## Resolution (2026-10-30)

- Status: FIXED
- Root cause: not a copied barrier. `rt_thread_spawn_isolated_with_args_context`
  evaluated the closure inline on the spawning thread and stored the result
  before returning, so the spawner never reached its own `gate.wait()`. The
  `AtomicI64` handles are process-global runtime handles and were already
  shared. lldb (`bt all`) of the hung repro showed a single interpreter thread
  (`simple-main`) in `rt_thread_yield` under
  `rt_thread_spawn_isolated_with_args_context` (frame #32).
- Fix: the closure now runs on a real OS thread (64 MiB stack) after the
  spawner's thread-local interpreter state is installed on it
  (`InterpreterThreadState`, interpreter_state.rs); `rt_thread_join` /
  `rt_thread_is_done` / `rt_thread_free` consult the worker's `JoinHandle`.
- Specs: `test/01_unit/lib/nogc_async_mut/isolated_thread_barrier_spec.spl`
  (repro + 8-worker and two-generation generalizations): old seed timeout,
  new 3/3. `lockless_map_i64_spec.spl`: hang -> 12/12.
- Follow-up (no-argument spawn): `rt_thread_spawn_isolated_with_context`
  (plain `thread_spawn`) still ran the closure inline and deadlocked the same
  way. It now shares the OS-thread path (`spawn_isolated_worker`).
  Spec: `test/01_unit/lib/nogc_async_mut/isolated_thread_spawn_barrier_spec.spl`
  (two-party + 8-worker barrier): old seed timeout, new 2/2. Assertions that
  encoded the synchronous contract (`is_done()` true straight after spawn,
  `join()` after `free()` returning the value) were updated in the perf twins
  and `concurrent_thread_lifecycle_spec.spl`.
