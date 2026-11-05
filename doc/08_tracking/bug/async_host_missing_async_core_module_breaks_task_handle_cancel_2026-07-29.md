# Bug: `std.async_core` module does not exist — the whole async_host task-handle/cancel family is unbuildable

- **Date:** 2026-07-29
- **Status:** open (one contributing bug fixed this session; the module gap itself is
  a design decision, not fixed)
- **Severity:** CRITICAL — an entire documented API surface (task handles with
  join/abort/cancel, `JoinSet`) cannot be constructed at all
- **Found by:** lane G9 (mission-critical robustness campaign — cancellation semantics)

## Symptom

`src/lib/nogc_async_mut/async_host/handle.spl`, `joinset.spl`, `runtime.spl`,
`combinators.spl`, `unordered.spl`, `worker_thread.spl`, `future.spl`,
`scheduler.spl`, `promise.spl`, plus `async_host.spl`, `async_unified.spl`, and
`async_embedded.spl` at the parent tier all do:

```
use std.async_core.{AsyncError, CancellationToken, Poll, Priority, TaskState}
```

`std.async_core` **does not exist** — there is no `async_core.spl` anywhere in the
tree (confirmed: `find src/lib -iname "async_core*"` returns nothing). A comment in
`async.spl:55` even points at a specific expected location
(`src/lib/nogc_async_mut/async_core.spl`) that was apparently never created.

Constructing the documented types fails immediately:

```
use std.async_host.handle.{HostTaskHandle}
# constructing anything touching AsyncError/TaskState:
error: semantic: variable `TaskState` not found
error: HIR lowering error: Unknown type: AsyncError
```

`CancellationToken` happens to resolve anyway (there is exactly one class with that
name reachable, in `std.async.cancellation`), which is why
`HostTaskHandle.cancel()`/`HostJoinSet.cancel_all()` look plausible on read but are
actually unreachable — `TaskState`/`AsyncError` fields on the same classes fail first.

## Why no test caught this

`test/01_unit/lib/nogc_async_mut/async_host_spec.spl` never imports or constructs any
of these types. Every `it` block does `rt_file_read_text("src/lib/nogc_async_mut/async_host/" + path)`
and asserts `src.contains("class HostTaskHandle<T>")`,
`src.contains("me cancel()")`, etc. — a string-match over the source text, not a
build or a call. It reports 7/7 green while the module cannot be compiled.

## Contributing bug fixed this session

`async_host/joinset.spl`'s `HostJoinSet.add_task()` calls `task_alloc_id()` but never
imports it (the real definition lives in `std.async_sffi`, already imported correctly
by `src/lib/nogc_async_mut/async/task.spl`). Fixed by adding
`use std.async_sffi.{task_alloc_id}` to `joinset.spl`. This alone does not make the
file buildable — it still fails on the missing `TaskState`/`AsyncError`/`Priority`
imports from the nonexistent `async_core` module.

## Also fixed this session (unblocks `CancellationToken.new()` calls specifically)

`async_host/handle.spl` and `joinset.spl` both construct via
`CancellationToken.new()`, but `std.async.cancellation.CancellationToken` had no
static `new()` method (only a free function `token_new()`). Added
`static fn new() -> CancellationToken` to the class (delegates to `token_new()`). This
call now resolves; it does not by itself fix the `async_core` gap above.

## Why this is not fixed here

Creating `async_core.spl` requires deciding which of the *already-existing, divergent*
definitions of `TaskState` (in `async/task.spl`, `async/runtime.spl`, `async/poll.spl`,
and `mcp/tasks.spl` — 4 separate `TaskState`-shaped types were found; not verified
identical), `AsyncError`, `Priority`, and `Poll` become canonical, whether the other
call sites get migrated to import from the new module or the new module re-exports
from wherever the "real" ones already live, and what happens to the ~10 files across
`async_host/`, `async_unified.spl`, and `async_embedded.spl` that all assume a single
shared surface exists. That is a design decision (which lane/owner consolidates the
type family) explicitly out of scope for this lane's decision-free mandate.

## Scope / blast radius

- Affects: `async_host/handle.spl`, `joinset.spl`, `runtime.spl`, `combinators.spl`,
  `unordered.spl`, `worker_thread.spl`, `future.spl`, `scheduler.spl`, `promise.spl`,
  `async_host.spl`, `async_unified.spl`, `async_embedded.spl` (all reference
  `std.async_core`).
- The only real, working cancellation primitive in the tree remains
  `std.async.cancellation.CancellationToken` (now spec-tested; see
  `test/01_unit/lib/nogc_async_mut/cancellation_spec.spl` and the two related bug
  docs on its own defects). None of the `async_host` "task handle" cancellation API
  is usable until `async_core` is created.

## Suggested next step

A design/architecture decision: pick the canonical `TaskState`/`AsyncError`/
`Priority`/`Poll` definitions (or write new ones), create `async_core.spl` re-exporting
them, and re-verify each of the ~12 dependent files actually compiles and constructs
(not just string-matches) via real specs — mirroring
`test/01_unit/lib/nogc_async_mut/cancellation_spec.spl`'s approach of importing and
calling the real module instead of grepping its source text.


## Update 2026-11-05 (work/libbug-async-core-20261105) — module created; task-handle/cancel dispatch fixed

`std.async_core` now resolves: `src/lib/nogc_async_mut/async_core.spl` exports
`AsyncError`, `Priority` (new canonical definitions) and re-exports `Poll`
(`std.async.poll`), `TaskState` (`std.async.task`), `CancellationToken`
(`std.async.cancellation`). The async_host task-handle/cancel family builds and
its dispatch path works end-to-end:

- **Root cause found (closure ABI, not module resolution):** a closure whose
  body contains an ANY-typed call (e.g. a generic task body `f() -> T`) or
  whose return row is an enum/ANY (`Poll<()>`) is unencodable on the JIT
  closure ABI; the enclosing function is demoted to the interpreter, where
  stored closures no longer dispatch (the scheduler polled tasks, the poll
  matched neither `Ready` nor `Pending`, and the task stuck in `Running`).
  Fix: scheduler thunks are now `fn() -> i64` (1 = Ready, 0 = Pending);
  `HostRuntime.run_task` routes the generic call through a free helper
  (`_host_run_ready`) so the lambda body stays encodable. Cleanup actions are
  likewise `fn() -> i64`.
- `HostTaskHandle.is_cancelled()` now derives from the lifetime token (a live
  class reference) instead of the cached `context.cancellation_requested`,
  which reads stale through the snapshot the hybrid engine hands back.
- Evidence: `async_host_handle_cancellation_contract_spec.spl` 2/2 (was 0/2,
  header said "Expected-red … UNRUN"); owner_thread_queue 5/5,
  task_error_surfacing 18/18, async_host 7/7, cancellation 8/8, async 10/10,
  atomic_map OK — all on the real modules.

**Remaining open (NOT fixed here, seed-level):** `async_mutex_suspend_spec`
(12/15 red), `async_host_handle_cleanup_contract_spec` (7/8 red) and
`host_promise_terminal_spec` (3/3 red) still fail. Minimal repros show the lib
logic is correct when it compiles wholesale to JIT; the failures come from the
filed seed hybrid-engine bug (class instances ferried between JIT-compiled and
interpreted functions come back as stale snapshots — field writes on
`task_context().unwrap()` results are lost; same class of bug documented for
cancellation 2026-07-29), plus one missing seed extern
(`spl_condvar_create`) and one nil-lease edge in `sync.spl`
(`mutex_lifetime` on nil in the 65-sequential-locks test). Fixing those needs
the seed interpreter/compiler fix, not more lib work.
