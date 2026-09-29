# SOSIX route manifest v1: async completion family

Status: **partial RU-001 census**. Source baseline is `0161471e4cf` on
2026-09-26, plus the hosted FS direct-poll edit in this lane. This is a route
inventory, not evidence that one Future ABI, scheduler, or SimpleOS release is
qualified. The positioned file I/O family is separately inventoried in
`sosix_route_manifest_v1_2026-09-26.md`.

## Route keys

| Key | Profile and owner | Completion route |
|---|---|---|
| L | Legacy no-GC async API, `src/lib/nogc_async_mut/async/` | `Future<T>` stores a `Poll<T>` snapshot; `Task`/`Executor` are separate. |
| H | Hosted async API, `src/lib/nogc_async_mut/async_host/` | `HostFuture<T>` holds state and wakers; `HostPromise<T>` writes it. |
| S | Hosted SOSIX FS, common contracts plus `src/lib/nogc_async_mut/sosix/fs.spl` | One `SimpleRing` token and operation slot; `TaskPollResult<T>` names the live wait token. |
| O | SimpleOS async API, `src/os/async/` and service/device implementations | `OsFuture<T>` uses `OsWaker`/`OsPoll<T>`; no proven bridge to S. |

## Classified symbols

Signatures omit method receivers. A named caller is a source-confirmed example,
not a complete transitive call graph.

| Symbol and source | Signature; caller → owner → route | Disposition and missing evidence |
|---|---|---|
| `Future<T>.poll`, `src/lib/nogc_async_mut/async/future.spl` | `() -> Poll<T>`; legacy `Promise` examples and `future_compat_adapter.spl` → legacy Future → L | Keep compatibility during migration. `poll` reads stored `poll_result`; it has no operation-owner lookup or waker. At the committed baseline, pending `map`/`then` return detached pending futures. |
| `Promise<T>.new/complete`, `src/lib/nogc_async_mut/async/promise.spl` | `new() -> (Future<T>, Promise<T>)`; `complete(T) -> bool`; public `std.async.promise` consumer → L | Committed baseline returns a separate pending future and only toggles `completed`, so it does not publish the value. No qualified task wake or retirement bridge exists. Track in `doc/08_tracking/bug/std_async_promise_pair_never_publishes_2026-09-26.md`. |
| `Task.new<T>` and `Executor.run_iteration`, `src/lib/nogc_async_mut/async/{task,executor}.spl` | `new(fn() -> Future<T>) -> Task`; `run_iteration() -> ()`; `Executor.spawn` → legacy task queue → L | `Task` stores the future's opaque `state` bytes; `run_iteration` marks a scheduled task completed without polling a live future. This cannot serve as the SOSIX task/retirement owner. |
| `HostPromise<T>.complete` and `HostFuture<T>.poll`, `src/lib/nogc_async_mut/async_host/{promise,future}.spl` | `complete(T) -> bool`; `poll(Context) -> Poll<T>`; hosted runtime/join consumers → hosted future/waker owner → H | Pair shares a `HostFuture` and calls its wakers. Pending `HostFuture.map/then` construct new pending futures without a subscription to the source, so chaining parity remains open. Do not alias H to S by name alone. |
| `AsyncTaskFrame` / `StacklessAsyncTask<T>.poll`, `src/lib/common/contracts/execution/simple_ring_async_v1.spl` | `(AsyncTaskFrame, TaskContext) -> TaskPollResult<T>`; typed ring task contracts → common owner → S | Contract vocabulary only; it does not allocate a frame, schedule a task, or prove a Future bridge. `Pending` carries a `RingToken`. |
| `SosixHostedFs.result_of/poll`, `src/lib/nogc_async_mut/sosix/fs.spl` | `(SosixOperationId) -> Result<SosixCompletion,SosixError>?` / `-> TaskPollResult<Result<SosixCompletion,SosixError>>`; hosted FS consumer → ring/operation owner → S | `poll` now consults the live operation slot and returns the exact retained token while pending; `pump` owns terminal publication and lease retirement. Existing `fs_async_spec.spl` covers pending-to-ready, stale ID, timeout, and release; this edit still needs a source-matched run. |
| `SosixHostedFs.future_of`, same source | `(SosixOperationId) -> Future<Result<SosixCompletion,SosixError>>`; no remaining source caller found → compatibility snapshot → L/S boundary | A returned pending Future is a snapshot and will not update on later ring completion. The live `poll` path no longer uses it. Retain compatibility until an explicit operation-backed Future API can replace it without a second owner. |
| `SosixCompletionQueue.publish/take`, `src/lib/common/contracts/sosix/completion_v1.spl` | `(SosixCompletion) -> bool` / `() -> SosixCompletion?`; `SosixHostedFs.pump/take_completion` → bounded typed queue → S | Bounded publication can reject on full queue; provider/consumer evidence must show overflow handling, exact wake, terminal result, and separate physical retirement. |
| `OsFuture<T>.poll`, `src/os/async/os_future.spl` | `(OsWaker) -> OsPoll<T>`; VFS, NVMe, and virtio device implementations → SimpleOS service/device owner → O | SimpleOS has a separate trait and waker vocabulary. No verified adapter binds its completion to `AsyncTaskFrame`, SOSIX operation IDs, or the hosted ring ABI. Keep native device owners while designing that bridge. |

## Unresolved route and promotion gates

1. Define one owner-backed result slot and generation-qualified wake/retirement
   bridge for L/H/O consumers; do not publish a value merely by toggling a
   Promise flag or fabricate `Ready` after scheduling.
2. Decide whether `future_of` remains snapshot-only or gains an explicit live
   operation handle. A pending snapshot cannot be promoted as a task-backed
   Future.
3. Prove cancellation, deadline, queue overflow, partial effect, terminal
   publication, and physical lease retirement in each admitted provider.
4. Run the focused Promise/hosted FS/OS task tests with an admitted pure-Simple
   runner, then live SOSIX QEMU routes and SimpleOS guest evidence. Source
   presence and the existing model tests do not close RU-021 or the release.
5. Continue RU-001 with interpreter dispatch, loader imports, render/host
   calls, and the remaining service registry; this family is not the global
   census.
