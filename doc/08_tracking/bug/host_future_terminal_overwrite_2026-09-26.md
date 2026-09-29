# HostFuture terminal overwrite and HostPromise false publication

Status: source mitigation pending executable qualification (2026-09-26).

`HostFuture.complete` and `HostFuture.fail` previously replaced an existing
`Ready` or `Failed` state and could wake registered waiters again. A
`HostPromise` also returned `true` after directly writing its paired future,
even if another alias had already resolved that future. This breaks the
single-publication behavior required of the hosted async owner while SOSIX
task/completion routes are unified.

The source change makes terminal publication single-assignment, clears an
outstanding deadline on successful publication, and makes `HostPromise`
return the paired future's result. A production-importing spec covers
duplicate completion, direct future completion followed by a promise write,
and failure followed by a value write:
`test/01_unit/lib/nogc_async_mut/host_promise_terminal_spec.spl`.

The spec has not run with a source-matched pure-Simple compiler because this
checkout has no admitted runner. Pending `HostFuture.map/then` remain detached
snapshots; a live subscription and wake/retirement bridge is still required
before hosted Future chaining can serve as the shared SOSIX task route.
