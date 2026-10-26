# Cross-module symbol collisions: ThreadHandle, token_new, timestamp_* (2026-10-26)

Phase-4 seed lane reported collisions. Findings: genuine duplicate top-level
definitions in different stdlib modules (not a missing module path in a mangled
name). The compiler already warns
`public function X has N co-compiled definitions ... mangled $dupN variants
... falling back to the last definition [compiler_cross_module_private_symbol_collision]`:
same-name definitions are co-compiled and resolved by arg type, so identically
typed or class-typed duplicates resolve to whichever is last.

## ThreadHandle (FIXED here)
- `src/lib/nogc_sync_mut/concurrent/thread.spl` (canonical; fields handle, joined; join() -> i64?)
- `src/lib/nogc_async_mut/thread_sffi.spl` (different layout; join() -> bool) was a second `class ThreadHandle`
  re-exported from `nogc_async_mut/__init__.spl` while `nogc_async_mut/concurrent/thread.spl` re-exports the canonical one.
Fix: thread_sffi class renamed `OsThreadHandle` (users: thread_pool.spl, __init__ export).
Spec: test/01_unit/lib/nogc_async_mut/thread_handle_unique_spec.spl.

## token_new (OPEN)
`src/compiler/10.frontend/core/types.spl:172` (`token_new(kind,span_id,value)->i64`) vs
`src/lib/nogc_async_mut/async/cancellation.spl:37` (`token_new()->CancellationToken`),
the latter imported by `compiler/80.driver/cache/pinned_archive_capability.spl` and
test/01_unit/lib/async/async_primitives_spec.spl. Proposed: rename the cancellation one to `cancellation_token_new`.

## timestamp_* (OPEN)
Duplicates with differing signatures (i32 vs i64) across `common/time_utils.spl`,
`nogc_sync_mut/sffi/time.spl`, `nogc_sync_mut/io/time_ops.spl`
(timestamp_add_days, _diff_days, _from_components, _get_*), plus `timestamp_now` x3
and `timestamp_to_iso` x4. Proposed: dedupe to `common/time_utils.spl` and import.
