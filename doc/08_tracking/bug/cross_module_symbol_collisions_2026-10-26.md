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

## token_new (FIXED #4930)
`src/compiler/10.frontend/core/types.spl:172` (`token_new(kind,span_id,value)->i64`) vs
`src/lib/nogc_async_mut/async/cancellation.spl:37` (`cancellation_token_new()->CancellationToken`).
Fix: cancellation token function already renamed to `cancellation_token_new`, resolving the collision.

## timestamp_* (FIXED #4930)
Duplicates across `common/time_utils.spl`, `io/time_ops.spl`, database test modules, 
resource_utils, semihost_capture, and sffi/system stubs.
Fix: 
- Deleted 6 wrapper functions from `time_ops.spl` (timestamp_year/month/day/hour/minute/second); 
  added `pub use` re-export from time_utils (used by bug_add, test_runner, log_writer, etc.)
- Deleted `timestamp_now` stub from `test_extended/stubs.spl`; replaced with import from time_utils
- Renamed `semihost_capture.spl`'s `timestamp_now` → `semihost_timestamp_now` (different: uses semihost shell)
- Renamed database test stubs: `timestamp_to_iso` → `test_timestamp_to_iso` (in sync_mut/database/test.spl and async_mut/database/test.spl)
- Renamed mcp stub: `resource_utils.spl`'s `timestamp_to_iso` → `resource_timestamp_to_iso` 
- Kept `sffi/system.spl` timestamp functions (different: wrappers around rt_* externs, not duplicates)
