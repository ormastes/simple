# macOS scalar TLS shares a symbol with tagged generic TLS

## Reproducer and impact

`src/lib/nogc_sync_mut/runtime/thread_local.spl` declared
`rt_thread_local_get/set` with raw `i64` values for allocator and probe slots.
The hosted Rust provider instead uses `RuntimeValue` for those same C symbols;
an unset slot returns tagged `NIL`, not raw zero. Reading it as a scalar can
alias a valid slot identifier, and calling its setter as raw `i64` crosses an
incompatible ABI. The interpreter provider previously returned raw zero for
the same generic symbol, so interpreter behavior did not expose the native bug.

## Scoped fix and acceptance

- Keep `rt_thread_local_get/set` as tagged `RuntimeValue` operations for
  generic `ThreadLocal<T>`, with `NIL` on an unset/invalid handle.
- Add `rt_thread_local_get_i64/set_i64` for raw scalar clients, with zero on
  an unset/invalid handle and full-width `i64` round-trips.
- Keep the two value namespaces separate even when a handle is shared, and
  preserve per-thread isolation and free behavior.
- Route the no-GC scalar owner through the new symbols; the allocator's own
  slot-zero reservation is tracked in draft PR #1404.

Focused native Rust regression: `test_thread_local_raw_i64_abi_is_distinct_and_isolated`.
The companion allocator regression is in PR #1404. Neither PR is a complete
cross-backend admission until both land and their tests pass.

The interpreter's between-run cleanup now clears both TLS maps and resets the
handle sequence, preventing retained entries across test runs. Native free
invalidates the shared handle and drops the current thread's values. Values
left in another still-live thread's private map remain allocated until that
thread exits; cross-thread reclamation is not claimed by this fix.
