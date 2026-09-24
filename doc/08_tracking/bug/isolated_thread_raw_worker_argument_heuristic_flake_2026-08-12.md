# Isolated-thread raw worker argument heuristic is test-order dependent

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
2026-08-12.

`native_callable()` infers `raw_worker_args` from closure-record shape/address.
Under the broad Rust test filter `isolated_thread`, the existing scalar tests
`test_isolated_thread_spawn_with_args_and_join` and its direct-function variant
returned 5 and 36 instead of 42. Their exact behavior depends on whether tagged
integer arguments are decoded by `native_worker_arg()`.

Required correction: make worker argument ABI an explicit property of the
callable record, not an address/shape heuristic, and add deterministic tagged
and raw argument fixtures. This is separate from the heap-input gate: the five
new exact rejection/channel tests pass.

Cross-runtime companion gap: `src/runtime/runtime_thread.c` passes two worker
arguments raw and lacks the Rust runtime's registered synchronized-handle
classification. It must fail closed or consume an equivalent typed transfer
envelope before claiming isolated-thread parity.

## Triage 2026-09-13

Both halves are out of pure-Simple scope: `native_callable()`'s
argument heuristic lives in the Rust seed test/runtime harness, and
`src/runtime/runtime_thread.c` is fenced C runtime. Requires a Rust
seed rebuild (worker-ABI as an explicit callable-record property) to
fix, not reachable from a .spl/.shs change. Leaving OPEN, no attempt.

