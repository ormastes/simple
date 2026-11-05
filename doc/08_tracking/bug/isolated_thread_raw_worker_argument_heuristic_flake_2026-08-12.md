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


## Re-scope 2026-11-05 (MIR P2 family H, Opus root-cause)

**Not a concurrency race.** The only shared state on the spawn path is
`NEXT_THREAD_ID` (atomic `fetch_add`); classification is a pure function of
the closure word. Arithmetic of the original symptom: tagged 10 and 32 are
`80`/`256`; decoded raw and re-read with `as_int` they give `10>>3 + 32>>3 = 5`.
So the worker ABI was flipped to "raw" for a *real heap record address*.

**Original flake: fixed by `b6dbcaf484f` (2026-10-20).** The old x86_64-only
47-bit ceiling read aarch64 PIE/heap addresses (> 2^47) as int-tagged words;
whether a test's `Box` landed above 2^47 depended on allocator state, hence
test-order dependence. The ceiling is now per-arch (48-bit + TBI on aarch64).

**Evidence (Windows x86_64, `cargo test --lib isolated_thread`, 3 runs):**
11/11 pass each run; full `executor` filter 23/23. New specs in
`src/compiler_rust/runtime/src/executor_tests.rs`:
- `test_isolated_thread_worker_args_stress_concurrent_spawners` — 16 spawner
  threads x 32 spawns, closure + direct records interleaved, exact 42.
- `test_isolated_thread_heap_record_word_is_never_raw_abi` — 4096 live
  records, none classified as the raw ABI.
Sibling paths audited: `rt_thread_spawn_limited{,_with_args}` share
`native_callable`/`native_worker_arg` and are covered by the same rule.

**Residual defect (still OPEN): the encoding is ambiguous below 2^44.**
Repro: a record at a Windows heap address (~2^40) encoded `addr << 3` stays
under `NATIVE_USER_VA_MAX`, so `native_word_exceeds_user_va` is false, the
word is used as the record address unchanged, and the raw ABI is not
selected. A fixture asserting the tagged form failed at
`assert!(native_word_exceeds_user_va(word))` on this host. Also the C twin
diverges: `runtime_thread.c` sets `raw_worker_args = 0` for single-arg and
`= 1` for `_with_args` regardless of the word.

**Next step:** make the worker ABI explicit in the callable record (e.g. a
second marker word `NATIVE_RAW_ARGS_RECORD_MARKER` emitted by LLVM/Cranelift
codegen for natively compiled lambdas), consumed identically by Rust
`native_callable` and C `rt_native_closure_payload`; then drop the VA-ceiling
inference and add the tagged-word fixture back as a passing test.
