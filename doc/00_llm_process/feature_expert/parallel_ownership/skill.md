# Parallel Ownership Feature Expert

## Authoritative sources

- `src/lib/common/structural/transfer/`
- `src/lib/common/structural/storage_layout/`
- `src/lib/common/structural/parallel_commit/`
- `src/compiler_rust/runtime/src/value/transfer.rs`
- `src/compiler_rust/runtime/src/value/actors.rs`
- `src/compiler_rust/runtime/src/value/channels.rs`
- `doc/04_architecture/language/parallel_ownership_model.md`
- `doc/03_plan/language/parallel_memory_mdsoc_plus_parallel_agents_2026-08-12.md`

## Landed

- Frozen `TransferEnvelopeV1`, storage-layout, access-path, and parent-commit
  common contracts.
- Simple and Rust byte-compatible 40-byte `SPTR` v1 envelope codecs.
- Native 48-byte inline transfer packets; heap and reserved RuntimeValue tags
  fail closed.
- Finite 256-item native compatibility channels and actor inbox/outbox queues.
- Bounded Parent-to-Process/Process-to-Parent encoded frames with a real
  exec-child round trip.
- `ParentCommitFrameInboxV1` generation/replay admission and
  `ParentCommitPipedProcessSessionV1` single-handle, idempotent-close ownership.
- `ParentCommitOwnerV1` serialized revision/token publication after complete
  transfer/result validation.
- Common constant-size functional owner snapshot-root transition with stale/conflict/duplicate
  rejection and canonical-order batch receipts.
- Conservative dynamic-index overlap in the live borrow checker.

## Still proposed or incomplete

- Typed frozen, owned, encoded, ObjectRef, reduction, and device-lease payloads.
- Ownership-token registry, generation transitions, rollback, and receipts.
- HIR/MIR transfer operations and source invalidation in every compiler mode.
- Production-complete process/device transport, structured task groups, task
  arenas, payload-aware commit apply/verify adapters,
  and AoS/SoA/AoSoA lowering.
- Admitted self-hosted and real process/device system evidence.

## Operational rules

1. Name the canonical mutable owner and source revision.
2. Treat unknown ranges and dynamic values as conflicting/unclassified.
3. Prefer immutable input and child-created results.
4. Never serialize a process-local pointer or claim graph transfer from the
   inline packet path.
5. Require finite queues, visible failure/backpressure, deterministic commit,
   and receipt identity before critical-mode claims.
6. Do not infer a single actor authority from mailbox locking: current
   `ActorRef.send()` bypasses scheduler admission, and the scheduler is
   single-threaded. Choose a scheduler-domain restriction or one synchronized
   scheduler ingress before claiming copied-ref concurrency.
7. A caller-selected process generation bounds replay bookkeeping but is not a
   parent-issued freshness identity. Cancellation revocation, PID reuse, and
   natural-exit reap remain open until terminal receipts prove them. Track the
   work in
   `doc/08_tracking/bug/process_transfer_session_replay_identity_2026-08-12.md`.

## Focused native evidence

```text
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml value::transfer::tests
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml actor_wire_accepts_inline_values_and_rejects_heap_addresses
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml test_actor_rejects_heap_context
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml value::channels::tests
cargo test --manifest-path src/compiler_rust/common/Cargo.toml actor_handle_reports_bounded_mailbox_backpressure
```

The current self-hosted production gate is:

```text
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native
```

Do not run it until `bin/release/simple test --help` passes its bounded ABI
probe; status 139 is a deployment blocker, not a spec verdict.

Current `origin/main` has an unrelated missing `rt_io_tcp_probe_peer` re-export;
do not count a temporary isolated-worktree omission of that export as part of
parallel ownership implementation or as a clean release build.
