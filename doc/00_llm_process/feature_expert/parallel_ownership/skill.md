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
  `ParentCommitPipedProcessSessionV1` parent-issued generation,
  cancellation-revoke, natural-reap, and single-close-attempt receipts.
- `ParentCommitOwnerV1` serialized revision/token plus application
  payload-token-root publication after complete transfer/result/candidate
  validation, with before/after mutation receipts and atomic rollback.
- Simple `ActorRef` operations route through one admitting scheduler and fail
  closed outside its explicit OS-thread domain. The Rust provider exposes
  checked actor try-send plus cooperative, exactly-once stop: shared sender
  close wakes blocked receive, scheduler admission is removed, the worker stays
  joinable, and liveness becomes false. It retains a void send compatibility
  ABI; no C actor provider currently supplies parity.
- Common constant-size functional owner snapshot-root transition with stale/conflict/duplicate
  rejection and canonical-order batch receipts.
- Conservative dynamic-index overlap in the live borrow checker.

## Still proposed or incomplete

- Typed frozen, owned, encoded, ObjectRef, reduction, and device-lease payloads.
- Ownership-token registry, generation transitions, rollback, and receipts.
- HIR/MIR transfer operations and source invalidation in every compiler mode.
- Production-complete process/device transport, structured task groups, task
  arenas, arbitrary application-schema commit adapters,
  and AoS/SoA/AoSoA lowering.
- C/interpreter checked actor try-send/stop parity, collision-resistant process
  session identity/PID-reuse proof, stdin request framing, and graph/schema
  codecs.
- Admitted self-hosted and real process/device system evidence.

## Operational rules

1. Name the canonical mutable owner and source revision.
2. Treat unknown ranges and dynamic values as conflicting/unclassified.
3. Prefer immutable input and child-created results.
4. Never serialize a process-local pointer or claim graph transfer from the
   inline packet path.
5. Require finite queues, visible failure/backpressure, deterministic commit,
   and receipt identity before critical-mode claims.
6. `ActorRef` now uses one scheduler-owned admission/lifecycle route with an
   explicit single-thread domain guard. Do not upgrade fail-closed copied refs
   into a cross-thread concurrency claim; a synchronized ingress would still
   be required for that contract.
7. Parent-issued generation, cancellation revocation, and natural-exit reap
   receipts are landed. Collision-resistant session identity, PID reuse, and
   provider cleanup parity remain open. Track them in
   `doc/08_tracking/bug/process_transfer_session_replay_identity_2026-08-12.md`.

## Focused native evidence

```text
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml value::transfer::tests
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml actor_wire_accepts_inline_values_and_rejects_heap_addresses
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml test_actor_rejects_heap_context
cargo test --manifest-path src/compiler_rust/runtime/Cargo.toml value::channels::tests
cargo test --manifest-path src/compiler_rust/common/Cargo.toml actor_handle_reports_bounded_mailbox_backpressure
```

The current self-hosted production gates are:

```text
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/actor_channel_authority_spec.spl --mode=native
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native
```

The actor executable has the five-step same-thread scheduler-authority flow,
finite mailbox/reply backpressure, copied argument isolation, unique stop, and
closed `actor-channel-authority/v1` typed evidence. The process executable has
the frozen five-step process flow, copied-frame
isolation, typed candidate-root mutation/rollback assertions, no SKIP path, and
explicit natural-exit/close-once checks plus closed
`parent-commit-piped-result/v1` evidence. Their authored operator mirrors are
`doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md` and
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`;
the exact evidence and resume gates are in the matching focused plans under
`doc/03_plan/sys_test/`.

Do not run them until `bin/release/simple test --help` passes its bounded ABI
probe; status 139 is a deployment blocker, not a spec verdict. The authored
mirrors are not generated-manual or `sspec-maintain` PASS until those commands
run successfully on an admitted pure-Simple runtime.

Current `origin/main` has an unrelated missing `rt_io_tcp_probe_peer` re-export;
do not count a temporary isolated-worktree omission of that export as part of
parallel ownership implementation or as a clean release build.
