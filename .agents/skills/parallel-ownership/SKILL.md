---
name: parallel-ownership
description: Plan, implement, or verify Simple parallel code involving tasks, actors, threads, processes, GPU/device work, transfer, memory layout, task arenas, mailbox bounds, or deterministic parent-authoritative commit. Use when mutable state crosses execution domains or when AoS/SoA/AoSoA policy affects concurrency safety or locality.
---

# Parallel Ownership

1. Identify the canonical mutable owner for every region and snapshot revision.
2. Classify each boundary input as copy, frozen share, owned move, scoped loan, handle, encoded copy, or device lease.
3. Prefer immutable input plus child-created output; require explicit `move` for established parent-owned mutable state.
4. Reject raw pointers and unclassified dynamic values at safe process/device/remote boundaries.
5. Record read/write/reduce/create access paths. Treat unknown dynamic ranges as overlapping until a proof establishes disjointness.
6. Use bounded result transport and preserve close/backpressure/cancellation failure states.
7. Validate base revision, access conflicts, and deterministic order before the owner commits results.
8. Keep logical `T[]` semantics separate from storage layout. Pin ABI, wire, persistent, MMIO, and address-observed data; use explicit conversions for layout changes.
9. Prefer local accumulation and partitioning before cache-line padding. Record layout, transfer, and commit receipts for critical paths.
10. Verify source invalidation after move, failure/cancellation cleanup, pointer identity isolation, randomized completion determinism, and layout semantic parity with real boundaries.

## Authoritative surfaces

- `src/lib/common/structural/transfer/`
- `src/lib/common/structural/storage_layout/`
- `src/lib/common/structural/parallel_commit/`
- `src/compiler/00.common/parallel_policy/`
- `src/compiler/55.borrow/borrow_check/`
- `doc/04_architecture/language/parallel_ownership_model.md`

Do not claim runtime codec, structured task, actor/process, or backend layout support merely because a common contract exists. Check the relevant work-package gate and executable evidence.
