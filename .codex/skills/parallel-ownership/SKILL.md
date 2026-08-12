---
name: parallel-ownership
description: Apply Simple owner-result parallelism and storage-layout safety when working on tasks, actors, threads, processes, GPU/device work, ownership transfer, bounded mailboxes, deterministic commits, or AoS/SoA/AoSoA decisions.
---

# Parallel Ownership

1. Name the owner of canonical mutable state and each execution domain.
2. Classify boundary data as copy, frozen share, owned move, scoped loan, handle, encoded payload, or lease.
3. Prefer child-created results and owner-side validation/commit.
4. Reject raw pointers and unknown dynamic transport at safe external boundaries.
5. Treat unknown access ranges as overlapping; preserve ABI-pinned layouts.
6. Require bounded transport and deterministic commit where the resolved policy requires them.
7. Verify move invalidation, cancellation, real transport isolation, and layout parity before claiming support.

Read `doc/04_architecture/language/parallel_ownership_model.md` and use the common contract modules before changing a runtime or compiler leaf.
