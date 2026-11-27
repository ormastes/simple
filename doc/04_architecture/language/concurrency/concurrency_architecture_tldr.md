# Concurrency — Lockless by Default — TLDR

- Default: **lockless**. Shared state is immutable or published by CAS-style swap.
- Prefer, in order: immutable/content-addressed values → actors/message passing
  with ownership transfer → atomic CAS on small cells (pointer swap, versioned CAS,
  unique-entry append log) → per-owner private state merged at read.
- Files/IPC: write privately, then atomic rename. Use content-addressed names
  (identical content is a benign race). No in-place writes. Logs are one file
  per event. "Current" state is an atomic pointer-file swap.
- Locks only by documented exception with an owner (HAL, hardware register,
  external API). A lock must be bounded, fail closed, and never held across
  await or I/O. **A new lock without an exception is rejected in review.**
- CAS correctness: version/tag against ABA, stated lock-free/wait-free guarantee,
  explicit memory ordering, bounded retry with backoff. A CAS failure is a typed
  result, never a panic (ADR-006).
- Tests: stress and interleaving specs. Every concurrency bug is P0.
- Full doc: [concurrency_architecture.md](concurrency_architecture.md).
