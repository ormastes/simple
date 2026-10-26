# TODO: pseudo snapshot and BuildRunner file-read cache

Status: OPEN — documentation only; implementation and native tests pending.
Related historical issue: snapshot performance TODO 347, referenced by the
drift-digest candidate `60a32d045e8`. This document does not alter that issue's
database state or claim its existing fix is verified.

Design: [Pseudo snapshot: BuildRunner file-read cache](../../04_architecture/pseudo_snapshot_build_runner.md).
Plan: [implementation checklist](../../03_plan/build_runner_lazy_snapshot_todo.md).

- [ ] Audit the compiler read boundary; implement BuildRunner provider routing
  and test that compilation never bypasses it for recorded inputs.
- [ ] Reproduce slow snapshot acquisition, attribute its phases, and compare
  equivalent private Git add/commit work with the existing SCV path.
- [ ] Implement per-generation, per-path single-flight immutable read caching.
- [ ] Capture unstaged/untracked contents lazily and reconcile staged versions,
  creation, deletion, generated inputs, and discovery dependencies.
- [ ] On encountering each new file version absent from the snapshot, add its
  captured bytes and create one small hidden commit. Suppress repeated-read
  commits; bound background publication and preserve the user's Git state.
- [ ] Maintain an ordered list of capture commit hashes for the running build,
  with crash-safe publication and hidden refs protecting the capture chain.
- [ ] At build completion, consolidate captured changes into one final hidden
  commit without rereading working files. Preserve intermediate hashes for
  provenance and finalize the dependency manifest before artifact publication.
- [ ] Reproduce concurrent read/write races, delayed commit workers, queue
  saturation, crash/recovery, and cache invalidation failures before repair.
- [ ] Add prevention tests for same-size/same-timestamp edits, atomic replacement,
  untracked deletion/recreation, repeated parallel reads, NUL bytes, CRLF/Git
  filters, different source roots, and edits across related source files.
- [ ] Verify that compiler-consumed bytes equal snapshot bytes, and that delayed
  background publication does not change already captured input versions.
- [ ] Verify final tree equivalence, no duplicate capture commits, interrupted
  ledger/commit recovery, garbage-collection safety, and idempotent finalization.
- [ ] Measure warm startup, first-source latency, total build/finalization time,
  work per changed file, peak RSS, and queue high-water marks. Target warm
  snapshot startup below ten seconds on representative inputs without hiding
  cost in unbounded background work or weakening documented consistency.

Acceptance requires measured performance improvement plus native correctness
and memory regression evidence. A thread-safe cache alone is insufficient
proof of coherent reads against arbitrary external in-place file writes.
