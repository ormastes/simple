# TODO: BuildRunner lazy snapshots and source-read cache

Status: proposed implementation work; no runtime changes made.
Requested: 2026-10-05. Scope: small hidden snapshot commits for builds.

Design: [Pseudo snapshot: BuildRunner file-read cache](../04_architecture/pseudo_snapshot_build_runner.md).
Tracking: [snapshot/performance follow-up](../08_tracking/todo/build_runner_snapshot_perf_followup_2026-10-05.md).

## Intended flow

- [ ] Begin with the existing committed tree and a private build snapshot ref.
  Use a private index or equivalent content manifest. Never stage files in the
  user's index or change the user's branch, HEAD, or working files.
- [ ] BuildRunner discovers staged, unstaged, and relevant untracked inputs,
  plus deleted paths. Treat working-tree bytes as the compiler input even when
  a path also has a different staged version. Avoid copying the entire tree.
- [ ] Capture changed source bytes on first compiler read, store them as
  immutable content objects, and record the path-to-content mapping. Add and
  create a small hidden commit for each newly encountered file version absent
  from the snapshot. Repeated reads and unchanged baseline files add no commit.
- [ ] Verify the compiler source-provider boundary and implement missing
  routing so BuildRunner owns the source-read cache. Compile the exact immutable
  buffer returned by that provider; do not reread the mutable path after hashing
  it. Existing complete provider support has not been verified by this plan.
- [ ] Reuse captured bytes for repeated reads in the same build. Changes after
  capture belong to the next build; a file changing during capture is retried
  or reported as unstable, never silently accepted as mixed content.
- [ ] Route import resolution, configuration reads, generated inputs, directory
  discovery, and relevant missing-file checks through the same input authority.
  Record deletion and discovery dependencies so cache reuse remains valid.
- [ ] Have workers publish content-addressed objects and immutable results to
  one manifest/commit owner. Serialize per-file commits and bound cache memory.
  Record their hashes in an ordered build ledger. A crash
  must leave recoverable objects without declaring an incomplete build valid.
- [ ] Permit delayed background snapshot commits while compilation uses pinned
  immutable buffers. Delay alone must not expire a valid captured input. Keep
  buffers pinned until durable storage succeeds; apply backpressure rather than
  allowing an unbounded pending-write queue or silently dropping input bytes.
- [ ] Use one capture operation per path/build generation with concurrent readers
  sharing the same immutable result. Specify atomic-save/cooperative-write
  guarantees for unversioned files; do not label thread safety as filesystem
  snapshot isolation or rely on timestamp checks to exclude all torn reads.
- [ ] Finalize a snapshot manifest identifying every input actually consumed.
  At build completion, squash the recorded capture commits into one hidden
  commit parented to the pinned baseline, using stored trees/objects rather
  than rereading the working tree. Preserve the intermediate hash list and
  retain its hidden chain ref according to the diagnostic retention policy.
  Bind build artifacts to that final commit, manifest, and compiler/options identity.
  Do not publish reusable artifact success while its input set is incomplete.

## Consistency and cache rules

This is a first-observation snapshot: each input is frozen on its first read.
It is not a claim that all files reflect the same build-start instant. If that
stronger guarantee is required, add filesystem snapshotting or validated
change tracking. For compilers without a source-provider interface, use an
immutable materialized input tree or report the unsupported mode explicitly.

Reuse committed blobs when the working-tree input is verified unchanged.
Do not trust a path, size, or timestamp alone as proof of content equality.
Use content identity for durable cache keys; include configuration, compiler,
target, and dependency identities. Keep transient read caching distinct from
artifact validity. Define how Git filters and line endings map to the actual
bytes seen by the compiler.

## Acceptance work

- [ ] Reproduce current snapshot delay and measure discovery, reads, hashing,
  materialization, subprocess startup, and lock waits independently.
- [ ] Test staged-only, unstaged-only, staged-plus-unstaged, untracked, deleted,
  renamed, binary/NUL-containing, and line-ending-sensitive inputs.
- [ ] Test concurrent edits, same-size/timestamp changes, atomic replacement,
  repeated reads, simultaneous workers, interrupted commits, and recovery.
- [ ] Test one commit per new captured file version, duplicate-read suppression,
  ordered concurrent publication, commit/ledger crash windows, missing objects,
  garbage-collection protection, and repeatable final consolidation. Verify
  that the final tree reproduces the capture chain and ignores later edits.
- [ ] Verify compiled bytes equal recorded bytes, missing imports invalidate
  correctly, and snapshots never alter the user's index or working tree.
- [ ] Measure cold/warm latency, total build time, peak memory, and cache hit
  counts. Target warm snapshot startup below ten seconds on the representative
  repository; measure rather than promise the result. Unchanged-input startup
  must avoid full-tree content reads, copies, and hashes.

Open integration choice: private Git refs/index versus the existing SCV object
store with a small Git-compatible commit manifest. Reuse the existing storage
owner where practical; do not introduce a second snapshot authority.
