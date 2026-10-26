# Pseudo snapshot: BuildRunner file-read cache

Status: design proposal, not an implemented or verified runtime capability.
Requested: 2026-10-05.

## Contract

BuildRunner owns the compiler's file-read cache and the build's input manifest.
The build starts from a committed baseline. Staged, unstaged, and untracked
working-tree content is captured when compilation first consumes it. Whenever
a newly encountered file version is not already represented in the build's
snapshot, add its captured bytes and create a small hidden commit through a
private index/ref or the existing SCV storage owner. Keep an ordered list of
these commit hashes during the build. At build completion, consolidate their
tree changes into one final hidden commit. The user's index, branch, and
working files remain untouched.

This is a first-observation pseudo-snapshot. Every captured path has one version
within a build, but different paths may have been captured at different times.
It provides repeatable reads of recorded input bytes, not a globally atomic
view of the project at build start. Compiler source-provider support must be
audited and completed; this proposal does not assert that it already exists.

## Small flow

1. Allocate a build generation and pin its committed baseline and configuration.
2. Discover relevant dirty paths without eagerly copying the entire repository.
   Discovery is a hint: reconcile created/deleted paths and later source reads.
3. On the first read, one per-path capture operation obtains the working bytes.
   Concurrent requests await that operation and receive the same immutable
   buffer. Unrelated files can be captured concurrently.
4. Compile from that exact buffer. Hash/store it once; publish a path/content
   identity and record dependency/discovery observations. Repeated reads use
   the captured bytes rather than reopening the mutable working-tree path.
5. For each newly encountered, uncaptured file version, the background writer
   adds its exact captured bytes and creates one small hidden commit. Unchanged
   baseline files and repeated reads require no new commit. Serialize commit
   publication while allowing file reads and object storage to run concurrently.
   Never reread working files to construct a commit. Use the existing object
   store/API so per-file commits do not require per-file Git subprocesses.
6. Record each published commit hash in the build's ordered snapshot ledger.
   The commit chain and ledger must be recoverable after interrupted publication.
7. When the build finishes, drain pending writes, validate the consumed-input
   manifest, and consolidate the recorded changes into one final hidden commit.
   Bind reusable artifacts to that finalized snapshot. Failed builds may retain
   a diagnostic snapshot, but must not publish successful artifact receipts.

## Commit ledger and final consolidation

The pseudo-snapshot records a baseline commit, a build generation, an ordered
list of capture commit hashes, and the consumed-input manifest. Each capture
commit extends the previous hidden commit; the single writer resolves ordering
without concurrent index mutation. A file already frozen for this build never
gets replaced by a later editor version. The next build captures that change.

Final consolidation is a squash of the captured tree changes, not a merge of
the current working tree. Create a final hidden commit parented to the pinned
baseline, with a tree equivalent to the completed capture chain and its final
input manifest. Do not copy or hash the source tree again. Keep the intermediate
hash list as provenance, and publish the final commit hash in an external build
receipt to avoid a self-referential commit identity.

Retain a hidden ref to the capture chain until the final snapshot is published
and the diagnostic retention policy permits cleanup. Merely listing hashes
does not protect intermediate commits from Git garbage collection. Recovery
must reconcile a published commit missing from the ledger and reject a ledger
entry whose object is unavailable. Repeated finalization must not duplicate
capture operations or change the compiled input versions.

## Delayed snapshot worker

A delayed commit worker does not invalidate already captured immutable bytes.
Compilation may proceed while those bytes are retained safely in the read
cache. Every uncaptured-file event remains a required commit operation even
if the worker services queued operations later. Eviction requires a durable
stored copy. Bound pending bytes and apply
backpressure when the writer falls behind; do not trade a snapshot latency bug
for unbounded memory growth. Report capture time separately from background
commit and finalization time. Moving a full-tree scan to a background thread
does not by itself remove that work or improve end-to-end build time.

## Concurrent unversioned files

BuildRunner's locks coordinate its own readers, not an editor or another tool.
Per-path single-flight capture prevents two compiler workers from observing
different versions. Atomic editor replacement can provide a coherent old or
new file through an opened handle, subject to platform semantics. Arbitrary
in-place writes can produce torn bytes; before/after size or timestamp checks
cannot prove this never happened. Establish cooperative atomic writes, suitable
filesystem read isolation, or explicitly document the weaker input guarantee.
Retry detected instability with a bound and report continuing instability.

Edits after capture are inputs to a later build. Changes across several files
can still yield an inconsistent project version in this mode. Such a build
must not be described as a build-start snapshot. A strict mode can use stronger
filesystem snapshotting or an immutable prepared tree when required.

## Complete dependency and cache identity

Route source contents, import resolution, relevant directory listings, missing
paths, configuration, and generated inputs through the same authority. Record
untracked deletion and creation, not only paths returned by the latest listing.
Bind artifacts to the finalized input manifest, compiler, target, and options.
Hash compiler-visible bytes; explicitly handle Git clean filters and CRLF so
the hidden commit cannot silently change those bytes. Reuse existing SCV
objects rather than introducing another independent snapshot authority.

## Relation to prior performance work

The earlier drift-digest candidate at commit `60a32d045e8`, documented in
`doc/10_metrics/startup/scv_snapshot_drift_digest_candidate_2026-10-05.md`, avoids
redundant hashing of identical buffers but retains the integrity reread and
materialization flow. It cites snapshot performance TODO 347 and the research
`doc/01_research/local/windows_source_snapshot_latency.md` at its historical
base. Those are historical references, not claims of current qualification.

This proposal addresses the broader eager-read/copy/publication path and is a
follow-up to that work. Preserve the deletion invariant documented in
[the untracked-deletion bug](../08_tracking/bug/scv_untracked_delete_reuses_stale_snapshot_2026-09-27.md).
The old digest optimization can coexist with this flow where still relevant.

Implementation and acceptance tasks are in the
[plan](../03_plan/build_runner_lazy_snapshot_todo.md) and
[tracking TODO](../08_tracking/todo/build_runner_snapshot_perf_followup_2026-10-05.md).
