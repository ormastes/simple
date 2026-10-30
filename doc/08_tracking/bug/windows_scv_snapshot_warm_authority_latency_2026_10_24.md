# Windows SCV snapshot authority misses the two-second target

Status: OPEN. Target: complete snapshot acquisition in at most 2 seconds with
cache enabled by default. This is a performance requirement, not a demonstrated
result or a claim that the target is impossible.

The retained Phase 3 attempt spent approximately 6m51 before source inventory
publication and another 4m55 before the requested snapshot was published. It
then reached parser progress in approximately 24 seconds. The attempt ended at
its normal 6 GB RSS guard without producing an object. System commit shortage
was subsequently observed despite plentiful physical RAM; timing attribution
must account for that host condition.

Component diagnostics measured alias parsing at 895 ms for 102034 rows and
canonical inventory decoding at approximately one second for 42604 rows.
Those diagnostics were compiled by the provisional Phase 2 compiler, whereas
that compiler's startup code has a different producer lineage. They cannot
exclude a producer-specific performance defect or establish whole-owner time.

## Concrete unsafe shortcut

`src/lib/scv/compile_snapshot.spl:188` physically canonicalizes selected live
paths before the exact-revision reuse check at approximately `:634`.
Moving this gate below an early cache-hit return would change admission:

1. Acquire an owned source symlink targeting a checkout-owned file and publish
   a valid snapshot.
2. Retarget the source symlink to a file outside the checkout containing
   identical bytes.
3. All content and semantic facets remain identical. The inventory reducer
   returns `ok-no-change`, so the same planned snapshot revision still exists.
4. The current physical containment check rejects the outside owner. A pure
   Git/content cache shortcut could return the old snapshot before observing
   the changed ownership and admit an invocation the current gate rejects.

Windows parent junction retargeting can similarly change a selected file's
physical owner without producing a tracked Git leaf-mode change. Fresh Git
HEAD, index and dirty-status observations alone do not replace that proof.

## Rejected source-copy shortcut

Copying a verified canonical chunk instead of the previous snapshot file is
also not a behavior-preserving hash optimization. Existing per-file tests
require a miss for a corrupt previous copy. The acquire regression "fails
closed when a tampered copy's fallback finds a drifted source" in
`test/01_unit/lib/scv/compile_snapshot_revision_reuse_acquire_spec.spl` requires
failure after corruption plus a same-length unpublished working-source edit.
Canonical-chunk copying would succeed in that case. Keeping a hash of the old
copy preserves the current oracle but eliminates the proposed hash saving.
No implementation or regression oracle was changed to conceal this difference.

## Safe next work

- Complete the prepared 50/500/5000-file native operation projection, separating
  path resolution, byte reads, SHA/UTF-8, directory creation, chunk publication,
  destination copy/readback, drift checks and scope overhead.
- Measure exact unchanged snapshot reuse and actual final-artifact restoration
  end-to-end with one immutable producer and normal commit/RSS admission.
- If per-path resolution dominates, design per-invocation native batch
  validation or a trustworthy filesystem/alias/reparse journal witness. Keep
  source and metadata corruption checks, ownership and all positive/negative
  macro/aspect/generated-input dependency authority.
- Evaluate the smaller directory-creation cache
  only against measured operation costs. Do not remove SHA-256 or containment
  checks merely to reach a timing target.

The detailed bounded proposal is
`doc/05_design/scv_snapshot_fast_reuse_2026_10_24.md`.
Native evidence is retained at
`C:/dev/simple-scv-commit-fast-storage-20261024/evidence/component-baselines.sdn`.
The operation probe has not executed: its bad redundant source selector is
identified, and retry awaits sufficient system commit headroom. No production
cache admission rule has changed.
