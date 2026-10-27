# SCVN-B03 storage implementation lane

Owner: `/root/impl_storage` (Codex, parent-guided SCV implementation).
Session/worktree: `/tmp/simple-scv-impl-storage-20261027`.
Branch: `work/scv-impl-storage-20261027`.
Base: `25cdeee5d5da8f8c7c3ab530d43bc2fd4a360d26`.
Integration target: `release/1.0.0`; parent owns integration and landing.

Scope: typed missing-read failures, bounded read-once capture, atomic byte
publication and actual SCV capture/diff/integrity callers. No compiler, app
entrypoint, configuration/schema contracts, or shared witness formats.

Runtime checks, tests and doc generation: **not_run**; no qualified native
runtime is currently provided. Rust-seed fallback and bootstrap are prohibited
for this lane. Source implementation alone does not complete SCVN-B03 or the
full SCV goal. Directory fsync, transactional multi-file root publication and
WAL durability require separate qualification; per-file sync/rename does not
establish them.

## Implemented source

- Canonical checked file identity and Result-returning compatibility name;
  direct production callers migrated, including shadow comparisons, parser
  install/verification, structural capture, diff/status and integrity checks.
- Existing FileBuffer uses the canonical regular/no-follow bounded-byte
  provider. It rejects failed reads, invalid bounds, post-read excess/length
  drift, and failed-buffer identity/publication. Symlinks fail explicitly.
- Atomic binary facade, byte chunk verification/deduplication, checked object
  publication, and no non-atomic text fallback. Restore/export/import paths
  preserve captured bytes and reject failed reads/writes.
- Snapshot checks its WAL/object/root/index/event acknowledgements; WAL begin
  publishes a complete recovery record in one write, partial root failures stay
  pending, recovery does not acknowledge its failed writes.
- Existing oversized owners split with explicit compatible exports: structural
  values/source adapter, checkpoint integrity, stored-block gzip.
- Ten real-file unit regressions and four real-file snapshot system regressions
  authored; prior FileBuffer integration callers migrated to Results.

## Evidence and limits

Runtime/unit/system/core checks, SPipe docgen, sspec-maintain and native smoke:
**not_run** (qualified runtime unavailable; no seed fallback or bootstrap).
The two manual mirrors are explicitly authored/pending, not generated passing
evidence. Static diff review is source review only. No coverage percentage,
performance or operational qualification is claimed.

Static evidence: `git diff --check` passes after fixing one trailing blank
line; the mandated `doc/06_spec` executable-spec count is `0`. An authored
source-symbol comparison preserves all original top-level names in the three
split owners. All modified `.spl` files are below 800 lines. The fourteen new
scenario bodies contain no placeholder-pass idioms. None of these observations
establishes parser/type/runtime correctness.

Full SCVN-B03 remains pending. In particular, no parent-directory fsync was
added; per-file atomic replacement does not prove power-loss durability or an
atomic multi-object root. Mutable change pointers are still written before
snapshot WAL begin; repository-wide multi-writer serialization and transaction
boundaries require further work. Legacy metadata reads still use absence/error
conflating facades outside the migrated WAL/capture paths, and many callers of
the bool text-write facade elsewhere in SCV still ignore failures. Warm status
retains its pre-existing same-stat event optimization; frozen inventory and
watcher completeness belong to subsequent capture work. No B03 done mark,
verify PASS, release, push, PR or merge is claimed by this source candidate.

## Frozen-candidate review corrections

Reviewed source: `bba564c2185c64bdf828cd0704629f7f3ad3aa6f`.
Reviewer: parent Astra `astra_storage_tldr_review`; review is source-only.

Two P1 findings required a follow-up source candidate before integration:

1. Annotated-tag import did not check a failed tag-object write before updating
   lightweight and annotated references. The importer now returns that failure
   before either write. All reference setters check text-write outcomes;
   annotated setters also reject error text/unsafe/missing object references.
2. The new byte publisher borrowed predictable destination `.tmp` and `.lock`
   paths, which could overwrite/delete unrelated files during restore/export.
   It now uses the existing typed secure-temp-directory owner (exclusive
   private stage in the same parent), exclusively creates its own payload,
   writes/syncs/renames it, and cleans only owned staging paths. It touches no
   destination lock neighbor. The original text-atomic metadata protocol is
   unchanged; no generalized migration of that existing protocol is claimed.

The byte staging fault fixtures now obstruct the actual staging parent rather
than assuming a fixed `.tmp` pathname. Added four restore/export scenarios
(success and replacement failure, retaining both valuable neighbors) and four
annotated-tag/reference integration scenarios. There are now twenty-two
authored regressions across the three new specs, plus the migrated legacy
FileBuffer integration spec. Execution/docgen/core checks remain **not_run**.
Parent-directory fsync, multi-root transactions and full B03 acceptance remain
pending. This follow-up corrects the two findings in source; it does not claim
runtime acceptance or release admission.

Follow-up static source review: `git diff --check` passes; eleven paths are
changed/added; no modified `.spl` exceeds 800 lines. The tag-object error check
precedes both reference calls. The byte publisher references neither FileLock
nor `atomic_temp_path`, and uses the typed private-stage facade. Scenario
counts are unit 10, system 8, integration 4; no placeholder passes were found.
These checks are source inspection, not executed behavioral evidence.
