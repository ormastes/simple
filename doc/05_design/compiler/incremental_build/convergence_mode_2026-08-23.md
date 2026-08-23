# Two-mode stage1 build: convergence and validation (2026-08-23)

## The problem

A phase-1 build is a monolithic 6-step whole-closure run (0/6 source_closure,
1/6 parse, 2/6 hir, 3/6 typecheck+mono, 4/6 mir, 5/6 codegen, 6/6 link) that
dies and restarts from zero. run17 repeated the same 4,672s of work three times.
Worse than the cost is the blindness: the only progress signal is
"died at parse 144/689 again", which does not say *which* module, so run23 could
not pin its spin to a file at all.

## The design

Two explicitly separated modes.

**1. Convergence mode (iterate).** Rebuild only the files that failed; keep every
file that already produced an object. Loop: build -> collect the failing set ->
fix -> rebuild just that set. Repeat until every file produces an object. The
per-iteration failing-set size is the progress metric.

**2. Validation mode (clean).** Once the failing set is empty, discard all cached
state and do a clean full rebuild from scratch. **That artifact is the only one
that ships.**

## Why this dissolves the soundness blocker

Per-file HIR reuse is unsound today:
`build_surface_decl_index` indexes declaration names over every frozen surface,
and `surface_decl_owner_indices(name)` is queried by name during lowering with no
import-visibility filter, so an edit to a non-imported sibling can change what a
module lowers to while its import-closure digest stays put. 12.6% of top-level
declaration names in `src/compiler` + `src/lib` (7,206 of 57,047) are already
declared in more than one file, so the hazard is live, not theoretical. Full
evidence: `per_file_rebuild_soundness_2026-08-23.md`.

That blocker applies to **delivered artifacts**. In convergence mode the output
is *discarded* — it exists only to answer "which files still fail?". A stale
entry there costs at worst a wrong retry decision, which the next iteration
corrects and the final clean rebuild catches unconditionally. **Convergence mode
does not need sound caching; it needs cheap, monotone progress.** Validation mode
does no reuse at all, by construction.

This is why sound per-file reuse is deferred rather than blocking.

## The load-bearing part is attribution, not caching

Convergence mode is worthless if it cannot say which file failed. Two facts made
that impossible before this change:

1. **Claim markers were not invertible.** A parse shard claims a module by
   writing `{queue_dir}/{hash(path)}-{len(path)}.claim` containing only the shard
   spec (`"6/8"`). The marker *name* is a non-invertible hash, and the *content*
   held no path — so a marker could never be mapped back to a file.
2. **Reclaim destroyed the evidence.** `parse_shard_release_claims` deletes every
   marker owned by a dead shard so a retry shard can re-claim it. That is correct
   for re-claiming and fatal for attribution: a `.claim` with no cache entry
   behind it was the *only* "worker died while holding it" signal, and reclaim
   deleted exactly that.

### Landed fix

- The claim marker now carries `"<shard spec>\n<path>"`
  (`src/compiler/80.driver/driver_source_pipeline_parsing.spl`, in
  `_driver_parse_shard_claim`). Ownership has always been decided by the spec
  alone, and readers now compare only the **first line**, so legacy single-line
  markers — including ones written concurrently by an older shard binary — still
  compare exactly as before.
- `parse_shard_release_claims` (`src/app/cli/parse_shard_queue.spl`) reads the
  path out **before** deleting the marker and appends
  `status=orphaned spec=<spec> path=<path>` to `{queue_dir}/orphaned.claims`.
  The append is best-effort and never changes the released count: reclaim must
  not start failing because a ledger write did.
- `parse_shard_orphaned_paths(queue_dir)` reads the set back, de-duplicated.
  Legacy markers that recorded no path are **skipped, not reported under a
  fabricated name** — a convergence loop handed a nonexistent path would rebuild
  nothing and loop forever.

### Two outcomes, not one

"Failed to compile" and "the worker died while holding it" need different retry
behaviour and are now distinguishable. An external earlyoom SIGTERM is not the
file's fault (72 SIGTERMs in 12h on this box; `simple` is the preferred victim),
so an orphaned claim should be retried as-is, while a genuine compile failure
needs a source fix before a retry can succeed.

## Constraints this design must respect

- **Shared across workers, not per-process.** With `--threads 24`, many
  concurrent workers each recompute the whole 689-module closure independently.
  Any per-phase state must be shared, or the same phase gets checkpointed 24
  times. The orphan ledger is a single append-only file in the shared queue dir,
  which is correct under fan-out; a per-process memo would not be.
- **Do not inherit the memo-latch bug.**
  `frontend_parse_cache_scope()` latches its memo on the first call and never
  re-reads the env, while the publisher runs only in phase 2 — so on the
  `--entry`-less stage path the parse cache is silently off for the whole
  process, and `hir_cache_enabled()` gates on the same memo
  (`doc/08_tracking/bug/frontend_parse_cache_scope_memo_latches_off_2026-08-23.md`).
  The orphan ledger deliberately holds **no memo at all**: its path is derived
  from the `queue_dir` argument at each call, so there is nothing to latch. Any
  future per-phase receipt must resolve its scope after publication, or re-read.
- **Scale.** The closure is 689 modules out of 15,221 `.spl` files in `src`
  (`--entry-closure` follows imports from the entry). Per-file status tracking
  needs to scale to hundreds, not tens of thousands.

## Verification

`test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl`, 10 scenarios.
Measured 2026-08-23: **post-fix 10 passed / 0 failed; pre-fix (source reverted,
spec kept) 5 passed / 5 failed** — the 5 failures are exactly the new scenarios,
so the reproduce is proven to fail before the fix. Neighbours in the same defect
class cover legacy-marker compatibility, de-duplication across several dead
shards, the empty/unpublished queue, and a format pin on the claim *writer* (in
a different module from the reader — without it the writer could silently stop
recording paths while every synthetic-marker test still passed).

## Not landed here — explicitly

- **Stage A per-phase checkpointing.** Phases 3 (typecheck+mono) and 4 (mir)
  persist **nothing**, so a true "resume from phase 4" is impossible without
  first persisting MIR. Phases 1, 2 and 5 already have content-keyed caches
  (`.fpc`, `.hir`, objects), so resume across those is already implicit. The real
  gap is that phase 1 never calls `bootstrap_select_cache_lane()`
  (`scripts/bootstrap/bootstrap-from-scratch.sh:1010-1027`), so retry attempts do
  not share a scope. That is the cheap half and should land next.
  `phase.marker` (`driver_aot_native_output.spl:715`) is written once and
  **never read** — it is the natural place to grow a real receipt.
- **Stage C clean-rebuild gate.** Designed, not landed: convergence output must
  not be able to masquerade as success. A build is green only after a
  from-scratch rebuild with all caches cleared produces the artifact. This needs
  a provenance marker on the artifact recording which mode produced it, plus a
  fail-closed guard that refuses to ship a convergence-mode artifact. Until that
  exists the separation is a convention, not an enforcement, and the whole safety
  argument rests on it — so this is the highest-priority follow-up.
- **Sound per-file reuse for delivered artifacts.** Deferred with evidence; see
  `per_file_rebuild_soundness_2026-08-23.md`.

## Kill-switch

The landed change adds no reuse path, so it has no kill-switch and needs none:
it only records evidence that was previously deleted. Reclaim behaviour, the
released count, and the set of markers deleted are all bit-for-bit unchanged.
Every future reuse path (convergence retry selection, phase receipts) must ship
with an env kill-switch, default off.
