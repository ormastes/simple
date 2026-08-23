# Parse-shard children lost the slim entry — `6cedd51faec` silently reverted `5409b246adc`

- Filed: 2026-08-23
- Status: FIXED (this change) — one-line restoration
- Severity: high (build-wide memory; box saturation)

## Symptom

Every `native-build` parse-shard child is spawned as the FULL CLI
(`src/app/cli/native_build_worker.spl`), which evaluates the entire compiler
closure (~665 modules) before parsing a single file. With `--threads 8` that is
~8x a whole-compiler closure resident at once.

Measured live on this host 2026-08-23 (read-only `/proc` sampling of 41
already-running `native_build_worker` processes across two independent lanes,
521 samples over ~9 min):

| metric | value |
|---|---|
| per-worker VmRSS | 2.40 -> 2.74 GB, monotonically increasing, never released |
| VmPeak | 3.53 GB |
| anonymous (heap) share of RSS | 2516 MB of 2530 MB = **99.4%** |
| top mapping | `[anon:mimalloc]` 2450 MB (single arena) |
| Shared_Clean across workers | **14 MB** (the binary's text) |
| Pss vs Rss | 2516 MB vs 2530 MB — i.e. **no page sharing at all between workers** |
| Swap | 0 |

So N workers cost N x 2.5 GB of *private dirty* heap. Nothing is shared, nothing
is file-backed, nothing is reclaimed.

## Root cause

`5409b246adc` ("perf(native-build): parse-shard workers 3.82 GB -> 1.54 GB RSS
via a slim parse-lane entry") pointed `run_parse_shards` at the purpose-built
slim entry `src/app/cli/parse_shard_main.spl`.

`6cedd51faec` ("fix(native-build): log every parse-shard exit; reclaim a dead
shard's orphaned queue claims") rewrote `run_parse_shards` wholesale from a
stale base and put the line back:

```
-    # Slim entry: loads only the parse lane (see src/app/cli/parse_shard_main.spl),
-    # not the whole compiler closure native_build_worker.spl pays per shard.
-    var base = ["run", "src/app/cli/parse_shard_main.spl"]
+    var base = ["run", "src/app/cli/native_build_worker.spl"]
```

Its commit message says nothing about the entry — the reclaim work is entirely
orchestrator-side (`app.cli.parse_shard_queue.{parse_shard_release_claims,
parse_shard_exit_label}` is imported only by `native_build_main.spl`; the child
never touches it). The two changes are orthogonal; this was an unintentional
stale-snapshot clobber of the exact class `.claude/rules/vcs.md` "Sync must never
clobber" describes.

Cost of the revert: `driver_parse_shard_entry.spl:6-11` records 665 modules /
~3.3 GB for the full closure vs a measured 383 modules / 0.88 GB for the parse
lane; `5409b246adc` measured 3.82 GB -> 1.54 GB per shard. At `--threads 8`
that is roughly **18 GB of avoidable resident memory per build run**, which is
why three concurrent runs saturate a 125 GB box.

## Why no guard caught it

- `test/01_unit/compiler/driver/parse_shard_slim_entry_spec.spl:16` asserts
  exactly this ("dispatches parse shards to parse_shard_main.spl, not the full
  worker"). It is a pure text assertion over `native_build_main.spl`, so it has
  been RED on `main` since `6cedd51faec` — `src.index_of("\"src/app/cli/parse_shard_main.spl\"")`
  returns -1, so `slim_at > fn_at` is false. It was simply not run on that push.
- `scripts/check/check-parse-shard-rss-budget.shs:21` derives `SHARD_ENTRY` by
  grepping whichever entry `native_build_main.spl` names, so after the revert it
  budgets the *worker* entry rather than failing that the slim entry is gone.
  It is a per-shard budget and never multiplies by N.
- `scripts/check/check-perf-regression-tests.shs` has **no row** for this fix.

## Fix

Restore the slim entry (one line + its comment) in
`src/app/cli/native_build_main.spl:377`. Semantics-preserving: parse sharding is
a cache warm-up and, per `parse_shard_main.spl:1-10`, "can never change the
build's output"; a shard that cannot parse its args exits non-zero and is
ignored.

## Follow-ups (not done here)

- (a) Add a `check-perf-regression-tests.shs` row pinning the slim entry by
  mechanism, so the next stale snapshot fails the push rather than a test run.
- (b) `run_hir_shards` (`native_build_main.spl:445`) still spawns the full
  worker and has no slim entry — HIR children genuinely need the HIR lane, but
  they also rebuild the closure and frozen surfaces themselves
  (`doc/08_tracking/bug/hir_shard_children_reparse_closure_2026-08-22.md`).
- (c) `check-parse-shard-rss-budget.shs` should assert the entry it budgets is
  the slim one, instead of following whatever the source names.
