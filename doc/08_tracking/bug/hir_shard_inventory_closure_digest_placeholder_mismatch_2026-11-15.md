# HIR frozen inventory fails: interface closure rows differ across shard workers (2026-11-15)

Status: verification-pending (fix in `work/hir-inventory-closure-digest-20261115`)

## Symptom

Every phase-2 `native-build --entry-closure --mode dynload` on the per-file
worker route failed in phase 3 (WSL Ubuntu-24.04, builder = stage-2
`simple-bootstrap 1.0.0-rc.1`, entries `src/app/cli/lint_entry.spl` and
`src/app/test_runner_new/main.spl`, targets x86_64- and aarch64-unknown-linux-gnu,
4/4 runs):

```
[hir-shard] owner=1/2@0~h0 inventory publication failed: closure identity differs: published=f4ad49a4… worker=ae4019bc…
error: HIR frozen inventory publication failed
```

Raised at `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1160` (and
`:2018`) when `hir_shard_inventory` (`driver_hir_cache.spl`) ->
`hir_shard_recovery_inventory` (`driver_hir_recovery.spl:222`) finds a
published `{queue}/inventory` whose closure digest is not the worker's. The
queue is fresh per run (`hir-recovery/queue-<pid>-0`), so it is not stale state.
Every worker logged `[hir-cache] closure-key=interface surfaces=336
content_fallbacks=0`: same surface set, no fallbacks, different digest.

## Root cause

`hir_cache_closure_digest` (2026-11-13, `da7494c0ebf`) keys each closure row
on the surface's semantic interface digest (`S:{semantic_hash0..3}`). A HIR
shard worker builds REAL surfaces only for its own closure slice and an
empty-text PLACEHOLDER for every other module
(`driver_worker_surface_closure_v1.spl` step 4; `worker_mode == 2` parses `""`
in `driver_source_parse_selected.spl`). The placeholder keeps the source's
content hash, but its semantic digest is that of an empty module and is still
`semantic_cacheable`. Workers seeded from different slices therefore fold
different `S:` rows for the same module, so the first worker's published
digest never matches the others. The step-4 comment's invariant ("identity
fields come from the source, so the closure digest is unchanged") held only for
content rows.

Confirmation: with `SIMPLE_HIR_CACHE_CLOSURE_KEY=content` the same build passed
the inventory and reached AOT.

## Fix

Content rows are the default again; interface rows are opt-in
(`SIMPLE_HIR_CACHE_CLOSURE_KEY=interface`) and documented as sound only where
no placeholder surfaces exist. A placeholder cannot carry the real interface
digest without the parse P5 removes, and any per-process fallback just moves
the disagreement, so the only process-independent key is the source content.

## Spec

`test/01_unit/compiler/80.driver/hir_worker_placeholder_closure_digest_spec.spl`:
two workers with opposite real/placeholder splits (different entry slices) and
a consumer that built every surface produce one digest; a real source edit
still moves it. Interface-keying specs now opt in explicitly.

## Cost

Body-only edits invalidate the whole closure's HIR keys again (the pre-11-13
behaviour) until placeholders carry a real interface digest.
