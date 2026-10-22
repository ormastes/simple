# Phase 4: main build adopts every shard HIR entry but logs `cached=0`; parse shards never partition on the streaming route

- **Date:** 2026-10-19
- **Status:** root-caused and fixed in compiler source (takes effect at the next Stage 2)
- **Producer:** r13 Stage 2 `stage2-admitted/simple` sha256 `e6cb4bfd5533a790...` (aarch64)
- **Build:** Phase 4 full CLI, `--entry src/app/cli/_CliMain/main_and_help.spl --entry-closure --low-memory --threads 8`, 2702 modules, 4029 files, scope `boot-p4-r13`
- **Log:** scratchpad `phase4/r13p4/build.1.log`, `watch.1.log` (session 89db84d8)

## Reported symptom (two claims, both receipt artifacts)

1. "Main build ignores the shard HIR": 8 HIR shards stored 2702 entries, then
   every main-build row read `[build] phase=hir ... cached=0` for 13+ minutes.
2. "Workers cold-parse": 42,311 `phase2:surface:file:parse-start` lines for
   4,029 files; no `[frontend-cache]` line from any worker.

## What the log actually says

- `build.1.log:538745` is the main build's own summary:
  `[hir-cache] hits=2702 misses=0 stores=0 refused=0 rejected=absent:0`.
  Adoption worked. `cached=0` came from
  `driver_hir_pipeline_lowering.spl:1179-1181, 1205-1207, 1391-1393`, which
  passed a **literal 0** as the `cached` argument of `log_build_progress`
  (the parse loop passes `frontend_parse_cache_hits()`; the non-streaming
  HIR loop already passed `hir_cache_hits()`). Stage 3 r14 (`hits=1316
  misses=0`) and Phase 4 r13 behave identically; only the progress field lied.
- The real cost of the main HIR phase was the **hit path**: 2702 hits in
  `elapsed_ms` 256,503 -> 787,407 = 531 s, ~196 ms per hit over 940 MB of
  entries (largest 22 MB), serial. `hir_cache_load_in_owned_scope` called
  `hir_module_decode_stable` (`hir_codec.spl:515-521`): decode, then a FULL
  re-encode and compare. The store side already refuses an unstable frame
  (`hir_cache_store_in_owned_scope`, selfcheck or `decode_stable`) and the
  checksum pins the bytes, so the load-side re-encode re-proved a property the
  entry could not have lost.
- `phase2:surface:file:parse-start` fires at
  `driver_source_pipeline_parsing.spl:559`, BEFORE the front-end cache is
  consulted, so it counts hits as parses. The streaming surface route
  (`parse_all_streaming_surfaces_in_place_impl`, selected by `--low-memory`)
  never printed the `[frontend-cache] hits= misses= parses=` receipt that the
  non-streaming loop prints at :1038, so no process could show its hit rate.
  The 2,734 `.fpc` entries for 2,702 modules (not ~5,400) say the HIR workers
  hit under the same keys rather than missed-and-restored.
- All 8 parse shards reported `[parse-shard] done ... claimed=0` with
  parses 1288..1518 each (11,086 body parses for 4,029 files, ~2.75 per
  module). The streaming loop (:697-745) never called
  `_driver_parse_shard_owns`, so every shard parsed the whole closure racing
  its siblings; the shared claim queue the coordinator publishes
  (`SIMPLE_PARSE_SHARD_QUEUE`) was never consulted. Reproduced with r14 on a
  956-module probe (`--threads 2`): `done shard=0/2 parses=877 claimed=0`,
  `done shard=1/2 parses=854 claimed=0`.

## Fix (pure Simple, red->green spec `test/01_unit/compiler/driver/hir_adopt_and_streaming_parse_receipts_spec.spl`)

- `driver_hir_pipeline_lowering.spl`: the three streaming HIR progress rows
  pass `hir_cache_hits()` as `cached`; the main build (not a shard) prints
  `[hir-cache] adopted=<hits> lowered=<misses>` right before the summary (the
  summary stays the last `[hir-cache]` line for `native_build_warm_receipt`).
- `driver_hir_cache.spl`: a hit decodes once; `hir_cache_load_reencodes_v1`
  keeps the load-side roundtrip only for the explicit `all` selfcheck mode
  (`SIMPLE_HIR_CACHE_SELFCHECK=1` / `SIMPLE_HIR_CODEC_ROUNDTRIP=1`).
- `driver_source_pipeline_parsing.spl`: the streaming loop skips sources a
  parse shard does not own, prints `[frontend-cache] hits= misses= parses=`
  for every process on the route, and a parse shard exits right after the
  loop instead of building the surface registry first.

## Found by the probe, recorded as a follow-up: the front-end scope is recomputed per child from the live tree

The 956-module r14 probe (`SIMPLE_M4_WORK_RECEIPT=1`, 2 parse shards, 2 HIR
shards, OOM-killed at 8 GB at HIR 301/956) showed the HIR workers cold-parsing
1551 files and hitting 967 although the parse shards had just stored every
file. The cache dir held two scope headers differing only in the compiler
source fingerprint: `sources=5f8c499e2799e1d6n189` (222 entries, written
23:37-23:39 by the parse shards) and `sources=b557e0d632a0cc4bn189` (955
entries, written 23:40-23:42 by the HIR workers; the HIR entries carry the
same). `native_build_frontend_source_fingerprint` (`driver_build/incremental.spl`)
hashes `src/compiler/10.frontend` relative to cwd at each process's first
parse, and the supposedly read-only tree received a commit touching
`10.frontend/core/lexer_struct.spl` at 23:39:04, between the two child kinds.
Each child of one build therefore computed its own identity, every worker
lookup missed, each worker overwrote the entry under the new header, and the
sibling worker hit ~50% of the time (708 paths hit by one worker and missed by
the other, 247 missed by both). Phase 4 r13p4 had a single header, so this did
not cause its symptoms, but it is the mechanism by which a parse-shard warm-up
is silently thrown away. Follow-up: the coordinator should compute the scope
once and publish `SIMPLE_FRONTEND_CACHE_SCOPE` to every child
(`_driver_publish_frontend_cache_scope` already honours a published value);
it must hash the CHILD binary (`simple_bin`), not the coordinator's own
executable, which is why it is not folded into this change.

## Not fixed here (recorded)

- `native_build_parse_shard_count` (`native_build_main.spl:613`) returns 0 for
  streaming only when the env requests streaming; the driver also selects the
  streaming route for `--low-memory`, so the coordinator and driver disagree
  about the route. With ownership honoured on the streaming loop this is no
  longer a correctness problem, but the two decisions should share one owner.
- Every HIR worker still re-parses or restores the full frozen closure
  (by design: lowering reads frozen surfaces). Under the streaming route a
  hit still pays bridge + surface + promote per file: probe 3 (278 modules,
  r14, tree stable) restored all 278 in the main build in 15.4 s including
  load_sources (<= 55 ms per file, 278/278 hits, HIR workers 813 hits / 21
  cold parses), which is the "146 s per worker" seen in Phase 4 at 4029 files.
