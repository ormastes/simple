# TLDR: true per-file src->obj plan

Full plan: `true_per_file_src_to_obj_plan.md` (same dir).

Baseline (p3new build.log): 8 global parse shards, then 9 workers each
re-parse the full closure (17 `selected=1525` lines, ~6 min each). 11m53s
logged, no object yet. Target: first object <= 10 s.

PRs, in order (consider landing 3 before 2c to avoid a rebase):
1. Publish closure once; workers reuse `SIMPLE_PARSE_CLOSURE_REQUEST`
   (`native_build_main.spl:1801/2009/2015`, `native_build_parse_closure_owner.spl:96-100`).
   Add `compile_targets.spl` (:1482-1484, :1537-1540) explicit file-worker marker;
   clear sites :1981/:2027/:2142; clean pid-keyed dirs. Integration spec counts
   real walks, expects 1.
2. No global parse barrier, split in three:
   2a per-stage driver entry points (parse/HIR/MIR/emit) + parity spec;
   2b `tldr_summary_v1.spl` + spec: target-neutral (all cfg variants), full
   summary-content sha256 (not `interface_digest_of_source`, which under-captures
   struct fields), policies for glob/bare imports, inferred types, generic bodies,
   macros, counted per-module fallback (measure rate), cross-process file lease
   + atomic rename, Windows share-delete/backoff + concurrent-read spec;
   2c route switch behind a flag.
3. Land #4962 (B1-B4 resolved per Fable re-review) + owner-pid lease for
   orphan picks + real per-file lane run. Several refs are branch-only
   (`work/per-file-single-process-pipeline`).
4. Leaf-first scheduling, `[first-object] ms=` metric, <= 10 s gate.
5. Invoker trait: process + fiber invokers, async node tasks (after #4910).

Every PR: spec red->green (plus `test/unit/` mirror where the divergence guard
needs it), time-to-first-object, total, peak RSS under external harness
capwatch.ps1 (not repo code) 8 GB on a small probe. Stage3 self-build proves the batch.
