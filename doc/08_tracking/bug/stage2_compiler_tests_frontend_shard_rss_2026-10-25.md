# Stage 2 compiler-test full-CLI build: frontend shard workers use about 2x their admission estimate (2026-10-25)

Status: OPEN (design). This record has the measurements and the cause. The
diagnostic rerun ran with the cap in monitor mode under a cgroup bound. Nothing
was raised permanently.

## Symptom

In lane p2shard-17, `stage2-compiler-tests` aborted with
`status=rss-cap-exceeded` and exit 88. The process tree peaked at 50,341,236 KiB
against a 50,331,648 KiB cap. At that point the full-CLI build
(`compiler_cli_build`, 2937 modules, `--threads 8`) was in HIR, with 8 shard
workers and 17 processes. The tree jumped to 28.8 GiB at HIR start, then grew to
49 GiB over about 8 minutes.

## Measurement (rerun1, Stage 2 9ccec40f, threads=20, monitor mode, cgroup 95G)

Per-PID RSS was sampled every 2 s.

| phase | workers admitted | admission estimate / worker | measured / worker | tree |
|---|---|---|---|---|
| parse shards | 18 (of 20) | 1,650,000 KiB | 3.1-3.6 GiB, lives about 34 s | 60.4 GiB |
| HIR shards | 10 (of 20) | 3,000,000 KiB | start about 1 GiB, max 5.3-6.3 GiB | about 57-65 GiB |
| parent | 1 | — | 2.0 GiB | |

- Admission caps HIR at 10 workers: 60% of the 48 GiB tree budget, divided by
  3 GB. Requesting 20 jobs does not give 20 HIR workers.
- Each worker grows steadily with the modules it lowers. At about 230-330
  claims per worker, HIR was about 90% done.
- The run was then contaminated. Phase-3 run-27d (110G scope) started
  concurrently at 09:17:28, and host memory pressure made the ledger claims fail.
  The workers reported `HIR shard ledger claim failed` and
  `BLOCKED: incomplete worker or ledger publication`. This is not a compiler
  verdict.

## Cause

1. HIR and parse shard children are exec'd (`run_ledger_shards`,
   `native_build_main.spl` ~926-1100). Each child re-parses from the cache and
   rebuilds the whole-program surface itself.
2. A child never returns lowering garbage, because there is no collector.
   Per-file parser globals and the phase memos are promoted on every claim
   (`driver_hir_pipeline_lowering.spl` ~957-1016). Growth is therefore
   proportional to the modules lowered.
3. The admission estimates (`shard_worker_budget_kb` defaults 1,650,000 and
   3,000,000 KiB, pinned in `scripts/bootstrap/lib/product-frontend-policy.shs`)
   are about half the measured peaks. Admission therefore lets in more workers
   than the cap can hold.

## Regression or scaling

This is scaling and design, not a p17 merge regression.
- No earlier p2shard lane reached HIR. p2shard-15 and -16 died in source
  closure or surface, so there is no older HIR baseline.
- A code review of cgmem2, rustscope, hirpath/posthirperf, lambdasym, spawn4,
  lenspan and the hir-cache rebase commits found none that touches HIR-shard
  child retention.

## Why 20 jobs cannot fit as designed

- 20 HIR workers × about 6 GiB is about 120 GiB, more than the 121 GB host, let
  alone the 48 GiB cap.
- 20 parse workers × about 3.4 GiB is about 68 GiB.

Fitting 20 jobs needs per-worker RSS below about 2.3 GiB. The candidates:
- Fork HIR children after the surface freeze, sharing it copy-on-write as MIR
  does (`fork_shared_heap_v1`). The watchdog sums per-process RSS, so it would
  also need PSS accounting.
- A rolling child exit after K modules (`SIMPLE_HIR_SHARD_CHILD_MODULES`,
  mirroring the MIR fork roll). This bounds the growth, not the base.
- Loading only each claim's import surface instead of the whole program.
- Admission from measured peaks (about 3.6 GiB parse, about 6.3 GiB HIR) would
  stop the cap overrun, but it means fewer workers.

## release/1.0.0

The measurements above come from the dev line (lane p2shard-17, base `d3fc04205cf`). The same
mechanism is on release/1.0.0: `run_ledger_shards` (`src/app/cli/native_build_main.spl`), the
`HIR shard ledger claim failed` path in `driver_hir_pipeline_lowering.spl`, and the 1,650,000 /
3,000,000 KiB admission estimates in `scripts/bootstrap/lib/product-frontend-policy.shs`. No
release/1.0.0 run was measured.
Line references above are dev-line. On release/1.0.0, `run_ledger_shards` starts at
`native_build_main.spl:906` and the per-claim promotion sits at about
`driver_hir_pipeline_lowering.spl:967-972`. Release/1.0.0 has no MIR fork child-module roll
(`SIMPLE_MIR_FORK_CHILD_MODULES` is absent), so the rolling-child-exit candidate has no existing
mechanism to mirror there.
