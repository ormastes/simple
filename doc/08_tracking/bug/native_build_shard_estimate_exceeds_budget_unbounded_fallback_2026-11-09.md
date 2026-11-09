# native-build: shard estimate exceeds budget; no-verdict MIR fallback is unbounded

Status: fix-implemented-verification-pending (P1, blocks phase 3)

## Evidence (stage3 attempt 1, C:/dev/p3new/stage2new/build_s3.log)
- `:11754` `[mir-shard] measured worker peak commit=18727136 kB (static estimate 27262976 kB, previous run 0 kB)`
- `:11755` `completed_workers=0 failed_workers=2 failed_modules=0 unfinished=-1`
- `.err`: `owner=0/1@0 status=CRASH exit=-2 claimed=0` then
  `falling back to in-process unsharded MIR`; result `peak_tree_GB=10.6 killed=True`.
- Host had ~49 GB free; reserve 24 GiB -> ~24 GB budget.

## Root cause
1. Per-worker static estimate (26 GiB here) is doubled while no peak is
   recorded (`shard_commit_unmeasured_estimate_kib_v1`) to 52 GiB, larger than
   the whole budget. Pricing is never clamped to what is available.
   Note: the 18.7 GB "measured peak" is the pool's commit delta (base - now
   headroom), so it includes any other host activity; it is an upper bound.
2. `run_mir_shards` outcome `fallback` (no module verdict) made the final
   worker lower MIR unsharded in process with no bound -> 10.6 GB+ and a kill.

## Fix
- `shard_worker_estimate_clamped_kib_v1(est, headroom - reserve)`: the pool
  price is clamped to the known budget, so one worker always fits; live commit
  admission still gates each further spawn.
- `native_mir_shard_fallback_action_v1`: no-verdict outcome retries once with
  1 worker, then refuses loudly (exit 1) unless
  `SIMPLE_MIR_SHARD_INPROCESS_FALLBACK=1`.

## Not folded in
`native_build_interpreted_worker_fixed_2_4gb_floor_2026-08-18` and
`native_build_interpreted_worker_rss_blowup_2026-08-18` are interpreted-worker
parse RSS terms, not planner pricing or fallback; left open.

## Open
Why the single MIR worker ran to timeout with claimed=0 (exit -2) is not
diagnosed here; the fix makes that failure loud instead of a memory blowup.

Spec: test/01_unit/app/cli/shard_budget_clamp_fallback_spec.spl

## Follow-up (owner item 3): s3b HIR-phase RSS growth
build_s3b.log.cap (live, read-only): tree 10.15 GB at 800 s -> 12.05 GB at
934 s, 4 procs, HIR at ~271/1616 modules (~14 MB per module retained). The
growth is in-process HIR retention, not shard pricing; it matches
native_build_interpreted_worker_rss_blowup_2026-08-18 (unbounded creep) and is
NOT fixed by this change. Needs a per-module retained-size profile of the HIR
worker.

## Measured-peak pricing (owner item 1)
With a recorded peak the worker is priced at peak + 25% (floor 1 GiB), not
max(static, peak): build_tr.log peak 7364284 kB -> 9205355 kB, 2 workers fit a
49 GB / 24 GiB-reserve host with no SIMPLE_*_SHARD_WORKER_KB override.
