# Phase-3 per-file pool refuses to start: MIR/HIR worker priced at 26 GiB (Windows)

- **Status:** open
- **Date:** 2026-11-15
- **Severity:** P1 (blocks every phase-3 self-build on a host with < 90 GiB free)
- **Binary:** `C:\dev\wt\seed-stage-20261115\stage2.exe` (28,815,872 B, 2026-11-15 15:32, contains
  `SIMPLE_UNIT_TLDR_ROOT`, so it includes #9387 and #9394)

## Symptom

Running `stage2.exe native-build ... --entry src/app/cli/bootstrap_main.spl --threads 40` exits rc=1 with 0 objects
after 441 s (peak tree 2.0 GB):

```
error: per-file worker pool refused (hir_workers=0 mir_workers=0, need >= 2): not enough free memory for 2 workers.
Free memory=28703588 kB, per-worker budget=27262976 kB (HIR 27262976 kB, MIR 27262976 kB), need >= 90876587 kB free ...
error: MIR shard aggregate failure; link and artifact publication blocked
```

Two other phase-3 runs on the same binary (PID 80348, OFF and ON lanes) ended the same way: 0 objects, killed.

## Expected

#9387 prices per-file pool workers at the measured per-file peak (5.04-5.65 GiB), not at the 26 GiB whole-program
closure price that `file_worker_pool_mir_budget_kb_v1(modules, scale=false)` returns. HIR is also at 26 GiB here, not
the scaled 9 GB default. With 28 GB free, the pool should admit at least 2 workers.

## Suspects

- `src/app/cli/file_worker_pool_refusal.spl:153-166`: the refusal path appears to take the unscaled (shard) price, or
  `file_worker_pool_live_usable_kb_v1()` returns 0 on Windows, so the scaled price is never applied.
- The `[hir-shard] tree budget clamped: ... headroom 25165824 kB -> effective 3538644 kB` line shows that the 24 GiB
  headroom (#9395) consumes almost all free memory on this host.

## Workaround (tagged `WA(p3-worker-price-26g)`)

Launch-environment only, no source change:
`SIMPLE_MIR_SHARD_WORKER_KB=6815744 SIMPLE_HIR_SHARD_WORKER_KB=6815744` (the host floor the error message names).

## Repro

Use the scratchpad `phase3self/build_p3.ps1` invocation: the stage2.exe flags above, `--threads 40`, on a host with
about 28 GB free.
