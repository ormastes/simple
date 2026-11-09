# native-build: default per-worker budget (26 GiB) refuses the per-file pool with 49 GB free

- **Status:** open (P3, bootstrap)
- **Found:** 2026-11-09, Windows, `C:/dev/p3new/stage2new/stage2_new4.exe native-build src/app/mcp/main.spl` in a clean `origin/main` worktree.

## Observed
```
error: per-file worker pool refused (hir_workers=0 mir_workers=0, need >= 2): not enough free memory
for 2 workers. Free memory=49251808 kB, per-worker budget=27262976 kB (HIR 27262976 kB, MIR 27262976 kB),
need >= 90876587 kB free.
```
The same build with `SIMPLE_HIR_SHARD_WORKER_KB=SIMPLE_MIR_SHARD_WORKER_KB=8000000` was admitted and
reported `[file-worker] measured worker peak commit=1134952 kB (static estimate 8000000 kB)` — the
peak of 1.1 GB came from workers that failed early, so it is NOT a fair need. A successful
entry-closure in-process build of the same entry measured `[mir-shard] measured worker peak
commit=13945208 kB (static estimate 27262976 kB)` — so the real MIR need is ~14 GB, about half the
26 GiB estimate. The defect is the ~2x over-estimate plus the 2-worker floor (2 x 26 GiB / 0.6),
which refuses any host with < ~91 GB free.

## Gap (not yet localized)
`src/app/cli/shard_mem_clamp.spl:240-241` declares `SHARD_{HIR,MIR}_WORKER_KB_V1 = 9000000`, yet the
refusal prints 27262976 kB (exactly 26 GiB). Whatever raises 9000000 to 26 GiB in
`shard_worker_budget_kb` / `shard_worker_estimate_kib_v1` (or the `shard_mem_clamp` worker
estimate) is the site to fix; it was not traced in this pass. The refusal message itself is correct
and names the override knobs.

## Repro
Run the command above on a host with < ~91 GB free and no `SIMPLE_*_SHARD_WORKER_KB` set.
