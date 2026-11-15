# Phase-3 MIR shard aggregate failure with no per-shard diagnostic (2026-11-15)

- status: open
- severity: P1 (blocks phase-3 acceptance on Windows)
- binary: C:/dev/wt/seed-stage-20261115/stage2.exe (has SIMPLE_NODE_ATTR, SIMPLE_UNIT_TLDR_ROOT)
- host: Windows 11, 31 GB free commit at launch, --threads 16

## Repro
Full-CLI native-build (`--source src/{compiler,app,lib,plugins,os}` and the two compositions,
`--entry-closure --keep-going --go-to-end --mode dynload --entry src/app/cli/main.spl`),
SIMPLE_MIR_SHARD_COUNT=3, with `SIMPLE_MIR_SHARD_WORKER_KB=6815744` and `SIMPLE_HIR_SHARD_WORKER_KB=6815744`
set (WA(p3-worker-price-26g) for B1, fixed in #9506). Ran with node-attr OFF and ON.

| lane | objs | first_obj_s | peak tree | wall | rc |
|------|------|-------------|-----------|------|----|
| OFF | 0 | -1 | 4.66 GB | 405.8 s | 1 |
| ON  | 0 | -1 | 1.81 GB | 308.8 s | 1 |

Log (both lanes):
```
[parse-closure] parent_walks=1 selected=3216 ...
[shard] threads=1 (... worker budget=27262976 kB ...)
[hir-shard] tree budget clamped: declared 0 kB, cap 0 kB, free 31122652 kB, headroom 25165824 kB -> effective 5956828 kB
[hir-shard] admission worker estimate=6815744 kB ...
[shard] threads=0 (... worker budget=6815744 kB, parent peak=4937200 kB)
[shard] threads=2 (... worker budget=6815744 kB ...)
error: MIR shard aggregate failure; link and artifact publication blocked
```

## Defects
1. **No diagnostic.** `native_build_main.spl:2396` reports an aggregate failure without naming any
   failing shard, module or worker exit code. No `[mir-shard] owner=` lines are printed, and the cache dir
   holds only `frontend/closure-request-*`. This should print each shard's verdict and exit code.
2. **HIR warmup admits 0 workers.** effective = free - 24 GiB headroom = 5.96 GB, which is below the
   6.8 GB per-worker estimate. MIR then starts 2 workers anyway. The two admissions disagree.
3. **The B1 workaround is partial.** The first `[shard]` admission still prices a worker at 26 GiB
   (host.sdn `worker_mem_mib=26624`), so it ignores SIMPLE_{MIR,HIR}_SHARD_WORKER_KB.

## Workaround
None cheap and safe: the failure cause is not observable. Retest on a stage2 that includes #9506, and on a
host with at least 40 GB free commit.

## Node-attr sanity gate
Inconclusive. Both lanes produced 0 objects, so OFF==ON cannot be judged from this run.
