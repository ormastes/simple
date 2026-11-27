# BUG: default per-file pool admits 0 workers (MIR priced at 0 kB) and degrades to 1 serial worker at 53 GB free

Status: FIX IN PR (source change; not re-run — see "Unverified")
Severity: P1 performance (canonical Stage 3 lane ~65+ hours)

## Measurement (2026-11-22)

Stage 2 compiler built from release head `53795406ba6`, building the bootstrap
CLI (1601-module closure) on a 64-CPU / 60 GB host, `--threads 40`,
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=44000000`, cgroup memory.max 46 GB, no
worker-price overrides.

```
[shard] threads=6 (requested 40, ... available=55953700 kB, tree budget=44000000 kB (declared 44000000 kB, cgroup memory.max 48234496 kB), worker budget=3800000 kB, parent peak=-1 kB)
[hir-shard] tree budget clamped: declared 44000000 kB, cap 48234496 kB, free 53436100 kB, headroom 12058624 kB -> effective 41377476 kB
[shard] threads=2 (requested 40, ... available=53436100 kB, tree budget=44000000 kB ..., worker budget=9000000 kB, parent peak=5374532 kB)
[shard] threads=1 (requested 40, ... available=53543896 kB, tree budget=44000000 kB ..., worker budget=0 kB, parent peak=-1 kB)
[file-worker] WARNING: pool admits 0 worker(s) under the tree headroom (hir_workers=2 mir_workers=0); raw free memory covers one worker + coordinator, degrading to 1 serial worker (RSS guard authoritative)
[file-worker] workers=1 ...
```

Result: one serial worker, 22 units in 63 minutes (~2.5 min per single-module
unit). Measured per-file worker RSS: 1.7-4.7 GB (tree 3-8 GB with one worker).

## Where the numbers come from

- Pool size: `src/app/cli/native_build_main.spl` `run_file_worker_pool_v1`,
  `parallel = min(hir_count, mir_parallel)`.
  - `hir_count = native_build_hir_shard_count` -> `shard_threads_mem_cap(threads, hir_price, parent_peak)`.
  - `mir_parallel = native_build_shard_threads(args, mir_price)`, which returns
    0 whenever the cap is <= 1.
- HIR price: `file_worker_pool_live_unit_hir_budget_kb_v1`
  (`src/app/cli/file_worker_pool_refusal.spl`) defaulted to
  `SHARD_HIR_WORKER_KB_V1` = 9,000,000 kB (`shard_mem_clamp.spl`), the
  whole-closure HIR worker price. Tree term: (44,000,000 - 40% reserve) /
  9,000,000 = 2.
- MIR price: `file_worker_pool_live_unit_mir_budget_kb_v1` defaulted to
  `FILE_WORKER_POOL_PER_FILE_WORKER_KB_V1`, declared as
  `pub const ... = SHARD_HIR_WORKER_KB_V1` — the only const in `src/app/cli`
  initialised from an imported const. The log shows it priced at 0 kB. Every
  later step preserves a non-positive price (`_file_worker_pool_unit_phase_price_kb_v1`
  returns the default, `_file_worker_pool_unit_scaled_budget_kb_v1` returns
  `budget_kb <= 0` unchanged), `shard_threads_cap_for(_, 0, _)` returns 1, and
  `native_build_shard_threads` maps 1 to 0. `min(2, 0) = 0`.
  The alias reading 0 in the natively built Stage 2 is inferred by elimination
  (HIR, which names `SHARD_HIR_WORKER_KB_V1` directly, printed 9000000; MIR,
  which goes through the alias, printed 0) and matches the open class
  `cross_import_const_no_hir_linkage_2026-07-25.md` /
  `bootstrap_stage2_driver_const_fold_import_2026-08-26.md`. It was not
  reproduced in isolation.

## Fix

- `FILE_WORKER_POOL_PER_FILE_WORKER_KB_V1` is the literal `9000000` (same value,
  no imported-const initialiser).
- New `FILE_WORKER_UNIT_WORKER_KB_V1 = 6291456` (6 GiB): the measured 1.7-4.7 GB
  unit-worker RSS plus >= 25% margin. It is the default for both unit-pool
  prices; the 9 GB whole-closure price is no longer used for unit workers.
- New pure `file_worker_pool_nonzero_price_kb_v1(price, fallback)`: a
  non-positive live unit price falls back to the unit price instead of
  reaching admission as 0.
- Overrides (`SIMPLE_*_SHARD_WORKER_KB`, host `worker_mem_mib`), scale-to-host,
  the 32-bit clamp, live commit admission and the RSS guard are unchanged.

Arithmetic for this host at 6,291,456 kB:

- HIR: host 60% x 53,436,100 = 32,061,660 -> 5; tree (44,000,000 - 17,600,000)
  / 6,291,456 -> 4; clamp 41,377,476 / 6,291,456 -> 6. `hir_workers = 4`.
- MIR: host 60% x 53,543,896 -> 5; tree 60% x 44,000,000 = 26,400,000 -> 4.
  `mir_workers = 4`.
- Pool = 4 workers. Priced worst case 4 x 6,291,456 + 5,374,532 coordinator =
  30.5 M kB, inside the 44 M kB tree budget and the 46 GB cgroup.

Spec: `test/01_unit/app/cli/file_worker_pool_scaled_budget_spec.spl`
("a zero unit price falls back to the unit price and admits 4 workers on the
2026-11-22 host").

## Secondary: ~2.5 min per unit (report only)

Each single-module unit child rebuilds the surface for the whole closure
(~9,600 `phase2:surface:file:*` lines per unit in the log), so cost per unit is
dominated by a fixed per-process surface build, not by the one module lowered.
The Stage 2 at `53795406ba6` predates `cc595ec5935`
(`native_file_worker_adaptive_batch_v1`, 2026-11-22), so it ran
`unit picked=1`. Release head already batches up to 16 modules per unit for
closures above 32 modules, which amortises the surface build 16x; no
`SIMPLE_FILE_WORKER_BATCH` default change is needed here. Caching the surface
across unit children is not addressed.

## Unverified

- No compiler or spec was run (a 50 GB build was live on the host). The new
  `it` and the three existing specs that reference
  `FILE_WORKER_POOL_PER_FILE_WORKER_KB_V1` are unexecuted.
- The 4-worker figure is arithmetic over the logged inputs, not an observed
  admission line.
- The alias-reads-0 root cause is inferred, as stated above.
- The 6 GiB price rests on one host's 1.7-4.7 GB measurement at batch size 1;
  a 16-module batch may peak higher. The RSS guard and live commit admission
  remain the enforcement.
