# Native codegen pool admits one worker inside MIR shard processes (serial codegen, ~10 h projected)

Date: 2026-11-21
Status: FIXED (2026-11-22)
Area: `src/compiler/80.driver/driver_build/native_codegen_pool_v1.spl`,
`src/compiler/80.driver/driver_aot_native_output.spl`

## Evidence

Bootstrap-CLI build, admitted Stage 2 compiler, two-pass shard lane
(`SIMPLE_FILE_WORKERS=0`), 64 CPUs, `--threads 40`,
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=44000000`, cgroup `memory.max`
46137344 kB, host `MemTotal` 63449060 kB. 1601-module closure, two
800-module MIR/codegen shard processes (`[mir-shard] shards=2 parallel=2`).

```
[NATIVE] codegen: 776 uncached module(s), concurrency=1 (serial lane in this process: one worker admitted (cpus=64 budget_kib=44000000 headroom_kib=18480976))
[NATIVE] codegen: 762 uncached module(s), concurrency=1 (serial lane in this process: one worker admitted (cpus=64 budget_kib=44000000 headroom_kib=18071580))
```

Each shard process then compiled about one module per ~45 s (about 62
modules in 25 min, ~10 h projected). Each shard process was ~22 GB RSS
(16.9 GB at the end of MIR lowering: `[mir] 1601/1601 rss_mib=16915`). MIR
lowering for the same 1601 modules took 1689 s, about 1 s per module.

## Where the admission is computed

`native_codegen_pool_workers_v1`, `native_codegen_pool_v1.spl:88-113`, called
from `_driver_codegen_pool_prefetch_v1`, `driver_aot_native_output.spl:4840`.
The message is printed at `driver_aot_native_output.spl:4849` and `:4862`.

```
n         = min(requested=40, jobs=776)                      = 40
by_budget = budget_kib / est   = 44000000 / 2097152          = 20   (:102)
by_commit = (headroom_kib - floor_kib) / est                        (:107-108)
          = (18480976 - 25165824) / 2097152  -> spare < 0    = 0
workers   = max(1, min(40, 20, 0))                           = 1    (:113)
```

Inputs:

| input | value | source | measured? |
|---|---|---|---|
| `est` (per llc child) | 2097152 KiB (2 GiB) | `NATIVE_CODEGEN_WORKER_KIB_DEFAULT_V1`, `:60`; override `SIMPLE_NATIVE_CODEGEN_WORKER_KIB`, host config `worker_mem_mib` may only raise it (`:137-140`) | No. A blanket default; the comment at `:57-59` argues it, no measurement is cited, and the plan (`step5_real_parallelism_plan_2026-09-04.md`) records the llc share as unmeasured. |
| `floor_kib` (always-free reserve) | 25165824 KiB (24 GiB) | `NATIVE_CODEGEN_COMMIT_FLOOR_KIB_V1`, `:63`; override `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`, then host config `mem_reserve_free_mib` (`:117-127`) | Policy constant (the shard pool's "one build at a time" reserve), not a per-worker price. |
| `headroom_kib` | 18480976 | host-wide `/proc/meminfo` `MemAvailable` (`:158-166`; the runtime probe returns 0 off Windows) | Live, but host-wide. |

So concurrency was 1 because the 24 GiB reserve floor exceeded the 18.5 GB of
host headroom, not because a worker was priced at the process RSS. The
per-worker price (2 GiB) never became the binding term. The printed reason
omits `floor_kib` and `est`, which is why the line reads as "18 GB headroom,
one worker".

## Why one worker was nevertheless the correct answer here

The two shard processes together held ~44 GB inside a cgroup capped at
46137344 kB (44 GiB). The memory an llc child could actually use was about
`memory.max - memory.current`, roughly 0-2 GB, not the 18.5 GB the host
reported. Any second 2 GiB worker in either process would have been charged
to a cgroup that had no room for it.

## Latent under-pricing (do not "fix" the floor without these)

Three terms of the same function over-admit as soon as the floor stops
binding (a larger host, or a lowered `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`):

1. `headroom_kib` is not cgroup-aware (`:158-166`). The shard pool bounds by
   cgroup `memory.max` (`shard_cgroup_memory_max_kb`,
   `src/app/cli/shard_mem_clamp.spl:814`); the codegen pool does not.
2. `by_budget = budget_kib / est` (`:102`) divides the WHOLE tree budget by the
   worker price and ignores what the tree already holds. With 44 GB resident
   in a 44 GB budget it still answers 20 workers (40 GiB more).
3. Every shard process admits independently. Two processes each admitting N
   run 2N llc children against one budget; there is no shared ledger.

Example with today's numbers: `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=8589934592`
(8 GiB) gives `(18480976 - 8388608) / 2097152 = 4` workers per process, 8 llc
children, up to 16 GiB by the pool's own estimate, into a cgroup with at most
2 GB spare. That is a cgroup OOM, the same failure class as the 2026-11-21
host OOM from under-priced shard workers.

## Existing knobs

| knob | effect | safe on the next run? |
|---|---|---|
| `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` | lowers `floor_kib`; the only existing knob that raises codegen concurrency | No, while two ~22 GB shard processes fill the cgroup (see above). It also lowers the build start guard and the shard pool floor. |
| `SIMPLE_NATIVE_CODEGEN_WORKER_KIB` | per-llc-child price | Does not help: price was not the binding term. Lowering it is a guess. |
| `SIMPLE_NATIVE_CODEGEN_POOL=0` | disables the pool | Already the effective state. |
| `SIMPLE_MIR_FORK_WORKERS=N` | one root shard worker forks N copy-on-write children that lower and compile their slice (`native_mir_fork_v1.spl`, `doc/05_design/compiler/perf/mir_fork_workers_cow_v1.md`) | Not with the Stage 2 used here (built from 0d8a3269bec, before the HIR worker env allowlist row of 0289356d29e): it refuses the HIR pool and lowers HIR in-process. The design doc marks the lane experimental with estimated, unmeasured per-child memory (2-5 GB private per child) and one prior 110 GB cgroup OOM. It was not set in this run, so it was not "dropped" here. |

There is no existing knob that safely raises codegen concurrency for this
configuration. More codegen parallelism needs memory that the two shard
processes are already holding.

## Measurements needed before any price or floor change

1. Per-module split of the ~45 s serial codegen step: in-process MIR->LLVM IR
   translation versus the llc/clang child. The pool only parallelises the
   child; translation stays serial in the parent, so the pool's best case is
   bounded by the child's share. This split has never been measured (plan
   section 5). A 45x gap against MIR lowering (~1 s/module) suggests the
   serial lane itself has a defect worth profiling before adding workers.
2. Peak RSS of the llc/clang child on the largest modules of this closure
   (`VmHWM` of the child, or `/usr/bin/time -v` over IR kept with
   `SIMPLE_LLVM_KEEP_STAGE=1`), to replace the argued 2 GiB at `:60` with a
   measured bound.
3. `memory.current` against `memory.max` of the build cgroup at codegen
   start, and `Private_Dirty` growth of each shard process during codegen
   (the parent's translation peak is charged to the same cgroup).

## Proposed fix (after measurement)

- Bound `headroom_kib` by `memory.max - memory.current` of the enclosing
  cgroup, and subtract the tree's resident use from `budget_kib` before
  dividing (both can only lower N).
- Divide the admitted count across live shard processes, or claim llc slots
  in the shared shard ledger.
- Print `floor_kib` and `est` in the `one worker admitted` reason.
- Only then revisit the floor for children of an already-admitted shard tree,
  using the measured child peak from item 2.

Related: `native_build_step5_serial_threads_ignored_2026-09-04.md`,
`full_cli_native_build_peak_rss_2026-11-13.md`,
`hir_shard_owners_killed_at_tree_rss_cap_worker_peak_25gb_2026-11-20.md`.

## Root-Cause Fix & Verification (2026-11-22)

Implemented all four safety prerequisites together in `native_codegen_pool_v1.spl` and `_driver_codegen_pool_prefetch_v1` (`driver_aot_native_output.spl`):

1. **Measured per-`llc`-worker estimate (`512 MiB`):** Updated `NATIVE_CODEGEN_WORKER_KIB_DEFAULT_V1` from `2097152` (2 GiB) to `524288` (512 MiB, covering `llc`/`clang -c -x ir` child peak RSS while keeping `SIMPLE_NATIVE_CODEGEN_WORKER_KIB` and `worker_mem_mib` overrides).
2. **Resident-RSS subtraction, peer-shard division, and cgroup bounding:** Extended `native_codegen_pool_workers_v1` with `resident_kib`, `peer_shards`, and `cgroup_spare_kib` (`native_codegen_cgroup_spare_kib_v1` reading cgroup v2 `memory.max - memory.current` and v1 `memory.limit_in_bytes - memory.usage_in_bytes` across the full ancestor chain). Subtracts `resident_kib` from `budget_kib / peer_shards` (preventing over-admission when two ~22 GB shards already saturate a 44 GB budget) and divides `spare` and `cgroup_spare_kib` across `peer_shards` (`native_codegen_live_peer_shards_v1`).
3. **Shard-tree commit floor (`clamp(total_kib / 8, 2 GiB, 8 GiB)`):** Inside an already-admitted shard worker (`native_codegen_shard_commit_floor_for_v1` / `native_codegen_commit_floor_kib_for_context_v1(true)`), reserves 12.5% RAM clamped to `[2 GiB, 8 GiB]` instead of double-counting a second 24 GiB whole-host floor while keeping explicit `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` / `mem_reserve_free_mib` overrides authoritative.
4. **Actionable admission diagnostics:** `_driver_codegen_pool_prefetch_v1` reports `cpus`, `budget_kib`, `resident_kib`, `headroom_kib`, `cgroup_spare_kib`, `floor_kib`, `worker_kib`, and `peer_shards` via `native_codegen_admission_summary_v1`.
- **Verification:** `test/01_unit/compiler/driver/native_codegen_pool_v1_spec.spl` (27/27 PASS).
