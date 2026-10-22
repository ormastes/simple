# Stage 2 matrix full-CLI build peaks above 40 GiB in MIR

- Status: OPEN
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu, 121 GiB host
- Blocks: `stage2-compiler-tests` `compiler_cli_build` under the lane's 40 GiB
  systemd scope (MemoryMax=40G, MemorySwapMax=0).

## Observation

With the HIR fixes 267d9e15084 / c030d481171 / 534a2b3e380 the Stage 2
compiler (sha256 `552150e76c3d73c5a50d83a21d18c283758c7d2bd666de8e23890c7ea95d15d8`)
for the first time lowered all 2702 full-CLI modules through HIR with no
worker crash (worker + main HIR ~38 min). It then entered MIR lowering
(`[mir-lower] WARNING: struct/class name ... re-registered with a DIFFERENT
field list` for FileStat, Task, CostEstimate, JoinPoint, Dependency) and the
process tree grew to `peak_rss_kib=41814840` before the scope's OOM killer
fired (`campaign_interrupted status=143`, journal: `oom-kill`). The task's
own ceiling is 50331648 KiB, so the bootstrap would have allowed it.

Run r8, `.simple/storage/build/bootstrap-r8/stage2-compiler-tests/
aarch64-unknown-linux-gnu/verification/campaign.*/process.env`.

## Not yet established

Whether MIR retention for the full CLI is bounded below 48 GiB at all (a
sibling lane recorded an 83 GiB MIR retention failure).

## Stage 3 (bootstrap_main) shows the same growth

Stage 3 resumed from r8 (`--resume-stage3-from-admitted`, admitted Stage 2
sha256 `552150e7...15d8`, one thread) with the elevated tree cap
`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=46137344` /
`SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB=52428800`:

| time | RSS (KiB) | HIR modules |
|---|---|---|
| 16:24:27 | 39,517,324 | 653 / 1315 |
| 16:25:27 | 41,106,488 | 688 |
| 16:26:27 | 42,454,456 | 726 |
| 16:27:27 | 43,874,968 | 758 |
| 16:28 (killed) | peak 46,284,808 | 771 (`compiler.semantics.join_point_model`) |

Watchdog verdict `status=rss-containment-unverified`, elapsed 1095 s of HIR.
Growth is ~1.4 GB per 35 modules and linear, so the remaining 544 modules
need roughly +22 GB (~68 GB total before MIR). The coordinator's memory lane
attributes ~14.9 GB of it to `driver_log_typed_hir_abi_interface_v1`
(driver_hir_pipeline_lowering.spl:207), which runs per module only because
`SIMPLE_COMPILER_PHASE_PROFILE=1` is hard-coded into the Stage 3 argv
(resume-stage3-from-admitted.sh:911, stage3-native-build-worker.sh:109) and is
part of the admitted args digest. The default Stage 3 cap (5.86 GB floor)
killed the two earlier attempts at HIR module 32.

## Stage 3 r11 (r8 base + 5bc133fb1c2 ABI-trace opt-in)

Admitted Stage 2 sha256 `70c5d97fa251f3ae0ce0880b01a9d6ae005e979bfc31511eb22e67e4944f6c61`
(Stage 2 build 587 s, peak 2.62 GB). Stage 3 resume with headroom/MemoryHigh
55 GiB, MemoryMax 56 GiB, watchdog cap 54 GiB, ceiling 55 GiB, launched
17:38:20 with 114 GB available:

| time | RSS (KiB) | HIR modules | host avail |
|---|---|---|---|
| 17:46:48 | 19,845,520 | 268 | 94G |
| 17:48:49 | 25,837,032 | 395 | 89G |
| 17:51:49 | 34,234,924 | 528 | 79G |
| 17:54:49 | 40,219,000 | 680 | 71G |
| 17:56:49 | 43,846,508 | 764 | 67G |
| 17:57:49 | 47,958,448 | 805 | 58G |

The live headroom guard stopped it at 17:58:07 at HIR 808/1315
(`runtime_headroom_watch_available_kib=57667656`, unit memory peak 47.1G,
23 min 38 s CPU). Slope ~57 MB/module, the same as the r8 run without the
ABI-trace change. Host availability fell ~7 GB faster than Stage 3's own RSS
because two `native-build` processes from another lane (PIDs 449611, 449861,
~11 GB together, started 17:54 using this run's Stage 2 binary) ran
concurrently. Projected full-HIR RSS at this slope: ~78 GB.
