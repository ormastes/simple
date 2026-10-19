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
