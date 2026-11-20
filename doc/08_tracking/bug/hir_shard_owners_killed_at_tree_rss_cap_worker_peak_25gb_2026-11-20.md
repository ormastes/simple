# Stage 2 HIR shard owners killed at process-tree RSS cap (worker peak 25.6 GB vs 9 GB estimate)

- Date: 2026-11-20
- Status: open
- Lane: phase-2 bootstrap, WSL ubuntu-p2, commit 6d8ca1e90d30,
  `--full-bootstrap --stop-after-stage2 --mode=dynload --jobs=12 --no-mcp`,
  `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=50331648` (48 GiB) on a 64 GB host.
- Row: `compiler_cli_build` FAIL after 3563 s (max_rss 20.3 GB); verdict ABORTED.

## Symptom

```
[hir-shard] owner=0/3@0 status=CRASH exit=-1 claimed=605
[hir-shard] owner=1/3@0 status=CRASH exit=-1 claimed=455
[hir-shard] owner=2/3@0 status=BLOCKED ... frozen retirement receipt invalid (terminal=true tree_empty=false leader_reaped=true exit=-1 signal=15)
[hir-shard] measured worker peak commit=25609632 kB (static estimate 9000000 kB, previous run 0 kB)
failed module: CRASH src/compiler/80.driver/driver.spl
failed module: CRASH src/os/apps/smux/runtime_connection_recovery_v5.spl
```

## Evidence

- HIR tree budget: `declared 50331648 kB ... effective 44599583 kB`; admission
  estimate 9,000,000 kB per worker, coordinator reserved 8,300,820 kB, 3 workers
  admitted. Measured worker peak was **25,609,632 kB** (2.8x the estimate):
  3 x ~25 GB + coordinator cannot fit 44.6 GB.
- Host timeline (`~/log/p2_rss.log`): used 45-47 GB through 11:41-11:49,
  48.6 GB at 11:50:13, **49.0 GB at 11:51:08** (= the 48 GiB cap), 2.1 GB at 11:52:03.
- Ledger (`.../cache/compiler-tools/stage2/<exe>/<sources>/`): the CRASH rows are
  each owner's **last claim** (in flight): owner 0 claimed
  `runtime_connection_recovery_v5.spl` 11:51:06, terminal CRASH 11:51:19;
  owner 1 claimed `driver.spl` 11:51:18, terminal CRASH 11:51:28; owner 2's last
  claim 11:51:28, then SIGTERM teardown. `exit=-1` = no normal exit.
- The two modules are tiny (187 and 67 lines); they are victims, not crashers.
- No kernel OOM lines in dmesg; the kill came from the bootstrap tree-RSS guard
  window, not the kernel.

## Owner 2 receipt

`tree_empty=false` after SIGTERM is the fail-closed check in
`src/app/cli/worker_hir_owner_v1.spl:157` refusing to freeze a receipt while a
descendant is still alive during the abort teardown. It is a consequence of the
abort, not the root cause; not changed here.

## Root cause

Memory policy: HIR worker admission uses a static 9 GB estimate with
`previous run 0 kB` (no recorded peak), so it admits 3 workers whose real peak
is ~25.6 GB each. The RSS guard then kills the tree at the cap.

## Rerun knobs

```
SIMPLE_HIR_SHARD_WORKER_KB=26000000   # -> 1 HIR worker under the 44.6 GB effective budget
```
(`18000000` admits 2 workers but is below the measured peak; only use if the
peak is recorded lower on the next run.) Alternative: `SIMPLE_HIR_SHARDING=0`.

## Follow-up

- Persist the measured worker peak so the next run's admission uses it
  (log shows `previous run 0 kB`).
- Parse alone took 2,705 s; tracked separately in
  `hir_worker_prologue_exceeds_internal_timeout_2026-11-20.md`.
