# Stage 2 HIR shard owners killed at process-tree RSS cap (worker peak 25.6 GB vs 9 GB estimate)

- Date: 2026-11-20
- Status: fixed
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

## Fix (2026-11-24)

Root causes diagnosed and fixed in `src/app/cli/native_build_main.spl` and
`src/app/cli/shard_mem_clamp.spl`:

1. **Peak path parent & unsafe raw scope filename (`previous run 0 kB`)**:
   - `native_build_path_parent_v1` only checked `/` and failed on Windows `\`
     paths; updated to split on the last `/` or `\` while preserving `/` and
     Windows drive roots (`X:/`, `X:\`).
   - `run_ledger_shards` and `native_build_recorded_worker_peaks_v1` embedded raw
     `SIMPLE_FRONTEND_CACHE_SCOPE` (which contains `:`, `;`, `=`, `/`) into
     `{parent}/{label}.{producer_key}.peak_kib`, failing on Windows `:` and
     creating nonexistent POSIX subdirectories `/`. Extracted
     `native_build_peak_producer_key_v1` (`"unknown"` if empty, else 16-char
     lowercase SHA-256 hex via `sha256_text`), `native_build_peak_record_path_v1`
     (no `//` UNC join), `native_build_peak_record_read_v1`, and
     `native_build_peak_record_write_v1` (creates missing parent directories,
     persists monotonically without shrinking heavy-run records, and warns if
     final persistence fails). `run_ledger_shards` also persists observed worker
     peaks incrementally during headroom probes so watchdog kills retain peaks
     for the next run.
2. **Wave-0 over-admission & MIR recorded-peak wiring**:
   - `run_ledger_shards` previously checked only `host_commit_avail_kib()` (which
     includes swap on Linux and returns `-1` on unknown hosts), ignoring active
     enclosing tree RSS caps (`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB`,
     `SIMPLE_PROCESS_TREE_RSS_CAP_KIB`, cgroup `memory.max`) minus coordinator
     peak RSS. Added `shard_pool_tree_worker_budget_kib_v1`,
     `shard_pool_live_tree_worker_budget_kib_v1`,
     `shard_pool_estimate_budget_cap_kib_v1`, `shard_pool_tree_admit_v1`,
     `shard_pool_spawn_admit_v1`, and `shard_pool_wave0_admitted_count_v1` in
     `src/app/cli/shard_mem_clamp.spl`, enforcing both host commit headroom and
     enclosing tree budget across wave 0 and refills (counting unmeasured live
     slots when probes are unavailable).
   - Wired `native_build_mir_admission_budget_kb_v1` and
     `native_build_mir_parent_tighten_v1` into MIR initial concurrency selection
     so MIR shard sizing also consults persisted worker peaks and coordinator peak.

Verification (`--mode=interpreter`):
- `test/01_unit/app/cli/shard_peak_persistence_spec.spl`: 6/6 passed
- `test/01_unit/app/cli/native_build_cache_scope_dir_spec.spl`: 4/4 passed
- `test/01_unit/app/cli/native_build_shard_admission_spec.spl`: 11/11 passed
- `test/01_unit/app/cli/native_build_mir_output_preflight_spec.spl`: 13/13 passed
- `test/01_unit/app/cli/shard_commit_admission_spec.spl`: 12/12 passed
- `test/01_unit/app/cli/shard_mem_clamp_spec.spl`: 40/40 passed
- `test/01_unit/app/cli/build_parallel_perf_mem_regression_spec.spl`: 11/11 passed
- `test/01_unit/app/cli/bootstrap_capsule_shard_wiring_spec.spl`: 7/7 passed
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: `STATUS: PASS direct-env-runtime-guard`
