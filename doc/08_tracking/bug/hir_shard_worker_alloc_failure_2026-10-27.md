# HIR shard workers die in an allocation abort (host commit exhausted)

**Status:** open (admission fix + exit hint on branch `work/hir-shard-oom`) — P0
**Id:** `hir_shard_worker_alloc_failure_2026_10_27`

## Symptom

Phase-3 whole-program native-build, stage2 `C:/dev/p3new/stage2.exe`
(sha 6b0ba5f3, source release `824ab2671ba`), Windows, 128 GB RAM, commit
limit 136 GB, env `SIMPLE_HIR_SHARD_WORKER_KB=6000000`,
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=96000000`, threads 80 -> 8 HIR shards.
At ~313 s `buildwp3.log.err:2`: `memory allocation of 6291456 bytes failed`,
worker exit `-1073740791` (0xC0000409), 0 modules claimed;
`buildwp3.log:71229-71230`: `measured worker peak commit=10989479 kB (static
estimate 6000000 kB, previous run 0 kB)`, `completed_workers=0
failed_workers=9 failed_modules=1405`.

## Which allocator prints it

Rust std's default `handle_alloc_error` hook (stage2 links the Rust runtime:
`RUST_BACKTRACE` and `rustc/574ff7d9` strings are in the binary; the next err
line is Rust's `note: run with RUST_BACKTRACE=1`). The global allocator is
`System` -> `HeapAlloc`; a 6 MiB request goes straight to `VirtualAlloc`
commit, so it fails only when the **system commit limit** is reached. The abort
is `__fastfail` = 0xC0000409.

## Cause (not a per-child cap)

Candidates excluded:
- No job memory limit: shard children are spawned with only
  `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE` (`src/runtime/runtime_process_owned.c:4741`,
  `runtime_process.c:536,895`). `ProcessMemoryLimit` exists only in the Rust
  test sandbox (`src/compiler_rust/runtime/src/sandbox/windows.rs:72`).
- `SIMPLE_GLOBAL_DATASET_MAX_BYTES` set per child
  (`native_build_main.spl:1049`) is a soft eviction bound in
  `src/lib/nogc_sync_mut/mem/global_dataset.spl:126,151`, never an abort.
- No RSS guard acts on running workers; the pool loop
  (`native_build_main.spl:1036-1057`) only gates new spawns.

Mechanism: the pool prices each worker at
`max(static, recorded_peak, observed_peak)` (`native_build_main.spl:1040`).
First run, so no peak record: est = 6 GB. At warmup every slot is admitted in
one pass with `live_private` entries of 0 (`:1057`), so
`shard_commit_spawn_admit_v1` (`shard_mem_clamp.spl:310`) needs 8 x 6 = 48 GB
<= 80.4 GB free - 24 GiB reserve. All 8 then grew to ~11 GB commit
(8 x 11 = 88 GB + 4.6 GB coordinator) while only 80.4 GB was free at
admission -> the commit limit ran out and every worker aborted. "Tens of GB
free" was sampled after the workers died (the `.cap` file only has a single
end sample, `796s tree_GB=1.2`). Same class as the s3-wa note at
`shard_mem_clamp.spl:285`.

## Safe env for the current stage2

`SIMPLE_HIR_SHARD_WORKER_KB=12000000` (>= measured 10,989,479 kB peak +
margin). Admission then fits 4 workers in 80 GB - 24 GiB (4 x 11 = 44 GB).
Also stop other large builds on the host; the reserve is the only guard.

## Fix

- `shard_commit_unmeasured_estimate_kib_v1`: with no recorded peak, price a
  worker at 2x the static estimate (warmup admits 4, not 8, in this incident).
- `shard_worker_exit_hint_v1`: a 0xC0000409 worker exit now prints
  "allocation-failure abort ... host commit limit exhausted; set
  SIMPLE_HIR_SHARD_WORKER_KB to at least the measured worker peak commit".
- Spec: `test/01_unit/app/cli/shard_commit_admission_spec.spl`
  red (9/10, warmup admits 8) -> green (10/10).

Open: no running-pool guard kills/requeues a worker when live headroom drops
below the reserve; admission alone cannot stop growth after spawn.
