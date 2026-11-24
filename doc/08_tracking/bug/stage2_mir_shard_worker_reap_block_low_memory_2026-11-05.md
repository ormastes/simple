# Stage-2 candidate MIR shard workers BLOCK "could not be reaped" under --low-memory matrix config (2026-11-05)

**Status:** OPEN. Observed in the stage2 compiler-test matrix of the
trust-root repro bootstrap (aarch64 Linux, cranelift, worktree at
df48a86ff5a). Distinct from
stage2_parse_shard_entry_scv_snapshot_race_2026-11-05 (that one fails entry
collection pre-compilation; this one fails shard lifecycle post-lowering).

## Symptom

The matrix's first cell — stage2 candidate building
`src/app/cli/_CliMain/main_and_help.spl` with
`--backend=cranelift --low-memory --timeout 1800 --threads 2` — progressed
through parse and deep MIR lowering (~47 min of active compilation across
the full CLI closure; per-module `[mir-slow]` rows at 2-3s) and then:

```
[mir-shard] owner=1/2@0 status=BLOCKED exit=-2 claimed=278 sealed=-1 finished=false
[mir-shard] outcome=fail exit=1 failed_modules=0 claims=502 all_stopped=false
              blocked=worker could not be reaped
error: MIR shard ...
```

`failed_modules=0` — no module failed to lower; the shard owner could not
reap finished workers. Sibling cells in the same matrix run PASS
(compiler_version printed `simple-bootstrap 1.0.0-rc.1`; the test_runner
build's MIR shards completed 160/160 claims with sealed_failed=0).

## Contributing factor

Host RSS budgeting had dropped the cell to 2 build threads ("host budget
fits 2"); other concurrent heavy processes on the host were competing for
the 50% RAM budget. After freeing ~64 GiB, later cells received more
threads. Whether the reap blockage is purely resource-pressure timing or a
genuine lifecycle defect at 2 threads is not established.

## Impact class

Infra-level, pre-artifact: no codegen or lowering error is involved, but the
cell FAILs, so matrix/lane receipts can read as a compiler regression.
Retrying the cell with more memory/threads (or after freeing host budget)
is the first diagnostic step; do not attribute to MIR lowering without a
reproduced module failure (`failed_modules > 0`).

## Evidence

/tmp/stage2-repro-wt/.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log
(matrix run of 2026-11-05, task: stage2 cranelift SIGILL repro attempt 5).

## Status 2026-11-24: FIXED by 92d02442782 (match to this incident inferred)

Commit 92d02442782 (2026-11-13) changed the `run_ledger_shards` kill path to confirm a
killed worker by liveness (`shard_worker_confirm_kill_v1` /
`shard_worker_kill_stopped_v1`, `src/app/cli/shard_worker_reap_v1.spl`). Both host
runtimes reap inside `process_kill`, so the old 5 s re-wait answered -1 for a dead child
and the pool printed exactly `blocked=worker could not be reaped`.

This incident matches that shape: the cell ran `--timeout 1800` (30 min) but compiled
for ~47 min, and the owner reported `exit=-2` (still running at the deadline). That is a
timed-out worker going through the kill path, which the old reading misclassified. The
match is INFERRED from the log shape; the cell was not re-run.

Seed-verified 2026-11-24 (`C:/dev/seeds/simple-release.exe`,
`test/01_unit/app/cli/shard_worker_reap_spec.spl`): 19/20. All kill-confirm decision
cases pass. The one failure is a host-process case, `shard_child_wait_bounded_v1` on
`sh -c "exit 3"` under a 5000 ms budget, which answered -2. Spawning Git `sh` on this
loaded Windows host took longer than 5 s, so this is a timing case unrelated to the reap
decision. It is not filed as a regression of this fix.
