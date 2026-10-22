# Stage 3 sharded route: every HIR shard worker fails on SIMPLE_MEM_SNAPSHOT_FILE

- Status: FIXED (guard landed; sharded Stage 3 re-run pending)
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Blocks: Stage 3 with `SIMPLE_NATIVE_BUILD_THREADS=8` (HIR shard workers).

## Observation

r13 Stage 2 compiler, Stage 3 sharded route (8 HIR workers). Every worker
exited `BLOCKED` before claiming a single module:

```
[ERROR]   SIMPLE_MEM_SNAPSHOT_FILE could not be established safely
[hir-shard] owner=0/8@0 status=BLOCKED exit=1 claimed=0 sealed=0 finished=false
[hir-shard] owner=1/8@0 status=BLOCKED exit=1 claimed=0 sealed=0 finished=false
...
HIR shard ledger claim failed
```

(`.simple/storage/build/bootstrap-r13/stage3/aarch64-unknown-linux-gnu/attempts/recovery-threads1-*/stage3-native-build.log.before-resume`
in the `simple-lane-boot4` lane.)

## Root cause

`run_ledger_shards` (`src/app/cli/native_build_main.spl`) spawns the workers
with the parent's environment, so all eight inherit one
`SIMPLE_MEM_SNAPSHOT_FILE`. `mem_snapshot_begin`
(`src/compiler/80.driver/driver_mem_snapshot.spl:57`) opens that path
`O_EXCL`, so only the first opener can ever succeed.

The streaming lowering path already handles this
(`driver_hir_pipeline_lowering.spl:1003-1009`): "Shard children only fill the
HIR cache and may share the parent's configured path; they must not open its
O_EXCL evidence descriptor or publish an incomplete terminal row", guarded
with `if not hir_shard_mode:`. The retained lowering path (`:1671`) called
`mem_snapshot_begin()` unconditionally. On failure it also called
`hir_shard_guard_block(...)`, which blocks the shared ledger, so the next
`hir_shard_begin` returned -1 and surfaced as "HIR shard ledger claim failed"
— a downstream symptom, not a second bug.

## Fix

Mirror the streaming guard on the retained path: a shard child never calls
`mem_snapshot_begin()`. Spec:
`test/01_unit/compiler/driver/hir_shard_mem_snapshot_guard_spec.spl` (both
call sites must carry the guard; RED showed 1 of 2 guarded).

Per-worker derived snapshot paths were considered and rejected: the documented
contract is that children do not publish memory-evidence rows at all, and N
partial evidence files would not be what the Stage-3 memory watchdog reads.

## Workaround without a Stage 2 rebuild

Unset `SIMPLE_MEM_SNAPSHOT_FILE` for the sharded attempt: `mem_snapshot_begin`
returns 0 (disabled) on an empty path. The sharded main process still runs the
rt_criticality blob validation, so bug
`stage3_rt_criticality_validation_memory_spike_2026_10_19` applies to it too.
