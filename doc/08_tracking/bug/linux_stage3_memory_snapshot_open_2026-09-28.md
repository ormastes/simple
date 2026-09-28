# Linux Stage 3 cannot establish durable memory snapshot

- Status: OPEN
- Date: 2026-09-28
- Severity: RC bootstrap blocker
- Platform: `aarch64-unknown-linux-gnu`
- Release line: `release/1.0`

## Observation

The bounded Linux bootstrap attempt built and admitted a fresh Stage 2, then
passed its hello gate with a 24 GiB virtual address limit. Stage 3 parsed all
717 modules and failed immediately at HIR entry:

```text
[BOOTSTRAP-PHASE] +157084ms phase3:hir_typecheck:start
error: in-process native-build: SIMPLE_MEM_SNAPSHOT_FILE could not be established safely
```

The failure manifest is retained in the Linux worktree at
`build/bootstrap/scheduler/bootstrap-20260928T094745Z-4115784/failure-manifest.env`;
the log is `build/bootstrap/logs/aarch64-unknown-linux-gnu/stage3-native-build.log`.
The manifest records `stage2_qualification_status=passed`,
`stage_engine_status=failed`, and invalidated descendants. Stage 4 and the
release binary were not qualified.

The Stage 3 command transcript sets
`SIMPLE_MEM_SNAPSHOT_FILE=/home/yoon/release-rc1-linux-wt/build/bootstrap/stage3/aarch64-unknown-linux-gnu/memory-snapshot-v1.events`.
That parent directory existed with mode 0700 and no snapshot file remained.
The diagnostic is emitted when `mem_snapshot_begin()` returns -1. Inspection
of the admitted Stage 2 executable found the cause: its
`mem_snapshot_begin()` call to `rt_mem_snapshot_open` passes the Simple `text`
object in register `x0` and zero in `x1`. The runtime entrypoint requires a
byte pointer in `x0` and a positive byte length in `x1`, so it rejects the
call before creating the file. The source had declared this raw SFFI function
with a single `text` parameter. The phase-profile call and the three text
arguments to `rt_mem_snapshot_record` had the same ABI mismatch.

The integration branch now passes each text as `rt_string_data(value)` and
`rt_string_len(value)`, matching the runtime's raw pointer/length ABI. This
patch has not yet passed a new Stage 2/3 bootstrap transaction.

## Next bounded investigation

Run one new canonical bootstrap transaction in a fresh session and require
Stage 3, Stage 4, and the full release qualification gates to pass. The current
session has reached its three-cycle verification limit for this lane.
