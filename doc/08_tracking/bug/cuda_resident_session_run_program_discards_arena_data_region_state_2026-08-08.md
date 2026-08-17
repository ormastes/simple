# CudaVmExecutor.run_source / ResidentSession.run_program discard arena DATA-region state every call

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Date: 2026-08-08
Found by: Task K5 (`CudaExec` notebook lane)

## Summary

`src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl`'s `CudaVmExecutor.run_source`
calls `build_svmg_arena(code, step_budget, entry_pc)` on every invocation.
`build_svmg_arena` starts from `zero_bytes(ARENA_TOTAL_SIZE)` and writes only
the SGP header + the new program's code bytes + the constant `LOG_CAP_OFFSET`
word — every other byte of the arena, including the whole DATA region beyond
the code and the entire LOG/RECORD ring region (`>= ARENA_DATA_SIZE`), is
zeroed and then uploaded to the device via `session.arena_write(arena)`,
which fully overwrites whatever the device held from the previous launch.

`src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl`'s
`ResidentSession.run_program` calls `self.executor.run_source(...)`
internally for each program, so it inherits the same behavior.

## Impact

`doc/05_design/app/tools/notebook_lanes_architecture.md` §4.4 states, for
both CUDA submodes:
- Resident: "VM globals in the DATA region carry state between cells."
- Per-launch: "the arena is retained across launches ... state persists via
  the arena."

Neither promise holds with a naive per-cell call to `run_source`/
`run_program`: any `STORE32`/`STORE8` a cell's program wrote into the DATA
region, and any `SYS_PUTC`/`SYS_RESULT` output accumulated in the LOG/RECORD
rings, is unconditionally zeroed by the next cell's `build_svmg_arena` call
before that cell even runs. Two sequential `ResidentSession.run_program`
calls, or two sequential `CudaVmExecutor.run_source` calls with no
intervening merge step, therefore behave as if each cell ran against a
brand-new, unrelated device — the opposite of what §4.4 promises for the
notebook lane's whole reason for using a resident/persistent-arena mode.

## Workaround (not a fix — lives in the caller, not here)

`src/lib/nogc_sync_mut/notebook/cuda_exec.spl`'s `CudaExec.run_program_with_persistence`
does NOT call `run_source`/`run_program`. It reimplements the same
build→write→launch→read sequence at the call site and inserts one extra
step between `build_svmg_arena` and `session.arena_write`: it copies the
previous cell's full output arena into the freshly-built one, byte-for-byte
at the SAME absolute offset, for every offset from `max(this cell's
data_off, the previous cell's data_off)` onward (both the STORE32/STORE8
DATA-region bytes and the LOG/RECORD ring beyond `ARENA_DATA_SIZE` use
absolute arena addressing, confirmed against a live device — an earlier
draft of this splice instead copied by offset RELATIVE to data_off under the
wrong assumption that addresses shift with code length, which silently
shifted every persisted byte by (new data_off - old data_off) and corrupted
values). This is only correct because `CudaExec` owns the entire inter-cell
sequencing itself; it does not fix `run_source`/`run_program` for any OTHER
caller (e.g. a future non-notebook consumer, or a caller wanting resident's
"true" ring-polling behavior once the `cuMemHostAlloc`/watchdog-attribute
SFFI gap `cuda_resident_session.spl` already documents is closed).

## Suggested fix

Give `CudaVmExecutor` (or `ResidentSession`) an explicit persistence seam —
e.g. `run_source_preserving_data(source, step_budget, entry_pc,
prior_arena: [u8]) -> SvmgRunOutcome`, or simply expose the raw output arena
on `SvmgRunOutcome` so callers can implement the splice without duplicating
the launch sequence (as this file's `CudaExec` currently must). Either way
the DATA/LOG/RECORD persistence contract design §4.4 promises should live in
the shared executor, not be re-derived by every caller.

## Files

- `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl` (`run_source`, `build_svmg_arena`)
- `src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl` (`ResidentSession.run_program`)
- `src/lib/nogc_sync_mut/notebook/cuda_exec.spl` (workaround: `run_program_with_persistence`)

## 2026-08-08 follow-up: root-cause fix landed

The suggested fix above landed: `cuda_vm_executor.spl` now exposes
`run_source_persisting_data(source, step_budget, entry_pc, prior_arena,
prior_data_off)`, backed by a `build_svmg_arena_persisting_data` helper.
`cuda_exec.spl`'s `run_program_with_persistence` now calls this executor
method directly instead of re-deriving the splice at the call site.

An intermediate version of `build_svmg_arena_persisting_data` copied the
persisted region **relative to `data_off`** and was a real regression
(broke this file's own previously-passing spec: the persistence check
started returning false). Corrected to the same absolute-offset copy this
doc's original workaround section already documented as correct
(`copy_start = max(data_off, prior_data_off)`, no relative shift).

Verified: `test/02_integration/app/tools/notebook/cuda_exec_spec.spl` —
4/4 PASS on live dual-GPU hardware (RTX A6000 + TITAN RTX,
`SIMPLE_MODULE_LIMIT=4000` workaround for the unrelated pre-existing
module-count-limit infra issue), lint clean.
