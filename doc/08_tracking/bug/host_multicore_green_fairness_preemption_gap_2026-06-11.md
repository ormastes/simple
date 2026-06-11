# Host Multicore Green Fairness and Preemption Gap

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The hosted `multicore_green_spawn` lane now has real runtime-pool evidence:

- `used_runtime_pool()` and `pool_used=N/N` are enforced in profile rows
- hosted reports require `queue_model=work_stealing`
- Go-vs-C-vs-Simple stress evidence is current

That is enough for bounded CPU-parallel M:N candidate claims, but it is still
not enough for full Go-like scheduler parity on the host runtime.

The remaining host-side gap is the same one called out in the selected
requirements, research, and architecture docs:

- fairness/preemption is not yet proven end to end for hosted multicore green

## Why This Is Still Open

Current hosted multicore-green evidence proves:

- runtime-pool ownership
- bounded parallelism
- work-stealing queue reporting
- fanout/fanin checksum integrity

Current hosted multicore-green evidence does not yet prove:

- long-running CPU work is preempted or yield-forced with a host-side contract
- host fairness semantics comparable to Go's scheduler under sustained loop load

Current hosted fairness/yield boundary now also includes:

- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl`
  proves that raw `thread_yield()` inside a hosted multicore-green task is not
  enough to create Go-like fairness: with hosted parallelism pinned to `1`, a
  long-running task that calls `thread_yield()` still keeps a later quick task
  unfinished during the first short observation window on both source-run and
  standalone native paths
- this narrows the remaining host gap from a vague fairness concern to a
  concrete implementation boundary: non-resumable pool tasks need automatic
  preemption, compiler-inserted yield points, or task-splitting semantics,
  because raw OS-thread yield does not hand queued multicore-green work to the
  same worker

Current hosted runtime mechanism behind that gap is now explicit:

- `src/runtime/runtime_pool.c` runs each accepted task through
  `rt_pool_worker_main -> task->entry(task->closure_ptr)` and does not return
  to `rt_pool_pop_task(...)` until that closure returns
- the current host compensation hook in
  `src/compiler_rust/runtime/src/executor.rs` only marks real blocking sleep
  through `rt_thread_sleep -> rt_pool_worker_block_begin/end`; it does not make
  CPU loops resumable
- so the hosted pool has work stealing and bounded worker ownership, but not
  resumable task slices on the host lane
- this means host fairness cannot come from plain OS-thread yield alone; it
  needs compiler-inserted safepoints, runtime-managed preemption, or a model
  that breaks long work into requeueable slices

Current compiler insertion seam is also explicit:

- interpreter loops are centralized in
  `src/compiler_rust/compiler/src/interpreter_control.rs` through
  `exec_while`, `exec_loop`, and `exec_for`
- native/SMF loop lowering is centralized in
  `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` through the
  `HirStmt::While`, `HirStmt::Loop`, and `HirStmt::For` lowering branches
- that MIR lowering layer is the narrowest existing place to insert a future
  host safepoint or compiler-yield call without inventing a second loop model

Current hosted fairness/preemption gap coverage now includes:

- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl`
  keeps the remaining host monopolization gap explicit: with hosted
  parallelism pinned to `1`, a tight CPU task still keeps a later quick task
  unfinished through the first short observation window on both source-run and
  standalone native paths
- this is the current executable proof that hosted multicore-green still lacks
  automatic Go-like preemption or compiler-inserted yield points for non-
  yielding tight loops

Current hosted blocking-compensation evidence now includes:

- `test/03_system/feature/usage/multicore_green_blocking_compensation_gap_spec.spl`
  keeps the hosted compensation-worker fix covered: with hosted pool
  parallelism pinned to `2`, two sleeping tasks still allow a third quick task
  to complete within the first 30ms window on both source-run and standalone
  native paths
- blocking compensation now has executable hosted coverage; the remaining host
  parity gap is fairness/preemption

Current hosted bounded-parallelism regression coverage also includes:

- `test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl`
  now keeps the blocking-aware compensation fix pinned: a requested hosted
  parallelism of `2` stays at `2` under pure CPU saturation on both source-run
  and standalone native paths
- bounded parallelism now has executable hosted regression coverage; the
  remaining host parity gap is fairness/preemption, not oversubscription

SimpleOS has scheduler-facing timer/runtime/compiler safepoint coverage for its
green-carrier lane, but that is not the same as proving the hosted runtime-pool
lane has equivalent fairness/preemption guarantees.

## Current Evidence Boundary

Current positive hosted evidence:

- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

Current SimpleOS fairness/preemption evidence:

- `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`

These do not yet close the hosted-runtime parity claim.

## Exit Criteria

This gap can close only when the hosted multicore-green lane has executable
evidence for:

- fairness/preemption or an equivalent enforced host-side yield contract
- and the mechanism must be tied to one of the concrete seams above: runtime
  worker preemption, compiler-inserted loop safepoints, or resumable task
  slicing in the hosted pool

That evidence must be tied into the canonical multicore-green feature tracking
and must not rely on SimpleOS-only scheduler proofs.
