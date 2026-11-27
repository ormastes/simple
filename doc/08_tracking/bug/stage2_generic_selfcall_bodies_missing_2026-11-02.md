# stage2_generic_selfcall_bodies_missing_2026-11-02

- Status: **revert-ready after stage3 self-build** (current source green; frozen stage2 still affected)
- Severity: P1 (phase-3 link: undefined generic-class helper symbols)
- Workarounds: WA-BC-1 (`SimpleRing<i64,i64>` helpers), WA-BC-2 (`Future.poll`) in
  `C:/dev/p3new/linkdry/WORKAROUNDS.md` (laneBC objects); keep all `@workaround` tags.
- Lane: waf-5 (brief B5, `doc/03_plan/bootstrap/workaround_fix_briefs_2026-11-02.md`)

## Symptom (frozen stage2 ef0681fc0e1)

Undefined `lib.nogc_async_mut.async_ring.simple_ring.SimpleRing.{create,_advance,...}` and
`lib.nogc_async_mut.async.future.Future.poll`: stage2 MIR skipped `is_generic_template` methods and mono
specialized only direct calls, so self-calls inside a specialization and static `SimpleRing<i64,i64>.create`
kept unmangled names with no body.

## Current source (origin/release/1.0.0 @ 9220ac55822)

PR #5732 (one erased body per generic fn) emits a body for every generic-class method. Spec
`test/01_unit/compiler/50.mir/generic_selfcall_facade_symbols_spec.spl` (in-process seed HIR+MIR) lowers a
`Ring<K,V>` with `static create` + self-calling `_slot -> _advance` used via `Ring<i64, i64>.create(3)`, and a
`Future<T>.poll` called through a `Future<i64>` field: every MIR call target naming a fixture method has a
defined MIR function with blocks. Green on current source (it was not red, so no source fix in this lane).

## Revert condition

Rebuild stage2 from a tip containing #5732 (or later); when the stage3 link resolves these symbols without the
laneBC objects, drop `laneBC_simple_ring.o` / `laneBC_future.o` from the rsp and let the revert loop remove tags.

## Observed but not owned here

The same fixture logs `unresolved method call: push` for `var r = Ring<i64, i64>.create(3); r.push(1, 2)`
(receiver of an unannotated static generic factory call has no type) and E-RTI-003 for the generic owner;
these are the B2/B4 receiver-typing shapes (methods-mir / ctor-mir lanes), not missing bodies.

## Phase-3 link evidence and runtime spec (lane BC, 2026-11-02)

The 11 undefined symbols are referenced unmangled from inside the `SimpleRing__*$i64_i64` specializations, from
`FileFiberTldrBridgeV1.create` (static `SimpleRing<i64,i64>.create`), and from
`AsyncBufferedWriter.close/write_all` (`Future.poll`). Stage2 reported `[mono] specializations=0` on the targeted
build. WA-BC-1/2 build tagged concrete copies (`WORKAROUND(p3-laneBC)`, worktree `C:/dev/wt/p3-bc`) and link them
without aliases. The ABI proof (field offsets, argument registers, i64 handle returns) is in
`C:/dev/p3new/objs_extra/laneBC/*.dis`.

Runtime regression spec: `test/02_integration/compiler/simple_ring_future_unspecialized_spec.spl` drives the
create/reserve/commit/provider_take/complete/release/cancel self-call chains and `Future.poll` Ready/Pending.
It was not run on this host.
