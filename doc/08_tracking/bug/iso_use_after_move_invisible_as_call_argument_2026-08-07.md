# Bug: `iso` use-after-move is invisible to the borrow checker when the second use is a call argument

- **Date:** 2026-08-07
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** medium (the headline "use-after-move of an `iso` value is
  caught" guarantee does NOT hold for the single most natural way a
  programmer would trigger it — passing the moved value to a function)
- **Found by:** WP-E2E, writing the missing end-to-end spec that drives real
  source text through `parse_full_frontend -> HirLowering -> MirLowering ->
  BorrowChecker.check_function`, connecting three previously-isolated specs
  (`borrow_check_spec.spl`, `iso_move_pipeline_spec.spl`,
  `iso_parse_pipeline_spec.spl`).

## The actual defect

`BorrowChecker.analyze_instruction`
(`src/compiler/55.borrow/borrow_check/mod.spl:158-198`) only records a "use"
fact (`nll.record_use`) inside the `Copy(dest, src)` and `Move(dest, src)`
arms. Every other `MirInstKind` variant — including `Call(dest, func, args)`
— falls through to the catch-all:

```
case _:
    pass_do_nothing
```

(`mod.spl:198`). A function call's arguments are carried directly as
operands on the `Call` instruction (`src/compiler/50.mir/mir_data.spl:447`,
`459`, `641`) — MIR lowering never emits a separate per-argument `Copy`/
`Move` instruction for a call argument. So when an already-moved `iso` local
is passed to a function, the checker never sees any instruction that reads
it, and reports no error.

## Repro (real source text through the real pipeline, not hand-built HIR/MIR)

```
fn main():
    val x: iso i64 = 5
    val y: iso i64 = x
    print x
```

`errors_for_source(...)` (the real `parse_full_frontend` -> `HirLowering` ->
`MirLowering` -> `check_mir_module` pipeline) returns **0 errors** for this
program. Verified failing test:
`test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl`, case "reports
a use-after-move error for a moved iso local used as a call argument
(`print x`)" — asserts `errors.len() > 0`, currently RED (left in the repo
asserting the correct behaviour per repo policy against weakening a failing
test).

## What DOES work (so this is localized, not a chain-wide break)

The exact same file's first three cases are GREEN and sabotage-checked
(swapping sources between cases correctly flips each to RED, confirming the
assertions are content-sensitive, not vacuous):

1. `val x: iso i64 = 5 / val y: iso i64 = x / val z: iso i64 = x` — the
   SECOND use is another let-binding place-read of the already-moved `x` →
   **caught**: `check_mir_module` returns a non-empty `[NLLError]`. (Per
   `mir_lowering_stmts.spl:768`, both the `y` and `z` bindings are place-reads
   of an iso-typed source, so both lower to `MirInstKind.Move`, not `Copy` —
   the second `Move`'s `record_move` on an already-moved place is what
   `analyze_instruction`'s `Move` arm, mod.spl:177-181, turns into the
   error, not a `Copy`-based use-record. Not independently traced at the
   instruction level beyond this — the checker-return-value is what was
   directly measured.)
2. Same shape without the third line (no reuse) → correctly **no error**.
3. Identical shape with plain `i64` (no `iso`) → correctly **no error**
   (proves the mechanism doesn't just error on everything).

This means:
- `parse_full_frontend` parses `iso T` (parser gap from
  `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`
  is closed — see "LANE ISO2" in
  `src/compiler/10.frontend/core/parser.spl:513-528`).
- HIR lowering preserves `HirTypeKind.Isolated` for a `val` local's declared
  type (`src/compiler/20.hir/hir_lowering/types.spl:513-521`).
- MIR lowering emits a real `MirInstKind.Move` at the variable-to-variable
  let-binding site (`src/compiler/50.mir/mir_lowering_stmts.spl:768-771`,
  `mir_hir_type_is_isolated` gate at line 48).
- `BorrowChecker.check_function` reports a real `NLLError` for that Move
  followed by a later place-read use.

The break is ONLY in `analyze_instruction`'s handling (or rather
non-handling) of `Call` operands — the move-emission side of the pipeline is
proven working end-to-end by cases 1-3 of the same spec file.

## Where

- `src/compiler/55.borrow/borrow_check/mod.spl:158-198` —
  `analyze_instruction` has no `Call`/`CallIndirect` arm; add one that calls
  `nll.record_use` for every local operand in `args`.
- `src/compiler/50.mir/mir_data.spl:447,459,641` — confirms `Call` carries
  args as bare operands, no per-arg Copy/Move to piggyback on.

## Suggested fix

Add a `Call(dest, _func, args)` (and `CallIndirect`) arm to
`analyze_instruction` that iterates `args`, and for each operand that is a
local place, calls `nll.record_use(point, Place.local(local.id))` — mirroring
the `Copy` arm's `record_use` call but without the `record_assign` (a call
argument doesn't reinitialize anything). Also worth auditing
`MirTerminator.Ret(_)` for the same gap — `iso_move_pipeline_spec.spl`'s own
comments flag it as dropping its operand too, though that is out of this
bug's directly-measured scope.

## Test

`test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl` — left in the
repo with 3/4 cases green and the `print x` case genuinely red, per repo
policy (never weaken a failing test to make it pass).
