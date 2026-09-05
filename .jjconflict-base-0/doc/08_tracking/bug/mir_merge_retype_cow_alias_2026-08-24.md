# MIR merge retype retains earlier COW aliases

## Status

Open. Source-level evidence only; runtime measurement is intentionally omitted
under the user's no-verification instruction.

## Defect

Five MIR merge-result retype sites now mutate `self.builder` directly, but an
earlier branch-local `MirBuilder` value remains live after being assigned back
to `self.builder`. Because `MirBuilder.locals` has value/COW semantics, indexed
`set_local_type` can still privatize and copy all L locals.

Affected families:

- `mir_lowering_stmts.spl`: if and conditional-chain merge lowering;
- `_MirLoweringExpr/switch_operators_calls.spl`: switch, match, and result-match
  merge lowering.

The name/type setters no longer force array reconstruction themselves. Parameter
naming can amortize an initial privatization across later parameters, and the
Vulkan constant retype path has no builder alias. The merge paths remain O(L)
time and transient storage when their earlier builder aliases survive.

## Required closure

Refactor branch lowering so the authoritative builder is mutated directly for
the complete control-flow segment, or introduce a language-supported consuming
ownership transfer that demonstrably releases the temporary before retyping.
Preserve instruction/terminator order, merge placeholder behavior, inferred
type selection, spans, and result-match semantic markers. Add allocation/COW
evidence before closing this bug.
