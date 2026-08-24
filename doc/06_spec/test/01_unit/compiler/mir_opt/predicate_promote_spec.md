# Predicate Promote Quarantine Specification

## Status

`predicate_promote` is disabled and every public adapter is a compatibility
identity. The former adjacency matcher removed `MaskFromCmp` without proving
that its destination had exactly one function-wide use.

## Executable evidence

The paired executable specifications are:

- `test/01_unit/compiler/mir_opt/predicate_promote_spec.spl`
- `test/unit/compiler/mir_opt/predicate_promote_spec.spl`

They require adjacent Add, Mul, and Fma candidates to remain unchanged, pin
multiple candidate pairs, and include the original unsound witness: an
adjacent candidate followed by another use of the same mask. Existing mismatch,
non-adjacent, standalone, empty-module, and trailing-definition cases remain.
The direct function adapter and typed `PassKind.PredicatePromote` function route
are also exercised with non-empty MIR.
The previously exported operand matcher remains compatible, while both exported
`try_fuse_*` constructors are pinned to return `nil` unconditionally.

The pass descriptor specifications additionally require the pass to report a
disabled/rejected status before backend or cost selection.

## Reactivation contract

Reactivation requires one shared linear-time function def-use result, including
terminators and successor blocks. Fusion is legal only when the mask definition
dominates the adjacent consumer and that consumer is its sole use; types, lanes,
comparison kind, `Move` semantics, and source-span preservation must also be
proved. Per-candidate whole-function rescans are forbidden.

## Verification status

These scenarios were updated as source-level evidence only. No test, build,
benchmark, SPipe, or optimizer command was run for this quarantine tranche.
