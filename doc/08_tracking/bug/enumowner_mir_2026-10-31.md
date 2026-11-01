# enumowner: bare variant / enum-owner MIR failures in pinned stage2

**Status:** open (workaround applied); see 2026-11-01 re-check below

## Root bug
Stage3 MIR lowering (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, bare-variant
resolution ~L4255-4292 and owner check ~L4182) mis-resolves `match` subjects:
1. Bare `Ok`/`Err` arms over a method-call subject whose type is seen as non-enum are reported
   ambiguous (builtin Result wrapper not preferred before the multi-enum ambiguity check).
2. Bare `Tuple`/`Struct` payload arms over `Option<EnumPayload>`-unwrapped subjects are ambiguous
   with other enums declaring `Tuple`/`Struct`; subject type is reported as an unrelated symbol.
3. `un_op` bound from `HirExprKind.Unary(un_op, ..)` is inferred as `Visibility` (owner mismatch
   with `HirUnaryOp`).

## Workaround sites (tag `bug=enumowner-mir-20261031`)
- Result.Ok/Result.Err qualification: backend_helpers.spl (tail match), backend_api.spl (compile),
  async_ref.spl (two matches), file_fiber_tldr_bridge_v1.spl (two matches).
- EnumPayload / HirEnumPayload qualification: expression_core.spl, param_effects/context.spl,
  param_effects/infer.spl, param_effects/short_escape.spl, 35.semantics/resolve.spl,
  35.semantics/safety_checker_expr.spl.
- Typed local `un_op_t: HirUnaryOp`: 20.hir/hir_literal_constant_v1.spl.

Find all with: `git grep -n "bug=enumowner-mir-20261031"`.

## Removal condition
Remove once the root fix is in a stage2 used for bootstrapping.

## Status (2026-11-01 re-check)

Not reproducible outside the full stage3 closure. Seed-hosted in-process pure-Simple
HIR+MIR re-check (`test/01_unit/compiler/50.mir/enum_owner_unqualified_arms_spec.spl`):
bare `Ok`/`Err` over a method-call subject (with a competing `Ok`/`Err` enum), bare
`Tuple`/`Struct` arms over an unwrapped `EnumPayload?` (with a competing enum), and an
`un_op` payload binder next to `Visibility` all lower with no ambiguity/owner
diagnostic. Revert-ready: unknown — only after a full-closure stage3 build passes
without the qualifications (phase 3 owner).
