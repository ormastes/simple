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

## Status (2026-11-02 full-closure-competitor re-check, lane sbr-1)

Still not reproducible from current source. New seed-hosted spec
`test/01_unit/compiler/50.mir/enum_owner_full_closure_shapes_spec.spl` (4/4 green)
re-lowers the ORIGINAL unqualified shapes with the competitors the stage4 closure
really contains: a second user `enum Result<T, E>`
(`src/compiler/30.types/const_key_validator.spl`), three enums declaring
`Tuple`/`Struct` (runtime_value_v1 / parser_types / treesitter_types shapes), the
original `case Some(pl): match pl:` binder (the earlier spec only covered `if val`),
and an imported `Visibility` that shares a variant name with `HirUnaryOp`. The
current `subject_owner_type` Optional-payload ownership and `enum_match_type_owner_key`
Result/Option handling in `switch_operators_calls.spl` resolve all of them. The
failure is attributed to the pinned (older) stage2 binary, not to current source.
Audit: all 25 tagged sites present; no untagged `case Some(x): match x: case Tuple/Struct`
or `Unary(un_op ..) ... match un_op:` sites remain in src/. Bare `Ok`/`Err` over typed
`Result` locals also exist untagged (e.g. file_fiber_tldr_bridge_v1.spl:110/170/304,
file_text_session.spl:191) and were lowered by the frozen stage2 that emitted the
1414 stage3 objects, so the shape alone is not the trigger; no sites were added.
Removal condition unchanged.
Real-module attempt: re-lowering the original `hir_literal_constant_v1.spl` (untyped
`match un_op:`) together with its real imports (span, visibility, parser_types[_expr],
hir_operators, hir_types, hir_definitions) under the Rust seed exceeded the 900 s
per-spec budget (child-timeout, <1 GB RSS) before any diagnostic. A seed-hosted
full-import repro is therefore infeasible; it needs a native stage3 lowering run.
