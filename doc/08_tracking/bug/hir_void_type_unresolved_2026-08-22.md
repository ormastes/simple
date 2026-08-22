# HIR: `void` type annotation unresolved on the native path (2026-08-22)

**Status: RESOLVED** (same day).

## Symptom
Stage1 closure probe (no `SIMPLE_BOOTSTRAP`):
`[hir-fatal] src/compiler/semantics/enum_contract/__init__.spl: unresolved type: void`.
The fatal is blamed on the package `__init__` because it lowers the signatures
of its imported siblings; the actual source is
`src/compiler/35.semantics/enum_contract/hir_match_coverage.spl:44`
(`fn enum_contract_walk_unhandled(...) -> void:`).

## Root cause
`src/compiler/20.hir/hir_lowering/types.spl` `lower_named_kind` accepted only
`unit` for the unit type. The flat AST bridge
(`10.frontend/_FlatAstBridge/convert_nodes.spl:312`) maps tag `TYPE_VOID` to
`Named("void")`, the seed treats `void` as an accepted spelling, and ~30 owned
`.spl` files write `-> void`, so `void` reached the strict name gate and hit
`unresolved type: {name}`.

## Fix
`case "unit" | "void": HirTypeKind.Unit`.

## Regression spec
`test/01_unit/compiler/hir/void_return_type_spec.spl` (mirrored): 3 of 4 examples
fail pre-fix with the exact text (`-> void` local, imported-sibling signature,
generic arg `Result<void, text>`); 4/4 post-fix.
