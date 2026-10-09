# E-MONO-032 x115 / E-MONO-033 in phase 3: fn-typed parameters lowered to `Any`

Status: FIXED (source), native re-validation pending.
Date: 2026-10-09

## Symptom

The phase-3 build (frozen stage2 compiling `src/app/cli/bootstrap_main.spl`,
1160 modules, 0 HIR failures) stopped in monomorphization:

```
[mono] generic_fns=66 call_sites=124 specializations=3 unresolved=115
error[E-MONO-033]: monomorphization left 115 generic call site(s) unspecialized
```

115 x `E-MONO-032: call to generic X has no explicit type arguments and they
could not be inferred from its argument types`: `walk_hir_expr` 41,
`walk_hir_block` 14, `walk_hir_type` 12, `walk_hir_call_arg` 3, eight other
`walk_hir_*` x1 (all `src/compiler/20.hir/generated/hir_visitor.spl`), and
`cas_batch_error_v1` 34.

## Root cause (walk_hir_* family, 81 of 115)

The counts are exactly the generic calls inside the `walk_hir_expr` template
body (41/14/12/3/1x8). The one concrete caller
(`enum_contract/hir_match_coverage.spl:236`, explicit `<MatchSiteScan>`)
produced the specialization `walk_hir_expr$MatchSiteScan`; walking ITS body
failed at every nested call. Reduced spec with `SIMPLE_MONO_DIAG=1`:

```
[mono-diag] infer `walk` arg 1: no local type for NamedVar(acc)
[mono-diag] infer `walk` arg 2: no local type for NamedVar(f)
```

`f: fn(Node, C) -> C` reached HIR as `HirTypeKind::Any`:

- `src/compiler/10.frontend/core/parser.spl` (`parser_parse_type_impl`, the
  `kind == 20` branch) consumed the `fn(T, ...) -> R` shape and answered the
  bare `TYPE_FN` tag ("the bootstrap tag registry has no first-class fn-type");
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` turned `TYPE_FN`
  into `Named("fn", [])`;
- `src/compiler/20.hir/hir_lowering/types.spl` `lower_named_kind` maps
  `"fn"` to `Any`.

So in the specialized body `f` is not concrete (cannot bind `C`) and
`var acc = f(node, ctx)` has no local type (the callee is Any-typed), which
leaves `C` unbound for every `walk_*(child, acc, f)`.

## Fix

1. `types.spl`: a `TYPE_FUNCTION_BASE..TYPE_FUNCTION_LIMIT` (9750..10000,
   carved from the weak-reference block) registry interning
   `fn(params...) -> ret` shapes (`function_type_register`,
   `is_function_tag`, `function_type_get_params`, `function_type_get_ret`),
   reset with the other registries; `type_tag_name` answers `"fn"` for it and
   the two legacy `TYPE_FN` name/C-type sites accept it.
2. `parser.spl`: the `fn(...) -> R` annotation branch interns the shape and
   returns the registry tag (bare `TYPE_FN` only when the block is full).
3. `convert_nodes.spl`: a function tag is rebuilt as
   `TypeKind.Function(params, ret)`, which HIR already lowers to
   `HirTypeKind.Function`.
4. `type_checker.spl`: the `TYPE_FN` equality accepts a function tag on
   either side.
5. `monomorphize_integration.spl`: `callee_return_type` answers the declared
   return type of a local/parameter bound to a concrete `fn(..) -> R`, so
   `var acc = f(node, ctx)` is typed by `f`'s signature.

Fail-closed behaviour is unchanged: a genuinely uninferable call
(`only_ret<T>() -> T` with no context) still raises E-MONO-032.

## Spec

`test/01_unit/compiler/mono/visitor_fn_param_ctx_inference_spec.spl`
(fails before: `f` is Any, 2 unresolved; passes after: 3 call sites, 1
specialization, 0 unresolved, template pruned, verifier clean).

## cas_batch_error_v1 (34 of 115) -- NOT reproduced on release/1.0 source

All 34 call sites spell `cas_batch_error_v1<CasBatchTransactionV1>(...)`.
The pure-Simple parser DISCARDS explicit call type arguments
(`parser_expr.spl` `try_skip_ident_generic_args`; `EXPR_CALL` carries none,
HIR `Call` is built with `[]` type args), so the explicit spelling is a no-op
and the pass relies on result-context inference (`expected_result` from the
enclosing `return` / declared result). With the release/1.0 monomorphizer
that context resolves these sites (probe: `fn boxed[T](e) -> Result[T, i64]`
+ `return boxed<text>(1)` -> `boxed$str`, also in a 300-declaration file),
and a call with NO context (`val r = boxed2<text>(2)`) is refused -- which is
the remaining defect: explicit type arguments are silently dropped by the
parser. The frozen stage2 used by the phase-3 build therefore either predates
the result-context inference in `rewrite_call` or carries a native
miscompile of it; it must be rebuilt from current source before the 34 can
be re-attributed. Making explicit call type arguments survive parser -> flat
AST -> HIR needs an AST slot for them (`ExprKind.Call` has none) and is filed
here as the follow-up.
