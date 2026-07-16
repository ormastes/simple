# BUG: native path — `fn(T) -> U` type annotations fatal with "unresolved type: fn"

**Status:** FIXED (2026-07-16, lane r_fn_type)

## Symptom

Any `fn(T, ...) -> U`-typed parameter or local (a lambda VALUE stored/passed
through an ordinary fn-typed slot, e.g. `f: fn(i64) -> i64` or
`callback: fn(UiEvent) -> text`) fataled native-build:

```
error: HIR lowering error in <module>: unresolved type: fn
```

Parity cases `local_lambda_value_llvm` and `enum_text_callback_llvm`
(`scripts/check/check-native-seed-parity.shs`) both hit this.

## Root cause

Two-layer bug, both in the frontend, upstream of HIR:

1. **Parser (`src/compiler/10.frontend/core/parser.spl`)**: both function-type
   syntaxes — `fn(T, ...) -> U` and the paren-arrow form `(T, ...) -> U` —
   parsed the parameter and return types only to immediately discard them,
   always returning the bare, argless `TYPE_FN` sentinel (`=11`). This is
   unlike `Dict<K,V>`, `Result<T,E>`, and tuple types, which each register
   their component type tags in a dedicated `TYPE_*_BASE + id` registry
   (`dict_type_register`, `result_type_register`, `tuple_type_register`) so
   the real generic args survive to the AST bridge.
2. **AST bridge (`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`,
   `convert_flat_type`)**: the bare `TYPE_FN` tag mapped to
   `Type(kind: TypeKind.Named("fn", []))` — a zero-arg named type, not
   `TypeKind.Function(params, ret)`.
3. HIR's `lower_type` (`src/compiler/20.hir/hir_lowering/types.spl`) special-
   cases `TypeKind.Named` *before* its normal discriminant dispatch (a
   stage4 irrefutable-match-arm workaround — see comment at `lower_type`
   line ~255) and routes straight to `lower_named_kind("fn", ...)`, which has
   no case for `"fn"` and falls into the unresolved-symbol branch ->
   `HirTypeKind.Error` -> fatal (all non-`recovered` HIR errors are fatal
   since 00b5f60ea93).

Note `HirTypeKind.Function(params, ret, effects)` already existed and
`lower_type`'s normal (non-`Named`) dispatch already had a correct `d_func`
branch producing it — the bug was purely that fn-type annotations never
reached that branch; they were funneled into `lower_named_kind` as a bare
`Named("fn", [])` with no signature.

## Fix

Mirrored the existing Dict/Result/Tuple registry pattern for function types:

- `src/compiler/10.frontend/core/types.spl`: added `TYPE_FN_BASE`/`TYPE_FN_LIMIT`
  (4000..5000, free space before `TYPE_TUPLE_LIMIT`=4000 and `TYPE_NAMED_BASE`=10000),
  `fn_type_register(param_tags, ret_tag)`, `fn_type_get_params`,
  `fn_type_get_ret`, `is_fn_type_tag`, `fn_type_tag_to_id`; wired into
  `reset_all_pools` and exports.
- `src/compiler/10.frontend/core/parser.spl`: both function-type parse
  branches (`fn(...)`  and paren-arrow `(...) -> U`) now collect the parsed
  param type tags and return type tag into `fn_type_register(...)` instead
  of discarding them.
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`: `convert_flat_type`
  now checks `is_fn_type_tag(...)` (placed before the generic
  `>= TYPE_UNION_BASE` catch-all, same as the dict/result/tuple checks) and
  rebuilds the real `TypeKind.Function(params, ret)`, which flows into
  HIR's existing, already-correct `d_func` dispatch.

No changes were needed in `hir_lowering/types.spl`, MIR, or codegen — once
the real `TypeKind.Function` reaches `lower_type`, the existing dispatch and
downstream MIR call-typing (`HirTypeKind.Function(_, ret, _)` pattern
matches in `switch_operators_calls.spl`, `expr_dispatch.spl`,
`method_calls_literals.spl`) already handle it correctly, since they only
needed the real return type (arity is derived from the call site, per the
pre-existing paren-arrow branch comment).

A bare/argless `fn(...)`-without-`->` annotation continues to fall through
as `HirTypeKind.Infer` (via `TYPE_VOID`=0's pre-existing `<= 0` -> `Infer`
short-circuit in `convert_flat_type`), unchanged from before — this fix only
restores param/return type propagation for the syntax paths that declare
them.

## Verification

- `scratchpad`-only manual builds: both `local_lambda_value` (expect `611`)
  and `enum_text_callback` (expect `run`) native-build (LLVM, strict
  `SIMPLE_NO_STUB_FALLBACK=1`) and match expected output exactly.
- `scripts/check/check-native-seed-parity.shs` filtered to
  `NATIVE_PARITY_CASES="local_lambda_value enum_text_callback"`:
  `local_lambda_value_llvm` PASS, `enum_text_callback_llvm` PASS (cranelift
  legs XFAIL — pre-existing, unrelated seed SFFI gap, see
  `cranelift_seed_missing_sffi_externs_2026-07-16.md`).
- `sh scripts/check/native-smoke-matrix.shs`: `total=15 pass=15 fail=0
  xfail=0 xpass=0 codegen_fallback_hits=0`.
- Full `check-native-seed-parity.shs` run unfiltered to confirm no
  regressions from the shared frontend/type-tag changes (see companion
  session notes; large matrix, all legs PASS/XFAIL as before plus the two
  newly-fixed cases).

## Related (found + fixed in the same session, separate root cause)

While reproducing this bug, ALL native-builds (even `fn main(): print("hi")`)
were failing with an unrelated, unconditional `error: semantic: type
mismatch: cannot convert dict to int`. Root cause:
`src/compiler/10.frontend/desugar/desugar_async.spl` (landed in
`c5603ae1de5`, "fix(bootstrap): restore pure runtime ABI and Dict dispatch")
called `rt_dict_keys(...)` directly on real `Dict` values in three spots —
exactly the documented seed-compat landmine ("no rt_dict_*/rt_tuple_* extern
calls on real values; use `.keys()`/`.values()`/`.contains_key()`"). Since
async desugaring runs on effectively every module, this broke every single
native-build unconditionally. Reverted those three call sites back to
`.keys()` method calls (see diff); confirmed this alone restores a clean
`hello world` native-build before layering the `fn`-type fix on top.
