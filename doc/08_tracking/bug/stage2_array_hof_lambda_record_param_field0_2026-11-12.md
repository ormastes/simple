# Stage 2 native: array-HOF lambda parameter reads record field 0 (2026-11-12)

**Status:** fixed in source (MIR lowering); native confirmation is the next
Stage 2 rebuild (bootstrap run 14).
**Class:** silent wrong value. Catalogue row 14 of
`doc/07_guide/compiler/robustness/stage2_native_miscompile_classes.md`.

## Symptom

With the admitted Stage 2 compiler (`bootstrap-fable-13`, aarch64, cranelift),
`xs.map(\f: f.c)` over `[S(a: 1, b: 2, c: 3), S(a: 4, b: 5, c: 6)]` returned
`[1, 4]` (field `a`), and `xs.filter(\f: f.b != 0)` tested `f.a`. A `for` loop
over the same array, and the same lambda called directly, read the right field.
Consequence: `FeatureDatabase.incomplete_features()` and every `map`/`filter`/
`any`/`all`/`fold` over a record array in the natively built CLI returns wrong
values.

## Fixture matrix (Stage 2 native, before the fix)

| fixture | shape | output | verdict |
|---|---|---|---|
| m01 | `[S].map(\f: f.b)` | `0 0` (want `0 1`) | wrong |
| m02 | `[S].filter(\f: f.b != 0).len()` | `0` (want `1`) | wrong |
| m03 | `[i64].map(\x: x * 2)` | `2 4` | ok |
| m05 | user HOF `apply(xs, \f: f.b)`, slot `fn(S) -> i64` | `0 0` | wrong |
| m06 | user HOF with a named `fn getb(f: S)` | `0 1` | ok |
| m07/m19 | `val g = \f: f.c; g(s)` (direct call) | `3` | ok |
| m09 | `[S].map(\f: f.b + k)` (capture) | `10 10` (want `10 11`) | wrong |
| m11 | `[S].map(\f: f.a)` (field 0) | `5 6` | ok (coincides) |
| m16 | `for f in xs: out.push(f.b)` | `0 1` | ok |
| m18 | `[S].map(\f: f.c)`, three fields | `1 4` (want `3 6`) | wrong |

Element type must be a record, the field must not be field 0, and the lambda
must be untyped; captures do not matter; a named callback is unaffected.

## Root cause

`resolve_field_index` (`src/compiler/50.mir/_MirLowering/function_lowering.spl`)
finds a field's index from the base local's `struct_value_syms` row or from the
base expression's HIR `Named` type, and otherwise returns 0. An untyped lambda
parameter has neither:

- `lower_array_map` (`_MirLoweringExpr/method_calls_literals.spl`) inlines the
  lambda and binds its parameter to the decoded element with no record row.
  The `for` loop path (`mir_lowering_stmts.spl`, `array_element_struct_syms`
  -> `struct_value_syms[loop_var]`) publishes it; `map` did not.
- `filter`/`any`/`all`/`fold` lift the lambda through
  `lower_lambda_value_for_type` (`_MirLoweringExpr/switch_operators_calls.spl`)
  with no declared signature, so the lifted parameter got no record row either.
  With a declared `fn(S) -> i64` slot only a `TypeParam` parameter got one; a
  `Named` record parameter did not (m05).

The direct call is correct because `try_inline_lambda_call` binds the argument
local, which already carries its record.

## Fix

- `array_hof_element_record_owner(arr)`: the element record of a HOF receiver,
  from the same two tiers as the for-loop binding (published
  `array_element_struct_syms` row, else declared `[Record]` HIR element);
  `""` for plain-value arrays.
- `lower_array_map` records that owner on the element local bound to the
  lambda parameter.
- `lower_lambda_value[_for_type]` take `param_records: [text] = []`; the
  `filter`/`any`/`all` (param 0) and `fold` (param 1) dispatch passes the owner.
  A declared `Named` record slot records its own layout via
  `optional_payload_struct_name`.

No field access guesses: a parameter with no proven record still falls through
to the existing fallback, and no ABI or signature changes (the lifted
parameter stays the i64 handle, which `rt_value_as_int_wide` passes through).

## Evidence

- Seed in-process MIR spec
  `test/01_unit/compiler/50.mir/array_hof_lambda_record_param_field_spec.spl`:
  before 2/11 (only the two negative cases), after 11/11. Covers map (param,
  literal, capture, nested `w.inner.c`), filter, any, all, fold, a user HOF
  with a declared slot, a direct call, and an int-array map.
- Native fixture `test/fixtures/compiler/array_hof_lambda_record_field_native.spl`
  with Stage 2 `bootstrap-fable-13`: `map=1,4 filter=2 any=0 all=0`, exit 1
  (expected `map=3,6 filter=1 any=1 all=1`, exit 0). The after run needs a
  Stage 2 rebuilt from this source (run 14).
- Pre-existing, unchanged by this fix: `for_in_runtime_tuple_decode_spec`
  fails 3/15 with or without it.

## Not fixed here

The lifted copy of `val g = \t: t.c` (used only when `g` escapes as a value)
still has no record for `t`; nothing at that site proves one.
