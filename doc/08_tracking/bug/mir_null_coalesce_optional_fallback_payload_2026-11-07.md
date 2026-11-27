# MIR types `opt ?? other_opt` as the bare record, losing the optional merge

Status: fixed in MIR lowering; red/green under the seed-interpreted pure-Simple
lowering. Stage 2 native re-run pending the next bootstrap.

## Symptom (bootstrap run 15, Stage 2 row `compiler_cli_build`)

11x `enum construction 'compiler.hir.hir_types.HirTypeKind.Optional': payload
type mismatch at 0; function=lower_enum_construct_named
module=compiler.mir._MirLoweringExpr.switch_operators_calls`. Every module in
the shard was then sealed failed.

Source shape (`switch_operators_calls.spl`, `lower_enum_construct_named`):

```
val witness_type = option_payload_type ?? self.some_witness_inner_hir_type(args[0].value)
if val inner_type = witness_type:
    ... HirType(kind: HirTypeKind.Optional(inner_type), ...)
```

Both operands are `HirType?`, so the merge is `HirType?` and the `if val`
binder is `HirType`. This is valid Simple (chained `??` is documented in
`syntax_quick_reference.md`).

## Root cause

`NullCoalesce` lowering (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`)
assumed the default operand is always the left Option's inner `T`: it typed the
merged temp as the record `T`, gave it the record layout name, and checked the
default against the record owner (`null coalesce fallback does not match
declared record owner`). With a `T?` default the check failed (or, on the flat
path, the merge was typed bare `T`), the merged local never carried `T?`, and
the `if val` binder had no type evidence, so the enum payload slot rejected it.

## Fix

`null_coalesce_optional_fallback_type` recognises a default whose static type
(`enum_match_expr_type`) is `Optional(X)` with `X` alias-compatible with the
left's nominal payload owner. Unless the `??` expression carries a non-optional annotation, the merge then keeps the erased word type, gets
no record layout name, skips the record-owner check, and is remembered as `T?`.
The runtime merge is unchanged: the present edge stores `rt_unwrap_or_self`'s
payload and the default edge stores the default's word; `if val` unwraps both
forms with `rt_unwrap_or_self`.

Not widened: a `U?` default for a `T?` left still fails the owner check, and the
`T?` merge is still rejected by a mandatory `T` payload slot.

## Evidence

`test/01_unit/compiler/50.mir/enum_payload_inferred_carrier_spec.spl` (seed
`/home/yoon/dev/seed-try-target/release/simple test`):

- origin/release/1.0.0 `fe52a1431e6` without the fix: 8 examples, 5 failures
  (the record, enum and annotated optional merges, plus the mandatory-slot
  negative, which used to fail on the owner check instead).
- with the fix: 8 examples, 0 failures.
- Negatives that pass both before and after: a `U?` default for a `T?` left
  is still rejected, and so is `val w: T = a ?? b` with `b: T?`.
- Neighbouring specs (optional_record_coalesce_owner, coalesced_receiver_identity,
  optional_scalar_static_some, optional_enum_payload_owner,
  stage2_receiver_type_transport): the same pre-existing failures with and
  without the fix; enum_subject_owner_recovery, enum_payload_value_shapes and
  nested_optional_text_nil_pattern pass with the fix.

Native reproducer on the frozen run-15 Stage 2 binary (built from
`dba24b97b4d`, so it cannot show the fix): the same `p ?? self.wit(t)` /
`if val` shape fails with the identical `payload type mismatch at 0` message.
