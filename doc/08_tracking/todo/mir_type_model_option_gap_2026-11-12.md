# TODO: MIR type model has no `Option(T)` (type-model gap)

Source: post-merge Fable review of #8602, 2026-11-12.

`src/compiler/50.mir/mir_types.spl` (the `MirTypeKind` aggregates, about lines 190-196) has an exact logical
`Result(ok: MirType, err: MirType)` but no `Option(T)`. An `f64?` / `T?` value
is therefore typed by its runtime carrier: the enum-constructor retag in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (about line 6227) gives it
`Opaque("enum")`. The payload type `T` is erased from the MIR type.

Consequences seen so far:
- `test/01_unit/compiler/50.mir/enum_match_divergence_spec.spl` has to pin
  `Opaque("enum")` for `f64?` returns (#8602). It cannot check that the
  payload is `f64`.
- Any MIR consumer that needs the Option payload type has to recover it from
  HIR, as Result consumers no longer do.

Wanted: an exact `Option(inner: MirType)` kind, mirroring `Result`. Native
backends would lower it to the tagged runtime handle only through an explicit
ABI mapping, so the semantic type is never erased to `Opaque("enum")`.
Not started; no owner yet.
