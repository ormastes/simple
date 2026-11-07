# Native trait conversion loses bound sources with unknown metadata

Status: source fix and regression specifications authored; runtime verification pending.
Date: 2026-11-07

## Failure boundaries

1. `native_trait_declared_source_type` skips a supplied MIR local's top-level
   `Error` or `Infer` HIR type, then delegates to `receiver_declared_type`.
   For a bound `Var` or `NamedVar`, that helper reads the same unknown local
   again and returns before reaching the exact symbol's valid declaration.
   The earlier regression fixture used an unbound local and missed this path.
2. `coerce_native_trait_object` uses the recovered source only to recognize
   an existing trait object, then selects a concrete implementation from the
   raw local type again. An unknown local with a valid concrete expression or
   declaration therefore fails implementation selection when construction
   provenance is absent.

## Source repair

`src/compiler/50.mir/_MirLowering/native_trait_conversion.spl` now recovers
`Var` and `NamedVar` binding types through a conversion-specific helper. It
skips only top-level `Error`/`Infer` on the bound local before consulting the
exact symbol declaration. Other callers of `receiver_declared_type` retain
their existing behavior. Concrete supplied or bound local metadata, including
`Unit`, `Any`, and nested unknown payloads, retains its precedence.

Concrete implementation selection now consumes the same recovered source
type used for trait-object detection.

## Authored regression inventory

`test/01_unit/compiler/50.mir/native_trait_assignment_source_type_spec.spl`
adds coverage for:

- Bound `Var` and `NamedVar` with each `Error`/`Infer` local and each
  missing/`Error`/`Infer` expression metadata combination.
- Concrete metadata on a distinct bound local and authoritative supplied
  local metadata before a contradictory declaration or expression.
- Actual `coerce_native_trait_object` calls with no construction provenance,
  recovering a concrete declaration or expression, checking no diagnostics,
  both emitted thunks, a new object local, and its remembered target type.
- Concrete local precedence over contradictory target-trait expression metadata.

The conversion fixture uses an object-safe zero-method trait and a concrete
class implementation with reference semantics to isolate source recovery from
method dispatch and recursive field-copy behavior.

## Evidence and qualification limit

- Scoped `git diff --check`: passed.
- Astra final source review: approved the implementation and authored fixtures.
- No admitted self-hosted runtime was available to this repair lane. No Simple
  test, interpreter run, native compilation, or native execution was performed;
  no Rust seed fallback was used. Runtime correctness remains unverified.

Resume with the focused spec through an admitted self-hosted runtime, then the
required compiler/core and MCP/LSP smoke checks for this compiler change.
Source review and authored assertions do not constitute an executed test PASS.
