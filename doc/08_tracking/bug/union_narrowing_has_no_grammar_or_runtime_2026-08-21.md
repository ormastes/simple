# Union narrowing has no grammar and no runtime lowering (lane S4 follow-up)

- **Date:** 2026-08-21
- **Lane:** Wave 2D / Phase 4, S4 (union normalization)
- **Status:** OPEN — blocks the runtime half of S4

## What works after S4

`i64 | f64 | bool | text` now survives the flat-AST bridge as a real
`TypeKind.Union` -> `HirTypeKind.Union` -> `MirTypeKind.Union` (tagged), and
`compiler.semantics.union_normalize` synthesizes the canonical `@closed` enum
`__Union_bool_f64_i64_text` for it, which reaches the enum-contract table as
`contract=closed`. Gated by `scripts/check/check-closed-match-coverage.shs`
(fixture `test/fixtures/enum_contract/union_closed.spl`).

## What does not

There is no surface syntax for narrowing a union value, and no lowering behind
either candidate spelling. Measured on the seed at `bin/simple`:

1. `match x:` / `case i64 v:` — **parse error**:
   `Unexpected token: expected -> or => or :, found Identifier { name: "v" }`.
   A type-plus-binding arm is not in the grammar.
2. `if x is i64:` — **parses, then miscompiles**: the type name is lowered as a
   VALUE, giving
   `GlobalLoad: unresolved identifier 'i64' (not a global, function,
   const-data name, or import)` and a codegen stub fallback. `is` against a
   type is not wired for unions. `35.semantics/narrowing.spl:416` still carries
   the stale comment "Full union narrowing requires HirTypeKind.Union variant
   (not yet in HIR)" — the variant HAS existed; the narrowing was never built.

So a union-typed value can be declared and carried, but not discriminated, and
an exhaustiveness miss over a union cannot yet be reported as E-CLOSED-001 at a
real match site (the synthesized enum is contracted, but no source match names
its variants).

## Required to close

- Grammar for a narrowing arm (`case i64 v:` or equivalent) in the parser's
  match-arm rule.
- Lowering of that arm to `HirPatternKind.Enum(__Union_..., <VariantName>,
  payload)` against the synthesized enum, so the EXISTING closed-enum coverage
  check reports the miss with no new rule.
- `x is T` on a union lowering to a discriminant test rather than a global load.

Until then, do not claim S4 runtime narrowing; the normalization half is done
and gated, the narrowing half is not.
