# Bare variant inside `Some(..)` / `Ok(..)` / `Err(..)` binds on stage2, silently

- **Status:** FIX IN REVIEW (branch `work/rel-bare-variant-generic-slot-20261010`)
- **Date:** 2026-10-10
- **Severity:** HIGH (silent wrong-code in the pure-Simple compiler; seed is correct)
- **Component:** `src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl`
  (`lower_match_pattern`, `lower_payload_slot_pattern`)
- **Found by:** review of `96d47457568`

## Summary

A bare unit-variant name wrapped in a generic constructor pattern --
`case Some(X):`, `case Ok(X):`, `case Err(X):` -- is a **variant test** on the
Rust seed (`interpreter_patterns.rs`: an identifier that names a variant of the
matched value's enum is a unit-variant pattern). The pure-Simple HIR lowering
lowered `X` as a **binding**, because payload sub-patterns were lowered without
the wrapped slot's type. A binding always matches, so the arm matches every
`Some` / `Err` value and every later arm over the same wrapper is dead. No
diagnostic is produced.

## Live sites in the compiler closure

| Site | Shape | Effect on a stage2-built compiler |
|------|-------|-----------------------------------|
| `src/compiler/10.frontend/cache_artifact/three_payload_semantic_closure.spl:581,588` | `match binding.embedded_role: case Some(PriorModuleTld): .. case Some(PackageInitTld): ..` | the first arm takes every `Some`; the `PackageInitTld` arm is dead |
| `src/compiler/80.driver/cache/reference/reverse_reference_coordinator_v1.spl:809` | `case Err(ScopeGenerationMismatch):` | swallows every `Err` |

## Fix

The wrapped slot's type is taken from the generic instantiation:

- top-level arm: the subject's `T?` / `Option<T>` / `Result<T, E>`; the inner
  pattern is then lowered against `T` / `E` exactly like a top-level bare arm.
  A subject with no static HIR type uses the existing untyped-subject rule;
- payload slot: the declared slot type (`o: Op?`, `o: Option<Op>`,
  `r: Result<i64, Op>`) is recorded per enum, variant, slot and wrapper path.

## Not covered

- `[Op]` (array) slots and array patterns: a bare name inside an array
  pattern still binds.
- Struct-pattern payloads (`case V(field: X)`).
- A wrapper over a subject whose static type is known and is neither an
  Option nor a Result keeps the previous lowering.

## Evidence

`test/01_unit/compiler/50.mir/bare_variant_generic_slot_spec.spl` -- includes a
seed-executed oracle example (`Some(PriorTld)` / `Some(InitTld)` return 1 / 2).
