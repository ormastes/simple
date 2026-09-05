# `.?` on Option returns the payload object, not bool — both engines

**Date:** 2026-07-28
**Severity:** medium (silent wrong values through `-> bool` functions)
**Status:** open; workaround applied at one site

## Symptom

`opt.?` on an `Option<T>` evaluates to the **payload T** (truthy object) instead of a
boolean, on BOTH the tree-walk interpreter and the JIT (verified via
`test/01_unit/compiler/types/units_newunit_registry_spec.spl` failures: `expected
UnitEntry(...) to equal true`).

Consequence: a function declared `-> bool` that returns `opt.?` silently returns the
object; the declared return type is not enforced. Every `expect(x.?).to_equal(true)`
or `== true` comparison downstream fails (or worse, truthiness masks it in `if`).

## Repro

```simple
fn has(name: text) -> bool:
    val opt = lookup(name)   # Option<UnitEntry>
    opt.?                    # returns UnitEntry, not bool
```

`expect(reg.has("x")).to_equal(true)` → "expected UnitEntry(...) to equal true".
Condition contexts (`if opt.?:`) still behave as expected via truthiness, which is why
this survives most usage.

## Expected

Per language rules (`.?` is the predicate form, ".? over is_* predicates"), `.?` should
produce `bool` — or at minimum, returning it from a `-> bool` function should coerce or
be a type error.

## Workaround (applied)

`src/compiler/30.types/units/unit_registry.spl` `has()` rewritten to
`match ... case Some(_): true / case None: false`. Spec rewritten to assert via match
on concrete fields, never `expect(x.?).to_equal(true)`.

## Fix direction

Either lower `.?` to a real bool in both engines, or enforce declared `-> bool` return
coercion/diagnosis. Audit other `-> bool` functions returning `.?`:
`grep -rn "^\s*\w*\.\?\s*$" src/ --include=*.spl` (last-expression position).
Related family: JIT `Option<i64>=3 reads as None`, `Some(i64)` payload shift — Option
representation quirks cluster; this one is engine-agnostic.
