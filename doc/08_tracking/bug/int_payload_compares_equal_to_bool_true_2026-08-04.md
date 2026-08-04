# `1` compares equal to `true`, turning a real type error into a passing assertion

**Status:** OPEN (equality / matcher coercion).
**Found:** 2026-08-04, while measuring the `T?`-to-`bool` coercion fix.
**Impact:** silent. Makes assertions pass that should fail, and makes any
grep-based estimate of the `T?`-to-`bool` defect's reach wrong.

## Symptom

An `i64` value compares equal to a `bool`:

```simple
expect(1).to_equal(true)      # passes
expect(42).to_equal(true)     # fails: "expected 42 to equal true"
```

So the assertion succeeds for exactly one integer value and fails for all
others. Nothing warns that the two sides have different types.

## How it was found

While measuring which specs the `T?`-to-`bool` coercion fix repairs
(`optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`),
the idiom `check(<expr>.?)` against a `bool`-declared parameter was found in
**660** files under `test/01_unit/std` — but only 28 of them were red. The
`deep/` (200 files) and `improved/` (432 files) families were green.

They are not vacuous. Sabotaging one `check(true)` to `check(false)` in
`test/01_unit/std/deep/array_deep_10_spec.spl` turned it red (`43 total, 42
passed, 1 failed`), so those specs do assert.

They are green because they happen to write `check(Some(1).?)`. Per the `.?`
semantics (`doc/07_guide/quick_reference/syntax_quick_reference.md`), that
yields the bare payload `1`, which is then compared against `true` — and the
comparison succeeds. The red specs are the ones whose payload is anything else:
`Some(42)`, `Some(Some(10))`, `d.get("key")`.

## Why this matters beyond the one defect

1. **It masks a real type error.** The whole point of the sibling report is that
   passing a `T?` where a `bool` is declared should be coerced or rejected. Where
   the payload is `1`, this coercion bug is *invisible* — the test passes for the
   wrong reason.
2. **It invalidates site-count extrapolation.** Any estimate of a bool-coercion
   defect's blast radius derived from grepping `.?` sites is wrong by the
   fraction of sites whose payload is `1`. Here that fraction was ~95%
   (632 of 660). An earlier corpus-wide figure of ~1,200 failures was exactly
   such an extrapolation and had to be withdrawn.

## Repro

```simple
use std.spec

describe "int/bool equality":
    it "should not equate 1 with true":
        expect(1).to_equal(true)       # currently PASSES; should fail
    it "already fails for other ints":
        expect(42).to_equal(true)      # fails as expected
```

`use std.spec` is required — without it `expect` never asserts and the file
reports green regardless.

## Fix direction

Make equality type-aware at the matcher boundary: comparing an integer against a
bool should be a **failure with a type-mismatch message**, not a truthiness
coercion. Prefer failing loudly over silently coercing — a spec that asserts
`to_equal(true)` against a non-bool is a defect in the spec, and it should say
so.

Check whether the same coercion exists in the interpreter's general `==` before
changing only the matcher; if it does, the matcher fix alone would leave `1 ==
true` true in ordinary code.

Related: `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`.
