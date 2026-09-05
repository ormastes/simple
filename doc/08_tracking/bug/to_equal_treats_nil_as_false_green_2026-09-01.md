# `expect(nil).to_equal(false)` passes — `to_equal` disagrees with `==` (2026-09-01)

**Status:** OPEN. Found while re-baselining `test/03_system/**` genuine failures.

## Symptom

The `to_equal` matcher reports equality for operand pairs that `==` reports as
**not** equal. That is a false-green: an assertion that should fail passes
silently.

Reproduce (fresh Rust seed built from `origin/main` @ `c6ce53c444d`):

```simple
use std.spec.*

describe "nil vs false":
    it "operator ==":
        val d = {"a": 1}
        print "m == false  -> {d.get("b").? == false}"   # false
        print "hit == true -> {d.get("a").? == true}"    # false
    it "matcher":
        val d = {"a": 1}
        expect(d.get("b").?).to_equal(false)             # PASSES
```

Measured: `Results: 2 total, 2 passed, 0 failed`.

`d.get("b").?` evaluates to `nil` (correct — `.?` returns `T?`, see
`doc/07_guide/quick_reference/syntax_quick_reference.md:516-537`). The `==`
operator correctly says `nil == false` is `false`. `to_equal(false)` on the
same `nil` says they are equal.

**CORRECTION (2026-09-01, measured):** the mirror case does NOT reproduce.
`expect(1).to_equal(true)` correctly FAILS. Measured on a seed built from
origin/main, both cases in one spec file:

```
  OK  nil vs false      <- expect(d.get("b").?).to_equal(false)  PASSES (the real defect)
  X   int vs true       <- expect(1).to_equal(true)              FAILS (correct)
  2 examples, 1 failure
```

So the defect is specific to a `nil`/absent-optional left-hand side being
treated as equal to `false`, NOT a general "any value equals any bool"
looseness. Scoping this correctly matters for the fix: a sweep written for the
broader claim would change behaviour that is already right. The original
sentence follows, retained so the overstatement stays visible:

> The mirror case is the same defect: `expect(1).to_equal(true)` also passes,
while `1 == true` is `false`.

## Why this matters

This is the "loud failure becomes a silent wrong answer" class. Any spec whose
oracle compares a possibly-nil value against `false` — or a possibly-int value
against `true` — is not asserting what it appears to assert, and will stay
green through a real regression. The population is not yet measured; it should
be, because `to_equal` is the most-used matcher in the tree.

## What is NOT the bug

`.?` returning `nil`/`1` rather than `false`/`true` is correct and documented.
Specs comparing `.? == false` were wrong oracles and were corrected separately
(commit `8bc29a794e0`). This record is only about the matcher/operator
disagreement.

## Fix direction (not yet implemented)

`to_equal` should use the same equality relation as `==`, so that nil is equal
only to nil and a bool is equal only to a bool. Landing this will flip
currently-green specs to red — as with the #212 matcher-chain fix, a newly-red
spec is the fix working, and the underlying oracle should be corrected rather
than the assertion reverted. Expect the change to need a sweep of the affected
oracles in the same or an immediately following change.
