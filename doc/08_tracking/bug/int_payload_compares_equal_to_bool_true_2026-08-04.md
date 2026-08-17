# `1` compares equal to `true`, turning a real type error into a passing assertion

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
Retained because the *observation* that prompted it is real and still
unexplained; the *mechanism* asserted below is not.
**Found:** 2026-08-04, while measuring the `T?`-to-`bool` coercion fix.

## REFUTATION (read this first)

The central claim — that `expect(1).to_equal(true)` passes — is **false**.
Tested from a worktree at origin, spec placed inside the tree so discovery
works, with a deliberate failing control proving the file was not vacuous:

| expression | OLD binary | binary with the coercion fix | pure-Simple runner |
|---|---|---|---|
| `check(Some(1).?)` (the 632-file pattern) | passes | passes | passes |
| `expect(1).to_equal(true)` | **fails** | **fails** | **fails** |

Equality is strict in every engine reachable here, on both sides of the
coercion fix. So `1` does **not** compare equal to `true`, and the explanation
offered below for why the `deep`/`improved` families are green is wrong.

**What remains true and unexplained:** those ~632 files *are* green, and
sabotage proved they are not vacuous (`43 total, 42 passed, 1 failed`). Since
`check(Some(1).?)` passes even on the OLD binary — which lacks the argument
coercion — neither loose equality nor the coercion fix accounts for it. The
real mechanism is still unidentified; whoever picks this up should start by
instrumenting what value actually reaches `condition` in
`fn check(condition: bool)` on the OLD binary, rather than trusting either
story below.

Note also that per `reference_spec_dsl_is_rust_intrinsics`, the spec DSL
resolves to Rust intrinsics in `bdd.rs` and the `.spl` spec-library matchers
may be unreachable — so "the pure-Simple matcher is looser" is not a testable
hypothesis as stated.

## Original (refuted) symptom

An `i64` value compares equal to a `bool`:

```simple
expect(1).to_equal(true)      # claimed to pass — IT DOES NOT
expect(42).to_equal(true)     # fails: "expected 42 to equal true"
```

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
