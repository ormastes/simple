# Bug: `expect(a == b).to_equal(false)` mis-evaluates the inline `==` argument

**Status:** RESOLVED (2026-09-12, re-verified: repro now passes)

**Date:** 2026-07-07
**Status:** CLOSED (2026-09-12) — not reproducible; see "Re-check 2026-09-12" at the end.
**Severity:** Medium — false-RED on specs that assert inequality of two
distinct values via `expect(<comparison>).to_equal(<bool>)` (the values under
test are correct; only the harness idiom mis-fires).
**Component:** self-hosted interpreter — `expect(...)` chained-method
argument evaluation (see also `.claude/rules/language.md` "Chained methods
broken — use intermediate `var`").

## Symptom

Review of the WM motion-background provider work surfaced this on distinct
`u32` values:

```simple
val a: u32 = 4294901760   # 0xFFFF0000
val b: u32 = 4278190335   # 0xFF0000FF
expect(a == b).to_equal(false)
```

fails with:

```
expected 4294901760 to equal 4278190335
```

i.e. the matcher receives the *raw operands* `a` and `b`, not the boolean
result of `a == b`, even though `a != b` and the expression should evaluate
to `false` before ever reaching `.to_equal(false)`.

## Root cause (as observed)

The inline `a == b` argument to `expect(...)` collapses into the surrounding
`expect(...).to_equal(...)` chain instead of being evaluated to a standalone
`bool` first. This is the same family as the general "chained methods
broken" landmine already tracked in `.claude/rules/language.md` and in
`interp_chained_replace_2026-07-05.md` / `interpreter_chained_map_named_fn_arg_2026-05-29.md`:
an expression nested inside a chained call is not fully reduced before the
outer chain consumes it, so the failure message reports the pre-comparison
operands rather than the comparison's boolean result.

## Workaround

Bind the comparison to an intermediate `val` before asserting, matching the
project-wide chained-method workaround:

```simple
val eq = a == b
expect(eq).to_equal(false)
```

## Testing-rule impact

Matchers must not receive inline binary expressions as arguments —
`expect(<a> <op> <b>)` should be treated as a landmine the same way chained
method calls are. Specs should bind the comparison to a `val` first. Related:
`bdd_expect_compare_to_equal_bool_eager_fail_2026-06-30.md` covers a
different (Rust-seed BDD runner, eager-flag) root cause for a similar
surface symptom (`expect(a == b).to_equal(false)` false-failing) — that one
is specific to the seed's per-example `BDD_EXPECT_FAILED` flag; this one is
the self-hosted interpreter's chained-argument evaluation order. Do not
conflate the two fixes.

## Triage 2026-09-12
Re-verified 2026-09-12: ran the record's own `expect(a == b).to_equal(false)` repro on distinct u32 values; it printed `PASS` with no false-RED, unlike the originally-reported "expected X to equal Y" failure. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).

The record's own operands, inline, unbound:

```simple
val a: u32 = 4294901760
val b: u32 = 4278190335
expect(a == b).to_equal(false)
```

passes. Sabotaging it to `.to_equal(true)` fails with a **bool** comparison,
not with `expected 4294901760 to equal 4278190335` — so the inline `==` is
being reduced to a bool before the matcher consumes it. **Not reproducible** —
status CLOSED. The "matchers must not receive inline binary expressions"
testing rule recorded above is no longer load-bearing for this defect.

Regression guard: `test/01_unit/bugs/spec_expect_inline_comparison_argument_spec.spl`
(8 examples). The guard deliberately uses the **inline** shape, not the
`val`-bound workaround: the workaround form was never broken, so a guard
written that way would be vacuous for this defect. One control example in the
workaround shape is kept so a future failure can be attributed to the inline
path rather than to comparison itself. Coverage: the record's u32 operands
(`==`, `!=`, and an equal-operand control), `<` and `>=` ordering, a text
comparison, and a comparison over two call results.

```
SPEC FILE VERDICT: test/01_unit/bugs/spec_expect_inline_comparison_argument_spec.spl outcome=OK declared>=8 executed=8 passed=8 failed=0 skipped=0 dropped=0
```

Non-vacuity proof: flipping the expected bool on the inline `==` examples and
on the inline `<` turns the file RED —
`outcome=ERROR declared>=8 executed=8 passed=5 failed=3 skipped=0 dropped=0`.

Note for whoever triages the sibling: `bdd_expect_compare_to_equal_bool_eager_fail_2026-06-30.md`
is a DIFFERENT root cause (the seed BDD runner's per-example `BDD_EXPECT_FAILED`
flag) with the same surface symptom, and this re-check says nothing about it.
