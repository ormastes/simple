# Bug: `expect(a == b).to_equal(false)` mis-evaluates the inline `==` argument

**Date:** 2026-07-07
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
