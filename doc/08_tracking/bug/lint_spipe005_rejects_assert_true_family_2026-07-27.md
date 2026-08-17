# SPIPE005 does not recognize `assert_true`/`assert_false` as assertions — contradicts the testing rule

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane F)
**Area:** `src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:376`
**Severity:** medium — the linter rejects the assertion form the project's own rules
prescribe, forcing contrived workarounds in new specs

## Finding

`SPIPE005` ("no real assertion in example") recognizes only the `expect(`-family as
a genuine assertion — `expect(`, `expect_not(`, `to_equal(`, `to_contain(`, and
similar matchers. **The standalone `assert_*` family is not in the list.**

So an `it` block whose only assertion is `assert_true(...)` is reported as having no
real assertion and fails lint.

This directly contradicts `.claude/rules/testing.md`, which prescribes that family:

> **Standalone assertions:** `assert_true`, `assert_false`, `assert_equal`,
> `assert_not_equal`, `assert_contains`, `assert_nil` — use these for bare
> boolean/equality checks instead of `expect(x).to_equal(true)`

It also collides with lint rules **SPIPE006/SPIPE007**, which actively *push authors
away* from `expect(bool).to_equal(true)` / `.to_equal(false)` and toward
`assert_true` / `expect_not`. The two rule families therefore give contradictory
instructions: SPIPE006/007 say "use `assert_true`", SPIPE005 says "`assert_true` is
not an assertion".

## Impact

An author following the documented rule writes a correct spec that fails lint. The
observed workaround was to introduce a `marker()` helper plus `to_equal` purely to
satisfy the checker — i.e. **the lint rule induced less direct test code**, which is
the opposite of its intent.

Because the test runner's post-spec lint gate turns lint findings into spec
failures (see
`test_runner_post_spec_lint_gate_empty_file_arg_2026-07-20.md`), this can also
present as a phantom test failure rather than as a lint message.

## Reproduction

Write an `it` block whose only assertion is `assert_true(some_condition)` and run
`bin/simple lint <spec>`; SPIPE005 fires.

## Fix

Add the standalone assertion family to the recognized-assertion set at
`traceability_and_assertions.spl:376`: `assert_true`, `assert_false`,
`assert_equal`, `assert_not_equal`, `assert_contains`, `assert_nil`.

Add a regression fixture covering an `assert_true`-only example (must pass lint) and
an example with genuinely no assertion (must still fire SPIPE005), so the rule keeps
catching what it is for.

## Verification at HEAD (2026-08-01, read-only static analysis)

Confirmed. The rule is at
`src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:383`
(inside `me check_spipe_example_bodies`, declared line 343). The exact condition:

```
val assertion_like = normalized.contains("expect(") or normalized.contains("expect_not(")
    or normalized.contains("to_equal(") or normalized.contains("to_be(")
    or normalized.contains("is_equal(") or normalized.contains("to_contain(")
    or normalized.contains("to_start_with(") or normalized.contains("to_end_with(")
    or normalized.contains("to_be_greater_than(") or normalized.contains("to_be_less_than(")
    or (trimmed_stmt.starts_with("expect ") and trimmed_stmt.len() > 7)
```

`normalize_lint_line` (line 573) only strips spaces/tabs, so no `assert_*` spelling
can incidentally match. An `it` block whose only statement is `assert_true(x)` sets
`has_real_assertion = false` and fires SPIPE005 at line 390 (Deny, category
`spipe_empty_examples` — `config_and_model.spl:591`).

### The docs are right; the rule is wrong

- `assert_true` is a real, failing assertion: `src/lib/nogc_sync_mut/spec.spl:749`
  (`if not value: fail_assertion("Expected true")`), plus the same family in
  `src/lib/*/src/testing/helpers.spl:47`. It is also injected into every spec
  prelude by `test_runner_execute.spl:342` / `test_result_wrapper.spl:67`, so it is
  the runner's own sanctioned form.
- `.claude/rules/testing.md:14-15` prescribes it and records that
  `to_be_true`/`to_be_false` are rejected by the runner on bool receivers.
- **The linter contradicts its own autofix.** `SPIPE006`'s easy-fix at
  `traceability_and_assertions.spl:646` rewrites `expect(x).is_equal(true)` into
  `assert_true(x)` — output that SPIPE005 then rejects. Applying one lint's autofix
  produces a Deny from another lint in the same file.

### A regression spec for the fix is ALREADY IN TREE and must be red

`test/02_integration/app/spipe_quality_lint_spec.spl:107-126` — "accepts the
standalone assert_ family as a real assertion" asserts
`count_lint(source, "SPIPE005") == 0` for all six `assert_*` forms. Its sibling at
:128-136 ("still flags an assertion-free example next to an assert_ one") asserts
the rule still fires on a bare `run_check()` block. So the fix's guard rails exist;
only the rule source was never updated. (Not executed here — ENOSPC lane is
read-only. Static reading of line 383 says the :107 example cannot pass.)

### Precise one-line change (NOT applied)

`traceability_and_assertions.spl:383` — append to the `assertion_like` disjunction:

```
 or normalized.contains("assert_true(") or normalized.contains("assert_false(")
 or normalized.contains("assert_equal(") or normalized.contains("assert_not_equal(")
 or normalized.contains("assert_contains(") or normalized.contains("assert_nil(")
```

Note `assert_equal(` also substring-matches `assert_not_equal(`, so five tokens
would suffice, but list all six for readability. Nothing else changes: the
`statements.len() == 0` arm (line 370) and the sanctioned-skip arm are untouched,
so empty bodies and no-assertion bodies still Deny.

### Blast radius

Scoped to spec files only (`path.ends_with("_spec.spl") or path.contains("/test/")
or path.starts_with("test/")` — line 571). The change is purely additive to a
disjunction: it can only turn existing SPIPE005 firings off, never on. It does not
weaken detection of the thing the rule is for — a body with no assertion at all,
or an empty body, still fires, as the :128 regression example pins.

Tree-wide static count (a faithful re-implementation of `check_spipe_example_bodies`
+ the `is_test_like_file` gate at line 571, run read-only over `test/` and `src/`,
excluding `vendor`/`build`/`target`; the linter itself was NOT run — ENOSPC lane):

| | it-blocks | files |
|---|---|---|
| spec-scope `.spl` files scanned | — | 25,912 |
| SPIPE005 "no real assertion" firings today | 201,592 | 8,873 |
| …whose block DOES use a standalone `assert_*` (silenced by the fix) | 2,667 | **315** |
| residual firings still caught after the fix | 198,925 | 8,558 |

So the change flips diagnosis on **315 files / 2,667 examples — about 1.3 % of
current SPIPE005 firings.** It is additive to a disjunction, so it can only remove
firings, never add them, and the remaining 98.7 % keep firing. This is not
"silencing the rule".

Two caveats on that table, both pointing at further work rather than at this fix:

1. The absolute firing count is enormous, which says SPIPE005 has a much broader
   recall problem than the `assert_*` gap. Spot-checked residual examples include
   `test/shared/core/hello_spec.spl:18` (`if not true: fail("...")` — a real check
   the rule does not recognise) and helper-wrapped assertions. Those are separate
   defects; do not fold them into this one-line fix.
2. Sample confirmations of the `assert_*` class:
   `test/shared/control_flow/no_paren_spec.spl:5, :9, :20` — e.g. a block that is
   exactly `val list = [1, 2, 3]` / `assert_true(list.len == 3)` fires SPIPE005
   today.

Existing `@allow(spipe_empty_examples)` opt-outs already appear in generated
wrapper specs under
`src/compiler/70.backend/linker/test/.spipe_wrapped_entry_*_spec.spl` — direct
evidence of the workaround this bug predicts.

## Related

- `.claude/rules/testing.md` § Standalone assertions
- `doc/08_tracking/bug/lint_coll006_false_positive_integer_accumulator_2026-07-27.md`
  — a second lint false positive found the same day
- `doc/08_tracking/bug/test_runner_post_spec_lint_gate_empty_file_arg_2026-07-20.md`
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
