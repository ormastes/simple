# SPIPE005 does not recognize `assert_true`/`assert_false` as assertions — contradicts the testing rule

**Status:** open
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

## Related

- `.claude/rules/testing.md` § Standalone assertions
- `doc/08_tracking/bug/lint_coll006_false_positive_integer_accumulator_2026-07-27.md`
  — a second lint false positive found the same day
- `doc/08_tracking/bug/test_runner_post_spec_lint_gate_empty_file_arg_2026-07-20.md`
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
