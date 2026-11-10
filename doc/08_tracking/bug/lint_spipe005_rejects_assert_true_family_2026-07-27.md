# SPIPE005 does not recognize `assert_true`/`assert_false` as assertions — contradicts the testing rule
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Addendum 2026-11-11 — lane runner4: SUPERSEDED

The fix is in the tree at release/1.0.0 tip `b364745fdbf8`:
`statement_has_direct_assertion`
(`src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:703-704`)
now recognizes the full standalone assertion family — `assert_true(`,
`assert_false(`, `assert_equal(`, `assert_not_equal(`, `assert_contains(`,
`assert_nil(` — exactly the list this doc prescribed.

seed-smoke verification with the refreshed 2026-11-11 seed (lint, JIT lane):

- Fixture whose only assertion is `assert_true(1 == 1)`: no SPIPE005
  (passes lint apart from unrelated docstring warnings).
- Fixture with a genuinely assertion-less example (`val x = 1`): SPIPE005
  still fires — the rule keeps catching what it is for.

Regression-fixture gap closed in this lane: the negative oracles already
existed in `test/02_integration/app/spipe_quality_lint_spec.spl` (unasserted
and empty-body examples), but no positive `assert_true`-only oracle did; added
`accepts examples whose only assertion is a standalone assert_`
(commit `43c481c4d9a2`). Note: that spec file has a PRE-EXISTING, unrelated
failure at HEAD — `respects allow on spipe_placeholder_tests` (allow-attribute
suppression, `expect(true).to_equal(true)` still linting despite
`@allow(spipe_placeholder_tests)`) — verified failing on the unmodified HEAD
file as well; not caused by and not in scope of this row.

Verdict: SUPERSEDED. The SPIPE005/SPIPE006 contradiction is resolved; authors
following `.claude/rules/testing.md` no longer get lint-induced workarounds.

