# mir_lowering_new_spec.spl: 19/34 failures are pre-existing, not caused by a399483d/796d8484

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Date: 2026-08-08

## Summary

`test/01_unit/compiler/mir/mir_lowering_new_spec.spl` (and its duplicate tree
copy `test/unit/compiler/mir/mir_lowering_new_spec.spl`) fails 19 of 34
examples (`15 passed, 19 failed`) on the deployed seed `bin/simple`. The
2026-08-08 session regression sweep report
(`doc/09_report/testing/session_regression_sweep_2026-08-08.md`) labeled this
"PRE-EXISTING" but cited no dated bug doc — unlike its other two cited
pre-existing failures. This was flagged as a possible unsubstantiated label,
because the same session's commits `a399483d` and `796d8484` edited two files
this spec reads and asserts against as raw source text:
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` and
`src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl`.

## A/B test performed

1. Ran the spec on the deployed `bin/simple` (Rust seed) with origin/main
   content of both files (post `a399483d`/`796d8484`):
   `bin/simple run src/app/test_runner_new/test_runner_single.spl
   test/01_unit/compiler/mir/mir_lowering_new_spec.spl --no-session-daemon
   --sequential` → **34 examples, 19 failures, 15 passed** (exact match to
   the sweep report's `FAIL 15/34 (19 failed)`).
2. Temporarily replaced both files with their content immediately before
   `a399483d` (`git show a399483d^:<path>`) and reran the identical command
   → **34 examples, 19 failures, 15 passed** — same counts.
3. Diffed the two runs' failing-example title lists (`grep '✗'` on both logs)
   → **byte-for-byte identical** set of 19 failing examples in both the
   pre-commit and post-commit code.
4. Restored origin/main content for both files
   (`git cat-file -p origin/main:<path> > <path>`) and verified the restored
   content matched byte-for-byte with `diff` against the pre-restore copies.

## Conclusion

The failures are unaffected by `a399483d`/`796d8484` — both commits are
strictly additive (`or name == "..."` alternatives appended to an existing
condition; new `declare ptr @...` lines appended after existing ones) and do
not touch any of the 19 failing examples' assertion targets. Most of the 19
failing examples read entirely different source files
(`expr_dispatch.spl`, `method_calls_literals.spl`,
`_MirLowering/module_lowering.spl`, etc.) that neither commit touched at all.

**VERDICT: genuinely pre-existing.** No regression from this session's span/
blend-span registration work. The failures are stale text-assertion checks
against MIR-lowering/LLVM-backend source that has drifted from the spec's
expected literal snippets — a separate, older issue that predates today's
work and needs its own root-cause pass (out of scope here).

## Correction to the regression-sweep report

`doc/09_report/testing/session_regression_sweep_2026-08-08.md`'s headline
said "11 suites clean ... 3 pre-existing-known failures" but its own results
table lists 14 suites with 4 FAIL rows (`mir_lowering_new_spec.spl`,
`tiered_jit_hotspot_spec.spl`, `browser_renderer_spec.spl`,
`web_css_text_layout_spec.spl`) and 10 PASS rows. The headline has been
corrected to "10 suites clean ... 4 pre-existing-known failures of 14 total"
and now points at this doc for the `mir_lowering_new_spec.spl` classification.
