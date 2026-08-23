# Feature Expert: COW-Alias Hot-Path Lint

## What this feature is

`PERF-COW-001/002/003` — an authoring-time lint for Simple's copy-on-write
alias defect class. Rule name `cow_alias_hotpath`, warn-level.

- Implementation: `src/compiler/35.semantics/lint/cow_alias_hotpath.spl`
- Wiring: `src/compiler/90.tools/lint/_LintMain/lint_checks.spl`
  (`check_cow_alias_hotpath_spl`, called from the per-file check sequence) and
  the code→rule-name map in `_LintMain/config_and_model.spl`
- Guide: `doc/07_guide/tooling/lint/cow_alias_hotpath_rule.md`
- Class analysis: `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`
- Open backlog: `doc/08_tracking/bug/cow_alias_hotpath_lint_findings_backlog_2026-08-23.md`

## Boundary rule

This lint is the AUTHORING-time half of a two-part gate. The PUSH-time half is
`scripts/check/check-cow-alias-hotpath.shs`, which owns the frozen baseline.
Never change one's detection semantics without changing the other: the spec
`test/01_unit/compiler/lint/cow_alias_hotpath_spec.spl` deliberately lifts its
acceptance cases from the ratchet's selftest fixtures so divergence shows up as
a red test rather than as two tools quietly disagreeing.

Do not escalate the rule to `Deny` while the backlog is non-empty. Do not
"fix" a ratchet FAIL by regenerating its baseline.

## Review checks

- A new detection shape must ship a must-NOT-flag fixture too. Both existing
  false-positive fixes (per-function state reset; loop-varying receiver) were
  found only because someone measured what the rule claimed cost that was not
  there.
- The rule source must stay clean under its own rule — pinned by the self-
  application example in `cow_alias_hotpath_product_fixes_spec.spl`.
- Cost: keep it a single linear pass over `iter_code_lines`. Re-measure with
  `sh scripts/check/check-lint-cost-budget.shs` and an interleaved on/off A/B;
  a per-line-scan rule must stay inside box noise.
- A product fix is pinned by MECHANISM (the shape is absent), never by wall
  time — the cost is zero at collection size zero, so a fixture cannot
  distinguish O(1) from O(n) per write.
