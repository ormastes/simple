# Static lint rules sharing a private `fn check_rule` dispatch into each other

**Status:** OPEN 2026-11-12 — pre-existing; observed while landing `robust_option_surface` (P1), which sidesteps it by naming its check fn uniquely.
**Severity:** Correctness of the live lint table (findings attributed to the wrong rule; some rules silently emit nothing).
**Affected files:** 15 of `src/compiler/90.tools/lint/rules/*.spl` declare a private `fn check_rule(params: LintParamsV1, unit: LintUnit)` (e.g. `nil_outside_unsafe_rule.spl:175`); `nil_return_non_optional_rule.spl:447` and `robust_option_surface_rule.spl` already use a unique name.
**Spec files:** none yet — reproducer below; the two-spec rule applies to the fix.

## Symptom

With the seed as the engine, running the full `static_lint_rule_table()` on
`pub fn connect(host: i64, timeout: Option<i64>) -> i64:` + `return nil`
emitted `ROB-OPT-001` 16 times (once per sibling whose `check_rule` resolved
to the newest module's `check_rule`) and never `NIL-UNSAFE-001`, while each
rule run alone through its own import path behaved correctly. The seed
prints the matching banner at startup:
`public function ... has N co-compiled definitions ... call sites resolve by
the caller's import path ... Rename the conflicting helper(s) to a unique
name. [compiler_cross_module_private_symbol_collision]`.
Renaming the new rule's fn to `robust_option_surface_check_rule` dropped the
count to one, which proves the mechanism.

## Unblock condition

Give every rule's check fn a unique name (`<rule>_check_rule`), then add a
spec that runs the full table on one fixture and asserts each code appears
exactly once; and a generalization spec asserting `NIL-UNSAFE-001` fires
through the full table (today it does not).
