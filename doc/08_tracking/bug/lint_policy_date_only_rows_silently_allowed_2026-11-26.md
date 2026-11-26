# Date-only diagnostic policy rows silently resolve to allow in CLI lint (2026-11-26)

Status: verification-pending

## Symptom
In `config/policy/diagnostic_policy.sdn`, a rule row that has `warn_since_date`
but no `warn_since_lang_version` always resolves to `allow` (stage "schedule")
in `simple lint`. This came in with PR #11849 (merge `2f13d8370469`), which added
more rows of this shape.

## Root cause
`DiagnosticPolicyInputV1.to_resolve_context()`
(`src/compiler/00.common/diagnostics/diagnostic_rule_policy.spl`) builds the
context with `release_date: ""`. The CLI lint overlay
(`policy_overlay_levels_with_context` in `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`)
never sets `policy_as_of`. In `DiagnosticPolicySnapshot.resolve`,
`date_reached("", threshold)` is false, and there is no edition gate to fall
back on. So every date-only row returns allow, and the engine says nothing.

## Fix (fail closed)
In `resolve`, a row with a date-only warn schedule is treated as started when the
effective date is unknown (empty). It then falls through to the profile baseline.
When a caller supplies an explicit release date or `policy_as_of`, the date
comparison works as before.

## Affected rows (CLI lint, no date supplied)
| rule | category | before | after |
|---|---|---|---|
| SPL-GC-001 (`gc_family_import`) | correctness | allow | warn (all profiles) |
| SPL-RET-001 (`ignored_return`, RET001) | correctness | allow | warn |
| SPL-IMPORT-001 (`use_unprovided_name`) | correctness | allow | warn |
| SPL-MATCH-002 (`match_fallthrough`) | correctness | allow | warn |
| SPL-MATCH-003 (`match_wildcard_catch`) | correctness | allow | warn |
| SPL-UNIT-002, SPL-PROVIDER-ABI-001, SPL-SFFI-RANGE-001, SPL-SFFI-ABI-001 | security | deny | deny (unchanged: the security stage runs before the schedule) |

The same resolver is also used by `driver_unit_profile.spl` and `doctor_cli.spl`,
which pass `""` as well, so they get the same correction.

## New findings
All five rows resolve to `warn`, and `warn` does not fail `simple lint` or a build.
The lint table default for these families was already `warn` before the policy
overlay. No lint warning ratchet or baseline exists, so there is nothing to rebaseline.

## Regression test
`test/01_unit/compiler/diagnostics/diagnostic_rule_policy_spec.spl`:
"fails closed on a date-only schedule when no release date is supplied (CLI lint path)".
It failed before the fix (23/24 passing) and passes after (24/24).
