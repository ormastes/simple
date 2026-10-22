# Any warning policy acceptance

Executable specification: [any_warn_rules_acceptance_spec.spl](../../../../../../test/01_unit/compiler/lint/frontend_diag/any_warn_rules_acceptance_spec.spl).

Requirements: `doc/02_requirements/language/mission_critical_profile.md`, REQ-MC-012–014, and the Any capability rules in `doc/02_requirements/language/critical_completeness.md`.

## Evidence status

This is an authored manual of the executable scenarios, not generated execution evidence. The updated specification has not run on an eligible full pure-Simple CLI. Checker-child invocation, interpreter assertions, runtime latency/RSS, and required core/MCP checks remain unverified. No warning-count reduction or production verification PASS is claimed.

## Resolve robust warning severity

1. Resolve moderate, strict, robust, and critical profile settings. Moderate/strict allow the three migration-rule families by default; robust/critical warn.
2. Apply explicit family settings. An explicit `allow`, `warn`, or `deny` retains its level when environment defaults are present. A disabled family must remain absent from the checker mask even when other families run.
3. Apply environment defaults only to families without explicit settings. Environment `deny` escalates profile warning defaults. The `off` kill switch disables the migration checker.
4. Apply warning-phase reporting. Enabled warning phase downgrades reporting to warnings without enabling an explicitly disabled family.
5. Exercise the actual HIR detector, report formatting, report parsing, and relay path. Compare concrete findings and family-specific severities rather than configuration values alone.

## Check each finding family

- Written Any declarations: parameters, return values, fields, and locals retain their own source locations. Nested/lowercase/multiline type spellings are covered; non-type expressions are excluded.
- Inferred Any flowing into concrete uses: arithmetic, comparison, typed arguments/returns, and unannotated aliases are covered. Typed values, nil comparisons, and untyped sinks do not produce these findings.
- Any iterable/receiver uses: `for` and method-call findings are separate from inferred-use findings. Concrete receivers do not produce an Any warning.
- Source and capability boundaries: these migration rules retain compiler-source scope and the established unsafe-block exemptions. They do not weaken the independent critical escape-denial rules.

## Reject invalid checker evidence

Missing, failed, and truncated child reports must differ from a checked clean report. Concurrent invocations require distinct report paths. Per-file output caps preserve the sentinel's full finding count. These authored negative controls do not establish that a real checker child was launched successfully.

## Qualification still required

Run the executable specification and real checker-child scenarios with an eligible full self-hosted CLI; retain the commands, outputs, and exact source/runtime identities. Run the required compiler/library/MCP/LSP checks afterward. Until those pass, this manual is a source-review aid and the policy change remains unqualified for landing.
