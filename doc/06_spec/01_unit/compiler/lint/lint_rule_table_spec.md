# Static Lint-rule Table

- Executable: `test/01_unit/compiler/lint/lint_rule_table_spec.spl`
- Requirements: `KPM-NFR-002`, `KPM-REQ-004`, `KPM-REQ-007`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- runs a registered rule.
- does not run an unregistered rule.
- refuses a mismatched major before dispatch.
- refuses a provider that copied a sibling provider identity.
- refuses a provider that copied the host contract digest.
- refuses a host with a prewritten or mutated contract digest.
- derives every production row from its own canonical provider identity.
- runs two pre-existing sibling rules through table rows.
- removing one pre-existing row silences only that rule.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
