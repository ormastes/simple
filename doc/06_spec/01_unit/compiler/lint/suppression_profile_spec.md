# Described suppression profile acceptance manual

Requirement: REQ-LINT-DESCRIBED-SUPPRESSION. Source: `test/01_unit/compiler/lint/suppression_profile_spec.spl`. Status: ten authored scenarios, all **UNRUN**; this manual is not generated execution evidence.

Setup uses actual `LintConfig` and `Linter` APIs. It disables ambient warning-phase variation explicitly, selects the requested profile through the existing parser, and passes source to `Linter.lint_source`. Assertions inspect actual diagnostic codes, levels, locations and EasyFix presence.

| Scenario | Action | Required observation |
|---|---|---|
| Ordinary profiles | Lint the same missing reason under unset, Moderate and Strict | Exactly one LINTALLOW001, Warn |
| Robust profiles and aliases | Select Robust/Critical/reliable/mission-critical | Exactly one LINTALLOW001, Deny |
| Location and guidance | Place an indented invalid attribute after a header | Line 2, column 3; reason guidance; no fabricated EasyFix |
| Described named positive | Explain why the fixture intentionally prints | No suppression issue or underlying print warning |
| Description boundary | Use whitespace-only reason or described blanket target | Exactly one Deny in each case |
| Self-suppression refusal | Suppress LINTALLOW001, with and without a description | Invalid admission remains Deny at its original line |
| Migration | Enable existing warning phase under Robust | The issue remains emitted at Warn |
| Final file profile | Put the file profile after the invalid attribute | Resolved Robust denies; resolved Moderate warns |
| Underlying warning | Use malformed print suppression under Robust | The original print warning remains Warn |
| Lexical controls | Put attribute lookalikes in comments and multiline strings | No suppression admission diagnostic |

Prerequisite cleanup retains seven existing lint/query contract checks and adds authored reasons to their intentional positive suppressions. Existing malformed negative controls are preserved. No CLI, compiler, runner, build or native probe was executed. Other warnings, engine defaults, broad warning cleanliness and runtime qualification remain separate gates.
