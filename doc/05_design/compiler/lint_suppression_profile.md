# Described suppression admission in explicit robust profiles

Status: source candidate; all execution is UNRUN. This is the selected bounded continuation of the robustness plan, not whole-warning cleanup or blanket severity promotion.

## Existing behavior and selected requirement

The release baseline `2f7439a9cebafe4fd34bd9743720e01faed2da5b` already includes source-bound autofix and reason-required named `@allow` attributes. The existing lexical header pass records missing descriptions and blanket targets as `LintSuppressionIssue` values. `Linter.lint_source` nevertheless publishes every `LINTALLOW001` as Warn, including explicit Robust/Critical profiles. The rule is deliberately outside the configurable lint-family mapping so it cannot silence itself.

REQ-LINT-DESCRIBED-SUPPRESSION: keep missing descriptions advisory in unset/Moderate/Strict configurations; reject them in explicit Robust/Critical configurations after resolving file attributes. Preserve the existing warning-phase downgrade, described named suppression, underlying diagnostics, locations and non-fabricated fix guidance. The root accepted this scope; broader warning-to-error semantics remain separate.

Existing work was inspected before implementation. The retained `robust-warning-errors-20261016` and `simple-robust-warning-current-20261016` worktrees implement a general `lint_level_for_profile` policy. They do not implement this admission helper; their blanket publication policy is intentionally not imported. The modern `source_bound_autofix_spec.spl` supplies actual public API and lexical controls. Older profile/query contracts expose intentional fixture suppressions that require descriptions under the already-landed rule.

## Implementation and policy boundary

`lint_suppression_issue_level` lives with the existing lint configuration policy. It examines the final resolved profile, returns Deny only for Robust/Critical, and uses `phased_lint_level` so `warning_phase: true` still lowers that result to an emitted Warn. The existing source diagnostic producer consumes this level. No default-level table, configurable rule-name map, general publication policy, engine default helper or CLI route is changed.

`LINTALLOW001` remains unmapped. Neither a malformed self-suppression nor an otherwise described `@allow(LINTALLOW001)` can hide a subsequent invalid suppression. The existing exact lexical recognition, nonempty reason boundary and blanket-target rejection are preserved. The author supplies intent; the tool does not generate a reason, add unsafe, or claim to assess the truth of a description. Existing problem/location/message remain actionable and no machine-applicable rewrite is attached.

This intentionally does not make every robust warning an error: other warning policies are unchanged, and the explicit existing warning-phase migration knob remains effective. Engine default helpers are unchanged; this does not claim new engine/driver enforcement wiring.

## Prerequisite cleanup

Seven positive lint/query contract fixtures contained intentionally missing descriptions: wide export, argument count, LSP severity, stub implementation, query dispatch, duplicate typed arguments and combined collection/duplicate-type checks. Their source strings now state the concrete fixture purpose. The two query fixtures expecting zero diagnostics otherwise conflict with the already-landed reason rule. Negative malformed-suppression controls remain malformed. The configuration documentation examples now show descriptions.

The scoped pre-edit census found no actual `@allow` production directive in the lint owner directory; occurrences were messages, examples or parser code. This is not a repository warning census. No qualified CLI autofix was run and no production warning-clean result is claimed.

## Acceptance and cost

Ten authored SSpec scenarios invoke real `Linter.lint_source` and `LintConfig` APIs with deterministic warning-phase settings. They cover ordinary and robust profiles/aliases, exact location and absent EasyFix, described positive suppression, whitespace and blanket negatives, self-suppression, migration downgrade, attribute order, retained underlying warning and lexical lookalikes. The seven existing contract fixtures keep their actual API assertions.

The change adds a constant-time profile match for each already-collected suppression issue. It adds no source scan, cache, file access or dependency. Runtime, latency/RSS, full CLI/core/MCP checks and broader warning inventory remain UNRUN. Independent source review is required; it cannot substitute for execution.
