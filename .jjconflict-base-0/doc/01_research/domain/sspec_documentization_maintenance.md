<!-- codex-research -->
# Domain Research: SSpec Documentization Maintenance

Date: 2026-08-03

## Question

How should a modern executable-specification tool assess documentation quality,
suggest or safely apply improvements, generate executable scenarios from a
reference specification, and produce a professional living specification?

## Executive finding

Treat documentization as a first-class maintenance analysis beside lint and
duplicate-check, but do not reduce it to one opaque grade. The useful product is
a deterministic, multidimensional scorecard backed by stable, located findings,
safe previewable edits, traceability to source requirements, and a layered
living manual. LLM assistance is appropriate for explaining ambiguous findings
or drafting optional prose, not for inventing requirements, oracles, or passing
assertions.

## Executable specifications and living documentation

Cucumber describes executable specifications as scenarios made of ordered
steps, and its official formatter model derives reports from execution events.
Gherkin supports Feature/Rule/Scenario hierarchy, Markdown descriptions, tags,
tables, and examples. It recommends concrete examples with a small number of
expressive steps, while separating behavior from incidental UI procedure.

- [Cucumber introduction](https://cucumber.io/docs/)
- [Gherkin reference](https://cucumber.io/docs/gherkin/reference/)
- [Cucumber reporting](https://cucumber.io/docs/cucumber/reporting/)
- [Better Gherkin](https://cucumber.io/docs/bdd/better-gherkin/)

Serenity's living-documentation model adds a layered requirements hierarchy,
stakeholder narrative, business rules and examples, status, coverage, and
evidence. Its central distinction is useful for SPipe: living documentation is
not merely a test report produced after implementation.

- [Serenity living documentation](https://serenity-bdd.github.io/docs/reporting/living_documentation)

Allure demonstrates the execution-evidence half of a professional manual:
nested steps, parameters, status, duration, attachments, history, retries, and
stability. These belong after the stakeholder-facing flow rather than replacing
it.

- [Allure test steps](https://allurereport.org/docs/steps/)
- [Allure history and retries](https://allurereport.org/docs/history-and-retries/)

### Implication for SPipe

Generated documents should layer information in this order:

1. provenance, freshness, purpose, audience, and scope;
2. capability/rule hierarchy and assumptions;
3. primary user/operator workflows with ordered steps and examples;
4. requirement-to-scenario traceability;
5. outcomes, captures, durations, and environment evidence;
6. unsupported, pending, ambiguous, and troubleshooting cases;
7. documentization scorecard and actionable maintenance findings;
8. generation metadata, source hash, tool version, and history.

The generator may assemble source facts and execution evidence. It must not
invent missing explanations or expected behavior.

## Quality analysis and scoring

Test-smell research supports automated structural findings but also shows that
rules need calibration. tsDetect reports detection across 19 test-smell types
and measured precision/recall; later studies show that smell severities differ
and that automatic or LLM refactoring can introduce new smells or reduce test
coverage.

- [tsDetect empirical evaluation](https://testsmells.org/assets/publications/FSE2020_TechnicalPaper.pdf)
- [Developers' perception of test-smell severity](https://arxiv.org/abs/2107.13902)
- [LLMs detecting and correcting test smells](https://arxiv.org/abs/2506.07594)

PIT's mutation-testing guidance is a useful boundary: execution or line
coverage does not prove oracle strength; mutation measures whether tests detect
injected faults. Mutation is expensive and implementation-centric, so it
should be optional evidence rather than a mandatory documentization component.

- [PIT mutation testing](https://pitest.org/)

SonarQube quality gates demonstrate that maintainers need explicit conditions
over named metrics, especially for changed code, rather than an unexplained
single score.

- [SonarQube quality gates](https://docs.sonarsource.com/sonarqube/latest/user-guide/quality-gates)

### Recommended score model

Report both an aggregate 0-100 convenience score and the evidence behind these
separate dimensions:

| Dimension | Example evidence |
|---|---|
| Narrative clarity | purpose/context docstring, outcome-named scenarios, domain language |
| Behavioral structure | ordered steps, setup/action/outcome visibility, focused scenario size |
| Oracle strength | concrete assertions, absolute oracles, no tautologies/placeholders |
| Traceability | stable requirement IDs, resolvable sources, scenario/manual anchors |
| Evidence completeness | appropriate capture, outcome, environment, artifact provenance |
| Coverage of behavior | primary, negative, boundary, unsupported, and recovery cases |
| Maintainability | named helpers, low duplication, folding/sections, deterministic metadata |

Hard blockers such as placeholder passes, zero executed examples, invented
oracles, dangling requirement IDs, and source-only pseudo-system tests must not
be hidden by a high average. Scores are guidance; configured thresholds decide
exit status. Every deduction must cite a stable rule and concrete evidence.

## Actionable finding interchange

SARIF 2.1.0 provides an established model for actionable static-analysis
results: stable opaque rule IDs, severity, messages, physical and related
locations, fingerprints/baselines, optional fixes, and suppression metadata.
GitHub's SARIF guidance additionally emphasizes rule help, precision, severity,
and stable fingerprints.

- [OASIS SARIF 2.1.0 plus Errata 01](https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html)
- [GitHub SARIF support](https://docs.github.com/en/code-security/reference/code-scanning/sarif-files/sarif-support)

An SSpec finding should therefore carry:

- stable rule ID and score dimension;
- severity and confidence/precision;
- source path, line/column/span, and related manual section when applicable;
- observed evidence, rationale, and remediation guidance;
- whether a deterministic safe edit exists;
- a stable fingerprint and baseline state;
- an optional suppression with owner and reason.

Human text and pure JSON should serialize the same report model. JSON output
must contain no progress/log noise so LLMs and IDEs can consume it reliably.

## Safe automatic changes

Modern codemod tools separate discovery and application. OpenRewrite exposes a
dry-run producing a patch before the apply task and can gate on proposed
changes. clang-tidy can export fixes separately from applying them. Semgrep
previews fixes before explicit autofix. OpenRewrite recipe tests require
before/after expectations and no unnecessary edits.

- [OpenRewrite Gradle dry run](https://docs.openrewrite.org/reference/gradle-plugin-configuration)
- [OpenRewrite recipes](https://docs.openrewrite.org/concepts-and-explanations/recipes)
- [OpenRewrite recipe testing](https://docs.openrewrite.org/authoring-recipes/recipe-testing)
- [clang-tidy](https://clang.llvm.org/extra/clang-tidy/)
- [Semgrep fix authoring](https://semgrep.dev/blog/2022/tips-and-tricks-for-writing-fixes/)

Recommended workflow:

`scan -> score/report -> select -> preview diff -> confirm/apply -> reparse -> format -> focused check`

Only deterministic, idempotent, behavior-preserving edits should be marked
machine-applicable. Narrative rewrites, requirement mapping, expected results,
and oracle changes remain suggestions or confirmed user-selected edits. Apply
one finding or an explicitly selected safe batch, retain a patch/rollback
artifact, and run each unchanged verification once.

## Reference specification to executable SSpec

Contract-driven tools demonstrate that generation is reliable when the source
specification is structured and preserves identity. Specmatic derives positive
and negative contract tests from OpenAPI, while Schemathesis generates
property-based cases and reproduction commands. Cucumber treats undefined or
pending steps as non-passing rather than silently accepting them.

- [Specmatic contract testing](https://docs.specmatic.io/contract_driven_development/contract_testing)
- [Schemathesis quick start](https://schemathesis.readthedocs.io/en/stable/quick-start/)
- [Cucumber API: undefined and pending steps](https://cucumber.io/docs/cucumber/api/)
- [Requirements traceability in model-based testing](https://doi.org/10.1109/VALID.2009.15)

A reference-spec-to-SSpec generator should:

- preserve source requirement IDs, locations, and hashes;
- map explicit preconditions, actions, outcomes, examples, and constraints;
- generate a traceability table and request confirmation for ambiguous mapping;
- produce modern manual sections, outcome-named scenarios, ordered steps, and
  capture placeholders;
- use explicit `fail("TODO: ...")` or `assert(false)` for unresolved setup or
  oracles, never a placeholder pass;
- make regeneration deterministic and idempotent;
- separate positive, negative, boundary, and unsupported cases when the source
  actually defines them.

Free-form Markdown can yield a reviewable scaffold, not automatically trusted
test semantics. LLM extraction should emit candidates with source evidence and
confidence; a human confirms the mapping before application.

## Recommended direction for Simple

Create one maintenance front end that reuses SPipe's canonical parser/docgen
and EasyFix's replacement/applicator model. Keep `simple lint` responsible for
code correctness/style and keep `simple duplicate-check` responsible for
duplication. The documentization command owns scenario/manual quality,
reference scaffolding, and the combined scorecard.

Deprecate parallel simplistic doc generators only after compatibility mapping.
`simple spipe-docgen` remains the generation engine; the maintenance command
may invoke it to compare source and mirrored-manual completeness. Avoid making
the legacy line-count heuristic or a generated timestamp the definition of
professional quality.

## Risks

- A score is gameable if evidence is opaque or one dimension masks blockers.
- Static smell rules can false-positive; publish rule help and support reasoned
  suppression.
- Generated tests inherit ambiguity from source specifications.
- LLM prose can sound complete while inventing behavior; keep it preview-only.
- Automatically adding generic docstrings can lower trust even while raising a
  structural score.
- Full-tree generation and mutation analysis can be too slow for a maintenance
  hot path; use scoped incremental analysis and optional deeper evidence.
