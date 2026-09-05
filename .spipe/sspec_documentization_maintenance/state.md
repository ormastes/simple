# Feature: SSpec Documentization Maintenance

## Raw Request

> $sp_dev update skill and sspec write and refactoring guide with llm wiki update. make sspec documentize level tool as mantenance tool like dullication and lint. research how to scan improve point and sugget improve ways by tool for llm or auto change with confirm or option. autochange infra exidts reuse it if possible. 1. can make tool more like modern sspec test which generate spec doc. can scoring sspec in documentization score it genrate. 2. reference spec -to-sspec tool gen sspec. modern sspec should like that. even the tool used test gen doc is not professional? suggest and update guide refactoring skill, test skill, and llm wiki. 3. research how sspec gen doc be like more complete spec doc. research web.

## Task Type

feature

## Refined Goal

Provide a professional SSpec documentization maintenance workflow that audits and scores executable scenarios and generated manuals, recommends or safely applies confirmed improvements, scaffolds modern SSpec from reference specifications, enriches SPipe-generated specification manuals, and keeps all authoring/refactoring/test skills and LLM process documentation aligned.

## Acceptance Criteria

- AC-1: Local and domain research artifacts identify the current SSpec/SPipe docgen flow, existing lint/duplication and confirmed auto-change infrastructure, current manual-quality gaps, spec-to-test prior art, and externally sourced professional executable-spec documentation practices.
- AC-2: Selected feature and NFR requirement documents define independently testable behavior, score semantics, safety/confirmation behavior, output formats, performance bounds, and compatibility expectations; no active `*_options.md` remains after selection.
- AC-3: A repository maintenance command scans one SSpec file or a supported scope and emits deterministic documentization findings with stable rule IDs, source locations, severity, rationale, suggested improvements, and an aggregate score whose components are explainable.
- AC-4: The maintenance command supports human-readable and machine-readable output suitable for an LLM, reports generated-manual completeness where a mirror exists, and exits nonzero only according to a documented threshold/policy rather than merely because advice exists.
- AC-5: Safe mechanical improvements reuse the repository's existing confirmed auto-change infrastructure when technically suitable; preview is the default, interactive confirmation or an explicit apply option is required for writes, and non-mechanical findings remain suggestions rather than invented prose or silently changed behavior.
- AC-6: A reference-spec-to-SSpec workflow generates or previews a modern SSpec scaffold with requirement traceability, manual sections, outcome-named scenarios, ordered `step("...")` flow, capture placeholders, and explicit fail-fast TODO assertions; it never represents generated placeholders as passing evidence.
- AC-7: SPipe doc generation produces a more complete professional manual from modern SSpec metadata and structure, including purpose/context, requirement traceability, primary workflow, evidence/captures, outcomes, edge or folded sections, troubleshooting/verification information, and an explicit score/findings summary when requested, without inventing unsupported narrative.
- AC-8: Focused unit/integration/system SSpec coverage proves scoring determinism, representative good/bad rules, threshold exits, JSON purity, preview/apply/decline behavior, spec-to-SSpec fail-fast scaffolding, and generated-manual structure; the mirrored manual reads as an operator specification without opening the source spec and reports zero stubs for completed examples.
- AC-9: The canonical SSpec authoring and refactoring guides explain the professional modern-SSpec standard, documentization maintenance command, scoring interpretation, spec-to-SSpec workflow, safe auto-change policy, and how this gate relates to lint and duplicate-check.
- AC-10: Workflow/process references are synchronized across `.codex/skills/sp_dev`, relevant refactor/test/system-test skills, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.gemini/commands`, `doc/00_llm_process/llm_wiki.md`, relevant `doc/07_guide` pages, and generated/manual `doc/06_spec` content; explicit `N/A` rationales are recorded for genuinely unaffected surfaces.
- AC-11: Focused verification passes once per criterion, the generated-spec layout guard returns zero executable specs under `doc/06_spec`, direct env/process runtime guards pass for working and staged scopes, and no unrelated shared-worktree edits are included in this lane.

## Scope Exclusions

- Rewriting unrelated existing SSpec suites solely to raise their scores.
- Using an LLM to invent domain requirements, expected outcomes, or passing assertions absent from the reference specification.
- Replacing SSpec as the executable authoring surface or SPipe as the runner/docgen/process layer.
- Releasing, committing, or pushing without a separate explicit user request and a verified PASS.

## Cooperative Review

- Sidecar lane A: inventory local SSpec/docgen, scoring/lint/duplicate tooling, and confirmed auto-change reuse points.
- Sidecar lane B: research external executable-specification, living-documentation, test-quality scoring, and spec-to-test generation prior art.
- Merge owner: primary Codex `/root` lane.
- Final reviewer: normal/highest-capability primary Codex after implementation and generated-manual review.
- Shared interface names (provisional until selected requirements): `SspecDocumentizationFinding`, `SspecDocumentizationScore`, `SspecDocumentizationReport`, `SspecMaintenanceOptions`, and `ReferenceSpecScaffoldOptions`.
- Manual flow steps: `Inspect the SSpec documentization baseline`; `Review scored improvement findings`; `Preview safe mechanical changes`; `Confirm selected maintenance changes`; `Generate and inspect the professional specification manual`.
- Setup/checker helpers: `load_sspec_documentization_fixture`, `expect_documentization_finding`, `expect_documentization_score`, `expect_preview_unchanged`, `expect_confirmed_change`, and `expect_generated_manual_section`.
- Fail-fast placeholder policy: generated scaffold TODOs use `fail("TODO: replace generated placeholder with an executable assertion")` or `assert(false)` and cannot count as PASS.
- Generated-manual review owner: primary Codex, with an independent sidecar review after substantive revision.

## Phase

verification-blocked

## Log

- dev: Created state file with 11 acceptance criteria (type: feature).
- research: Completed local and domain research with independent repository and web sidecars; primary Codex reviewed and merged the findings.
- research: Wrote feature options A-D and NFR options A-C; implementation is paused for mandatory user selection.
- requirements: User selected Feature B (dedicated `simple sspec-maintain`) and NFR B (CI-ready and LLM-friendly).
- requirements: Wrote final feature/NFR requirements and deleted the selected lane's option drafts.
- design: Architecture and system-test sidecars reviewed the selected B/B lane;
  wrote architecture, detail design, test plan, agent tasks, executable system
  specification, and mirrored operator manual.
- implementation: Added `src/app/sspec_maintain/` with typed findings, seven
  weighted scores, stable fingerprints, mirror identity, human/JSON/SARIF
  renderers, EasyFix-backed safe-preview metadata, rollback-aware apply,
  reference scaffolding, cache/baseline identities, and manual rendering.
- integration: Registered `sspec-maintain` in the CLI table/help/dispatch and
  conservative mutating MCP surface; added unit, integration, system, and
  retained performance specifications.
- docs: Updated Codex/Claude/Gemini SPipe, test, refactor, and verify guidance,
  repaired invalid bare `@step` template guidance, added the maintenance guide,
  and appended the LLM wiki without overwriting concurrent content.
- verification: Skill validator passes `refactor` and `verify`; existing
  underscore names make `sp_dev` and `system_test` fail the validator's
  hyphen-name convention. The first self-hosted check is blocked before feature
  parsing by an unrelated `<<<<<<< Conflict 1 of 1` marker in
  `src/compiler/10.frontend/core/parser_stmts.spl`; per concurrent-work and
  no-repeat rules this lane did not edit it or rerun the identical gate.
- verification: Scoped `git diff --check` passes; the layout guard reports zero
  executable specs under `doc/06_spec`; working and staged direct env/process
  facade audits both report PASS; all REQ-001 through REQ-012 identifiers are
  present in implementation/test evidence; the manual has all eight required
  sections. STATUS remains FAIL until the unrelated merge markers are resolved
  and the focused unit/integration/system/performance gates can execute.

## Research Artifacts

- `doc/01_research/local/sspec_documentization_maintenance.md`
- `doc/01_research/local/sspec_documentization_maintenance_tldr.md`
- `doc/01_research/domain/sspec_documentization_maintenance.md`
- `doc/01_research/domain/sspec_documentization_maintenance_tldr.md`
- `doc/02_requirements/feature/sspec_documentization_maintenance.md`
- `doc/02_requirements/feature/sspec_documentization_maintenance_tldr.md`
- `doc/02_requirements/nfr/sspec_documentization_maintenance.md`
- `doc/02_requirements/nfr/sspec_documentization_maintenance_tldr.md`
