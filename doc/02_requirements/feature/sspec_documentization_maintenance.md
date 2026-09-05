<!-- codex-research -->
# Feature Requirements: SSpec Documentization Maintenance

Status: Selected
Date: 2026-08-03
Selection: Feature Option B — dedicated `simple sspec-maintain` front end

## Goal

Provide one canonical maintenance workflow that measures and improves how well
SSpec source becomes professional SPipe living documentation, safely scaffolds
modern executable scenarios from reference specifications, and reuses existing
SPipe, lint, duplicate-check, and EasyFix owners.

## Requirements

### REQ-SSDOC-001 — Dedicated command family

The pure-Simple CLI shall expose `simple sspec-maintain` with these operations:

- `scan <scope>` — analyze SSpec source and, when present, its mirrored manual;
- `improve <scope>` — preview or explicitly apply safe mechanical changes;
- `scaffold <reference.md> --output <spec.spl>` — generate a modern fail-fast
  SSpec scaffold from a reference specification;
- `documentize <spec.spl>` — generate the professional mirrored manual through
  the canonical SPipe docgen owner and optionally include the scorecard.

Help shall explain the relationship to `simple lint`, `simple fix`,
`simple duplicate-check`, `simple spipe-docgen`, and legacy `simple spec-gen`.

### REQ-SSDOC-002 — Reusable analysis model

The analyzer shall expose reusable pure-Simple types equivalent to:

- `SspecDocumentizationFinding`;
- `SspecDocumentizationScore`;
- `SspecDocumentizationReport`;
- `SspecMaintenanceOptions`;
- `ReferenceSpecScaffoldOptions`.

A finding shall contain a stable `SSDOC-*` rule ID, score dimension, severity,
confidence, source path and location, observed evidence, rationale,
remediation, stable fingerprint, baseline state, and optional safe EasyFix.

The analyzer shall reference existing `SPIPE001..007` lint findings without
duplicating their correctness logic or IDs.

### REQ-SSDOC-003 — Explainable documentization score

`scan` shall emit named 0-100 component scores for at least:

1. narrative clarity;
2. behavioral structure;
3. oracle strength;
4. requirement traceability;
5. evidence completeness;
6. behavioral coverage;
7. maintainability.

It shall also emit one deterministic aggregate score with weights and every
deduction visible. Placeholder passes, no executed/real assertion, dangling
requirement references, invented oracles, and unconditional pending scaffolds
are blockers and cannot be hidden by the average.

### REQ-SSDOC-004 — Professional rule coverage

The first rule set shall detect representative modern-SSpec gaps including:

- test-speak or non-outcome scenario names;
- no visible `step("...")` flow;
- absent or generic placeholder narrative;
- unexplained magic expected values;
- missing capture/evidence for user/operator-facing scenarios;
- fake system narrative based only on source-text or local arithmetic;
- flat, unfolded scenario dumps;
- repeated setup that should be a named helper;
- missing verification/troubleshooting guidance;
- missing/stale requirements, plan, design, or research metadata;
- internal execution tags leaking into reader-facing output;
- missing negative, boundary, recovery, unsupported, or ambiguity cases when
  their requirement source defines them.

Each rule shall document what it detects, why it matters, scoring effect,
false-positive limits, suppression policy, and whether a safe edit exists.

### REQ-SSDOC-005 — Scope, output, and policy

`scan` shall accept one SSpec file or a supported directory scope. It shall
produce human, pure JSON, and SARIF-compatible output from one report model.
Machine stdout shall contain only the selected serialization.

`--min-score` and `--deny-severity` shall control exit status independently.
Advice alone shall not fail unless configured policy makes it a gate.
Deterministic ordering shall be by normalized path, source location, and rule
ID.

### REQ-SSDOC-006 — Mirrored-manual inspection

The analyzer shall derive the canonical `test/...` to `doc/06_spec/...` mirror,
detect missing/stale/structurally incomplete manuals, and score facts that are
visible in the generated document rather than source strings alone.

The analyzer shall distinguish implemented annotations from selected/planned
annotations and shall not penalize a source for unsupported syntax as though it
were available.

### REQ-SSDOC-007 — Preview-first confirmed improvements

`improve` shall preview a patch without changing files by default. Writes shall
require either interactive per-finding confirmation or explicit `--apply`.

Mechanical changes shall reuse EasyFix replacement/confidence/conflict and
atomic-write infrastructure. Apply shall retain a rollback patch, reject
overlapping/stale edits, reparse changed SSpec, and be idempotent. Narrative,
requirement mapping, outcome, and oracle changes shall remain suggestions unless
the user explicitly confirms an exact proposed edit.

Generic filler such as “Description of this block” shall never count as
professional documentation.

### REQ-SSDOC-008 — Reference specification to modern SSpec

`scaffold` shall parse supported Markdown requirement headings, stable IDs,
normative statements, preconditions, actions, expected outcomes, examples, and
source locations. It shall preserve source identity and content hash in the
generated scaffold and emit a mapping summary for review.

Generated SSpec shall use canonical `use std.spec.*`, outcome-named `it`
blocks, `step("...")`, requirement traceability comments/metadata supported by
the current toolchain, manual sections/folding metadata supported by the current
toolchain, and capture placeholders where the reference names visible evidence.

Any unresolved setup, action, or expected result shall use
`fail("TODO: replace generated placeholder with an executable assertion")` or
`assert(false)`. Generated placeholders shall be reported as stubs and never
count as passing evidence. Regeneration shall be deterministic and idempotent.

### REQ-SSDOC-009 — Professional document generation

`documentize` shall call/reuse the canonical SPipe parser and generator, not
create another parallel Markdown generator. When source facts exist, the manual
shall contain:

1. provenance, freshness, purpose, audience, and scope;
2. feature/rule hierarchy and assumptions;
3. primary user/operator workflows with ordered steps and examples;
4. requirement-to-scenario traceability;
5. outcomes, typed captures, durations, and environment evidence;
6. unsupported, pending, ambiguity, recovery, and troubleshooting information;
7. optional documentization scorecard/findings appendix;
8. source hash, generator/tool version, and generation history.

The generator shall assemble authored facts and execution evidence and never
invent missing prose or behavior. Executable SSpec shall remain folded detail,
not dominate the reader-facing flow.

### REQ-SSDOC-010 — Compatibility and canonicalization

`simple spipe-docgen` shall remain compatible in the first release.
`simple spec-gen` and older parallel generators shall be labeled legacy with
accurate replacement guidance; removal or output-changing aliasing requires a
separate audited migration.

CLI, MCP/tool surface metadata, help, and guides shall agree on whether a
command generates Markdown, scaffolds SSpec, or performs maintenance.

### REQ-SSDOC-011 — Workflow integration

The selected maintenance command shall be incorporated into SSpec writing,
system-test design, refactoring, SPipe development, and verification guidance.
The refactor flow shall run it beside lint and duplicate-check for changed
SSpec/manual scopes. Skills shall explain score interpretation, preview/apply
safety, reference scaffolding, generated-manual review, and failure policy.

Synchronized process surfaces shall include relevant `.codex/skills`,
`.agents/skills`, `.claude/skills`, `.claude/agents/spipe`,
`.gemini/commands`, `doc/00_llm_process/llm_wiki.md`, `doc/07_guide`, the SSpec
template, and the tool's mirrored `doc/06_spec` system manual. Unaffected
surfaces shall have an explicit `N/A` rationale in lane state/design.

### REQ-SSDOC-012 — Testable traceability

Unit, integration, and system SSpec shall cover every requirement, including
good/bad score fixtures, blockers, deterministic ordering, policy exits, pure
JSON/SARIF, missing/stale mirrors, preview/decline/apply/idempotence/conflicts,
reference scaffold traceability/fail-fast placeholders, professional generated
sections, compatibility help, and documentation-surface synchronization.

## Non-goals

- Rewriting unrelated SSpec suites to raise repository-wide scores.
- Treating LLM judgment as the deterministic CI score.
- Inventing missing requirements, expected outcomes, or passing assertions.
- Replacing SSpec, SPipe, lint, duplicate-check, or EasyFix.
- Removing legacy doc generators in this feature without a separate migration.
