# SPipe Project-Local Knowledge, Pair-Expert, Link-Safe Documentation, and PR Auto-Balancing

## Final architecture, refactoring design, feature design, and implementation plan

**Date:** 2026-08-31
**Status:** Selected final design — **amended 2026-08-31 for pure Simple implementation**

> **Amendment note.** This document was written assuming the implementation
> language was JavaScript, following the existing `@simple-lang/spipe` npm
> package. That assumption is withdrawn. Per CLAUDE.md ("ALL code in
> `.spl`/`.shs`"; "Impl in Simple unless it has big performance differences"),
> the canonical implementation is **pure Simple** at `src/app/spipe/`, and the
> 8.6k-line JS package is feature-frozen legacy being superseded — not a
> precedent for new work.
>
> Sections affected are flagged inline below with **AMENDED**. The plan of
> record is
> `doc/03_plan/infra/spipe/spipe_knowledge_compiler_refined_plan.md`
> (Revision 2: pure Simple); where the two disagree, the plan wins. That plan
> also carries the corrections this document got wrong about the current tree
> — notably that `SPK704`, `SPK803`, `SPK804`, `SPK901` and `SPK902` are
> **already taken** by shipped code for unrelated meanings, so §12's
> assignments of those codes must not be implemented as written.
>
> **Build-order prerequisite (not a design change):** `admit` and `assume`
> were hard keywords until 2026-08-21. The `knowledge admit` verb and
> `AdmissionVerdict` type below are implementable only on a seed at or after
> that date; verify with `bin/simple --version` before starting.
**Applies to:** `ormastes/Spipe`, host repositories that install or mount SPipe, and the existing SPipe Knowledge Compiler work in `ormastes/simple`
**Primary objective:** Make SPipe a portable LLM plugin, knowledge base, skill base, document compiler, safe-refactoring engine, and pull-request admission system for any project.

---

## 1. Executive decision

The final design is:

1. **SPipe remains independent and project-local.** A repository may install it as a package, mount it under `.spipe/spipe`, or point to it explicitly. SPipe must not assume that it is the parent repository or that one particular host layout exists.
2. **The host application's canonical documentation remains a single lifecycle-first tree.** The configured top-level roots are fixed policy boundaries. Rebalancing is allowed only below them.
3. **`common` contains intentionally promoted reusable knowledge and skills carried by SPipe.** Project documents do not become common merely because they look generic. Promotion is a reviewed semantic ownership change with provenance.
4. **Application knowledge is presented in two orthogonal dimensions.**
   - feature;
   - technical structure: layer and/or component.

   These are generated read-only projections over the same canonical artifacts, not duplicated writable trees.
5. **There is no canonical `doc/app/project/` child-project store.** Linked projects are registered in `.spipe/projects.sdn`; a `project/` hierarchy may exist only as a generated workspace view.
6. **Reverse references are generated views.** The default root is `reverse_ref/`, with configurable relation folders such as `aspect/`, `trait/`, `interface/`, `symbol/`, `requirement/`, and `test/`. The former `spect` name becomes a compatibility alias during migration.
7. **Feature work is paired.** A feature expert owns end-to-end behavior and acceptance; a layer or component expert owns technical invariants, interfaces, performance, and reuse. They jointly operate on one artifact graph rather than maintaining parallel documents.
8. **Every pull request runs document integrity, balance analysis, and deterministic rebalancing.**
   - Generated virtual views are always rebalanced automatically.
   - Small, high-confidence, same-root physical moves are automatically applied when the PR branch is writable by a trusted SPipe writer.
   - A non-empty balance plan must be represented by a separate structural commit before merge.
   - Large, ambiguous, cross-policy, or high-churn reorganization is not hidden in a feature PR; it becomes dedicated structural work.
9. **Content edits and moves/renames must be separated by commit.** A structural commit may change paths, equivalent link destinations, aliases, and generated manifests, but not prose or semantics.
10. **Broken-link safety is binary and cannot be averaged away by a score.** The balance score is a separate 0–100 organization metric. Hard integrity failures always reject.
11. **Low-scoring PRs are rejected.** The stable target is 85, the normal touched-scope merge floor is 80, and the absolute floor is 70. Legacy scopes below 80 require an expiring debt record and measurable improvement until migrated.
12. **`RefactorService` remains the sole canonical-file mutation authority.** The rebalancer produces a plan; a separate admission/apply coordinator may authorize that plan for automatic PR application. This preserves the existing MDSOC and safety invariant.

This design amends the existing SPipe Knowledge Compiler design rather than replacing it. Its identity, graph, search, snapshot, transactional-refactor, virtual-view, and promotion foundations remain valid. The principal change is that safe physical rebalancing becomes a normal PR operation under a strict policy instead of remaining proposal-only.

---

## 2. Current repository status and implications

### 2.1 Standalone SPipe

The current standalone SPipe repository already has:

- a portable Node CLI and MCP server;
- setup scripts for linking reusable process surfaces into a host;
- Unix containment checks and Windows junction support;
- project/domain/tool expert directories;
- a feature-expert template;
- release and review-admission infrastructure;
- package and plugin projections.

However, the current document organization is still centered on:

```text
doc/00_llm_process/
  domain_expert/
  project_expert/
  skill_command/
  spipe/
  template/
  tool_expert/
```

Equivalent or selected files are copied into:

```text
plugin/doc/00_llm_process/
.claude/
.codex/
.gemini/
```

The build script proves equality with repeated `cmp` operations. That prevents drift only after duplication has already been created; it does not establish one canonical source.

The current MCP resource space exposes only the fixed `spipe://skill` document, and the current CLI still hard-codes process surface names and document roots. The GitHub workflow runs the general build but has no knowledge-graph, link-safety, balance-score, rebalancing, or PR admission job.

### 2.2 Existing implementation in `simple`

The `simple` repository already contains a substantial SPipe Knowledge Compiler chain:

```text
doc/01_research/infra/spipe/spipe_knowledge_compiler.md
doc/02_requirements/feature/spipe_knowledge_compiler.md
doc/02_requirements/nfr/spipe_knowledge_compiler.md
doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md
doc/05_design/infra/spipe/spipe_knowledge_compiler.md
doc/06_spec/03_system/app/spipe/feature/
  spipe_knowledge_compiler_rebalance_promotion_spec.md
```

It also contains a partial modular implementation under:

```text
examples/05_stdlib/spipe/
```

The observed implementation includes identity, authorization, snapshots, graph storage, extraction, exact lookup, BM25, and integration tests for earlier waves. It does **not** yet contain a released rebalancing subsystem. The current system specification explicitly checks that the released CLI does not expose rebalance or promotion commands.

### 2.3 Refactoring consequence

Do not start a second knowledge-compiler implementation in the standalone repository.

Use this sequence:

1. freeze compatibility behavior in standalone SPipe;
2. inventory the partially implemented knowledge core in the `simple` example;
3. transplant or upstream that modular core into standalone SPipe;
4. merge standalone SPipe's newer release/review capabilities;
5. make standalone SPipe the sole canonical implementation;
6. replace independent example copies with a package/submodule fixture or a generated immutable test projection;
7. ~~keep Simple as an optional high-performance provider, not an owner of SPipe correctness.~~

**AMENDED — step 7 is inverted.** Simple is the **owner** of SPipe correctness;
if anything, JS becomes a compatibility surface. The provider protocol survives,
but its reference implementation is `spipe_knowledge_provider` (already `.spl`),
and the JS `js_fixed_point.js` becomes the parity foil — mirroring the existing
`.spl` parity probes in reverse.

**AMENDED — step 5 cannot be executed from this repo.** `.spipe/spipe` is a
separate git repository with no `src/` at all (an older generation: package
0.1.0, self-contained `cli/spipe.js`, `.sh` not `.shs`). "Transplant the core
into standalone SPipe" has nowhere to land from here. All new work targets this
repo; the JS example is frozen in place, and the cross-repo consolidation is
deferred debt.

The observed package-version difference between the standalone package and the embedded example is further evidence that independent writable copies should be removed.

---

## 3. Architectural invariants

These invariants are normative.

### 3.1 Knowledge invariants

1. One conceptual artifact has one immutable UID and one canonical writable content copy.
2. Path, title, heading, semantic key, and virtual location are mutable names, never identity.
3. The canonical host documentation tree is lifecycle-first.
4. Feature, layer, component, project, status, trace, and reverse-reference trees are projections.
5. Top-level configured roots are fixed. Rebalancing cannot cross them.
6. Promotion from app knowledge to common knowledge is not rebalancing.
7. Reverse references are derived from canonical forward edges. They may be cached but are not separately authored graph truth.
8. Generated skills and virtual views are never canonical edit targets.

### 3.2 Mutation invariants

1. `RefactorService` is the only service allowed to mutate canonical documents.
2. Every structural mutation is planned against an immutable snapshot and content hashes.
3. Apply is transactional, journaled, bounded, reversible, and revalidated.
4. An approved refactor must preserve UIDs and accepted trace edges.
5. A file move may rewrite paths and links but must not silently rewrite prose.
6. An LLM edit is applied in a temporary overlay and rejected when the resulting graph is invalid.
7. Human editors may temporarily hold a broken working state, but commits and merges may not.

### 3.3 PR invariants

1. Every PR receives a balance report bound to its latest head SHA.
2. A new human commit invalidates the previous report and balance plan.
3. A non-empty safe balance plan requires a separate structural commit.
4. No empty bot commit is created when the plan is empty.
5. A structural commit must be semantically neutral according to UID-resolved AST comparison.
6. The required admission check must come from the configured GitHub App or trusted CI identity.
7. Merge-queue evaluation reruns admission for the synthetic merge group.
8. Privileged automation must not execute PR-controlled code.

### 3.4 Determinism invariants

1. Ordering uses normalized path and UID tie-breaks.
2. Objective arithmetic uses bounded integers or fixed-point milli-units, not platform-dependent floating-point decisions.
3. The same base, head, configuration, parser version, and policy version produce the same plan and report.
4. Reapplying the same balance operation is a no-op.
5. A clean full rebuild and the equivalent incremental update produce the same graph root and score.

---

## 4. Final MDSOC architecture

```text
KnowledgeCompiler
  parent, snapshot owner, publication authority
│
├── WorkspaceRegistry
│     host, linked projects, worktrees, revisions, trust, mounts
│
├── ParserService
│     Markdown/SDN/SSpec/source metadata -> immutable deltas
│
├── IdentityService
│     artifact UID, section UID, keys, aliases, canonical path
│
├── GraphService
│     typed forward edges, accepted/candidate authority, graph queries
│
├── CacheService
│     content-addressed objects, file/folder summaries, worktree overlays
│
├── ReverseReferenceService
│     derived incoming-edge index and reverse_ref projections
│
├── ProjectionService
│     lifecycle, feature, layer, component, matrix, project, reverse_ref
│
├── DiagnosticService
│     identity, links, trace, generated-view, commit-policy diagnostics
│
├── BalanceScoreService
│     deterministic organization metrics and score explanations
│
├── RebalanceService
│     affected graph, candidates, objective, deterministic plan only
│
├── RefactorService
│     sole canonical writer, journal, apply, recovery, rollback
│
├── DocAdmissionService
│     PR/base/head policy, score floors, commit separation, final decision
│
├── BalanceApplyCoordinator
│     obtains narrow authorization and submits an accepted plan to RefactorService
│
├── FeatureService
│     feature identity, lifecycle scaffolding, classifications, acceptance
│
├── PairExpertService
│     feature + layer/component expert selection and pair-session contract
│
├── PromotionService
│     common-knowledge candidate, provenance, review and publication plan
│
└── SkillCompiler
      canonical common/app skills -> Claude/Codex/Gemini/agent/plugin projections
```

### 4.1 Parent/child ownership

This follows MDSOC ownership rules:

- the parent owns startup, immutable snapshots, publication, and shutdown;
- children return typed deltas, diagnostics, or proposals;
- siblings do not mutate each other;
- cross-cutting concerns such as authorization, budget, observability, and trust are transforms around stable ports;
- runtime-selectable parsers, search providers, source analyzers, and materializers are adapters;
- no analyzer receives a general repository write capability.

### 4.2 Why the apply coordinator is separate

The existing architecture correctly makes the rebalancer proposal-only. Preserve that.

Automatic PR balancing is implemented as:

```text
RebalanceService
  read-only plan
      ↓
DocAdmissionService
  verifies policy, score, trust, budget and head binding
      ↓
BalanceApplyCoordinator
  obtains a single-use, plan-bound capability
      ↓
RefactorService
  performs the only canonical mutation
```

Therefore, "automatic" does not mean that an optimizer has unrestricted write access.

---

## 5. Canonical and generated layout

### 5.1 Host project

```text
<host>/
├── doc/
│   ├── 00_llm_process/
│   ├── 01_research/
│   ├── 02_requirements/
│   ├── 03_plan/
│   ├── 04_architecture/
│   ├── 05_design/
│   ├── 06_spec/
│   ├── 07_guide/
│   ├── 08_tracking/
│   ├── 09_report/
│   └── 10_metrics/
│
├── .spipe/
│   ├── config.sdn
│   ├── projects.sdn
│   ├── artifact_aliases.sdn
│   ├── taxonomy.sdn
│   ├── doc_balance_debt.sdn
│   ├── skill_src/
│   │   ├── project/
│   │   ├── feature/
│   │   ├── layer/
│   │   ├── component/
│   │   └── pair/
│   ├── state/
│   ├── transactions/
│   ├── cache/
│   └── view/
│       └── knowledge/
│           ├── common/
│           ├── app/
│           │   ├── lifecycle/
│           │   ├── feature/
│           │   ├── layer/
│           │   ├── component/
│           │   ├── matrix/
│           │   └── project/
│           └── reverse_ref/
│
└── .claude/ .codex/ .gemini/ .agents/
    generated harness projections
```

The numbered roots above are defaults. A host may configure another fixed set, but the set is versioned policy and cannot be inferred or silently changed by rebalancing.

### 5.2 SPipe module

```text
Spipe/
├── doc/
│   └── ...                         # SPipe project's own lifecycle docs
│
├── knowledge/
│   ├── common/
│   │   ├── doc/                    # promoted reusable knowledge
│   │   └── catalog.sdn
│   └── family/                     # optional reviewed domain families
│
├── skill_src/
│   ├── common/
│   ├── phases/
│   ├── domains/
│   ├── tools/
│   └── harness/
│       ├── claude.sdn
│       ├── codex.sdn
│       ├── gemini.sdn
│       └── agents.sdn
│
├── schema/
├── src/
├── cli/
├── mcp/
├── scripts/
└── plugin/                          # generated release projection
```

### 5.3 Logical workspace view

The complete view is exposed through MCP and optionally materialized:

```text
spipe://workspace/{workspace}/
├── common/
│   ├── doc/
│   └── skill/
│
├── app/
│   ├── doc/
│   │   ├── lifecycle/
│   │   ├── feature/
│   │   ├── layer/
│   │   ├── component/
│   │   └── matrix/
│   └── skill/
│       ├── project/
│       ├── feature/
│       ├── layer/
│       ├── component/
│       └── pair/
│
├── project/                         # linked-project view, not canonical storage
└── reverse_ref/
    ├── aspect/
    ├── trait/
    ├── interface/
    ├── type/
    ├── symbol/
    ├── requirement/
    ├── test/
    ├── config/
    ├── command/
    ├── document/
    └── section/
```

### 5.4 No canonical `doc/app/project/`

Child projects are declared in `.spipe/projects.sdn`, for example:

```sdn
workspace:
  uid: WS-01...
  root_project: simple

projects:
  - uid: P-SPIPE
    name: spipe
    relation: extends
    linkage: gitlink
    mount: .spipe/spipe
    revision_policy: pinned
    trust: executable_policy

  - uid: P-NVFS
    name: nvfs
    relation: child
    linkage: path
    mount: examples/nvfs
    revision_policy: workspace
    trust: reviewed_reference
```

A generated `project/simple/`, `project/spipe/`, or `project/nvfs/` view is permitted. Storing linked-project documents under a host-owned canonical `doc/app/project/` is not.

---

## 6. Artifact metadata, identity, and graph

### 6.1 Document metadata

Use a Markdown-safe metadata block with a stable schema:

```markdown
<!-- spipe-meta
schema: spipe-artifact/2
uid: A-01K...
key: design.gui.event_ring
kind: design
project: simple
title: GUI Event Ring
features:
  - gui
layers:
  - runtime
components:
  - event_ring
owners:
  feature: gui
  technical_kind: component
  technical: event_ring
status: accepted
visibility: project
path_policy:
  fixed: false
  public: false
-->
```

Rules:

- `uid` is immutable.
- `key`, `title`, and path are renameable.
- at least one `feature` and at least one `layer` or `component` are required for managed app feature artifacts;
- common knowledge is exempt from app-owner fields and instead carries promotion provenance;
- `path_policy.fixed=true` excludes the artifact from physical rebalancing;
- `path_policy.public=true` requires a compatibility alias/redirect policy before movement.

### 6.2 Stable sections

Referenced or trace-critical headings receive stable identity:

```markdown
## Incremental index maintenance
<!-- spipe:section uid=S-01K... key=design.index.incremental -->
```

A heading rename preserves the section UID and stores the old slug as an alias.

### 6.3 Canonical forward edges

Persist active-direction forward edges only:

```text
contains
classifies
evidence_for
derives
satisfies
realizes
schedules
specifies
implements
verifies
covers
produces
links_to
uses_aspect
implements_trait
implements_interface
configured_by
invokes
aliases
supersedes
extends
promoted_from
depends_on
mounted_as
```

Each edge stores:

- edge UID;
- source and target UIDs;
- type;
- origin;
- authority/review state;
- confidence;
- source span;
- project, worktree, revision, snapshot;
- evidence hash.

### 6.4 Reverse references

The reverse index is derived:

```text
target UID/section UID
  -> [(edge type, source UID, source span, authority, revision)...]
```

Materialized view example:

```text
reverse_ref/
└── trait/
    └── serializable/
        ├── INDEX.md
        ├── implementations.md
        ├── users.md
        ├── affected_requirements.md
        └── affected_tests.md
```

These files are generated and read-only. They are not another source of truth.

### 6.5 `spect` migration

Configuration:

```sdn
views:
  reverse_ref:
    root: reverse_ref
    legacy_aliases:
      - spect
    relation_folders:
      uses_aspect: aspect
      implements_trait: trait
      implements_interface: interface
      implements: symbol
      verifies: test
```

Migration policy:

1. release N: `reverse_ref` becomes the default; `spect` resolves as a read-only deprecated alias;
2. release N+1: use of `spect` emits a deny-by-default lint for new references and a warning for old aliases;
3. release N+2: stop materializing `spect`; retain resolver aliases for historical links according to compatibility policy.

The root and folder names are configurable, but relation semantics and UIDs are not path-derived.

---

## 7. Common knowledge and promotion

### 7.1 Scope ladder

```text
session
  -> project
  -> project family
  -> SPipe common
```

### 7.2 Promotion is not balancing

A rebalancer may move:

```text
doc/05_design/gui/event/
  -> doc/05_design/gui/runtime/event/
```

within the same fixed root.

It may not move:

```text
doc/05_design/gui/ring.md
  -> knowledge/common/doc/concurrency/ring.md
```

That is promotion and requires:

- reusable-value evidence;
- project-specificity analysis;
- source provenance and revisions;
- license and attribution checks;
- secret/private-data scanning;
- at least two independent consuming projects under normal policy;
- human/expert approval;
- validation in every consumer;
- an `extends` or override model for project-specific additions.

### 7.3 Cross-repository promotion workflow

Avoid a single non-atomic transaction across repositories.

1. The app repository creates a `PromotionCandidate`.
2. SPipe creates a separate common-knowledge PR with generalized content and provenance.
3. SPipe common PR is reviewed and merged.
4. The app PR changes the local artifact into an `extends` relation.
5. Consumer validation proves no project-specific constraint was lost.

The artifact UID in the app and the common-knowledge UID remain distinct; provenance links them with `promoted_from`.

---

## 8. Feature creation and pair-expert design

### 8.1 Feature creation command

```text
spipe feature create <feature>
  --layer <layer>...
  --component <component>...
  --acceptance <file-or-text>
  --owner <feature-expert>
```

This command creates or updates:

1. a stable `Feature` record;
2. taxonomy aliases;
3. the feature expert skill source;
4. layer/component classifications;
5. a recommended pair-expert assignment;
6. an initial trace root and acceptance criteria;
7. virtual feature/layer/component views;
8. only the lifecycle artifact required for the current phase.

It does **not** create duplicate physical `feature/`, `layer/`, and `component/` document trees and does not fill the repository with empty lifecycle files.

### 8.2 Canonical app skill sources

```text
.spipe/skill_src/
├── project/
│   └── skill.md
├── feature/
│   └── gui/
│       └── skill.md
├── layer/
│   └── runtime/
│       └── skill.md
├── component/
│   └── event_ring/
│       └── skill.md
└── pair/
    └── policy.sdn
```

Pair-session runtime state is not canonical knowledge:

```text
.spipe/state/pair/<task-uid>.sdn
```

### 8.3 Pair selection

For each managed task:

```text
feature_expert =
  owner(feature classification)

technical_expert =
  component expert, when a specialized component is primary
  else layer expert
```

Selection inputs:

- changed artifact classifications;
- source ownership;
- required invariants;
- risk profile;
- performance/security/mission-critical tags;
- current expert availability;
- conflict-of-interest policy for verification.

A task spanning multiple features still has one integration feature owner. Additional feature experts are consulted rather than producing competing ownership.

### 8.4 Pair contract

```sdn
pair_session:
  task_uid: TASK-...
  artifact_uids: [A-...]
  feature:
    key: gui
    expert: gui-feature
  technical:
    kind: component
    key: event_ring
    expert: event-ring
  responsibilities:
    feature:
      - behavior
      - acceptance
      - end_to_end_trace
      - integration
    technical:
      - interface
      - invariants
      - performance
      - concurrency
      - reuse
  joint_gates:
    - requirement_consistency
    - architecture_fit
    - link_integrity
    - score_admission
    - verification_complete
```

### 8.5 Role switching by phase

Do not force equal typing time. Pair-programming studies show productive pairs frequently switch roles, while actual driving time is often unequal. Apply role switching to expertise rather than a rigid timer.

| Phase | Primary driver | Navigator/challenger |
|---|---|---|
| Intake and requirements | Feature expert | Layer/component expert |
| Architecture boundary | Layer/component expert | Feature expert |
| Detailed behavior/spec | Feature expert | Layer/component expert |
| Interface/performance/concurrency implementation | Layer/component expert | Feature expert |
| End-to-end integration | Feature expert | Layer/component expert |
| Verification | alternate; optionally independent verifier | alternate |
| Refactor/balance review | technical expert examines structure | feature expert verifies unchanged intent |

Every phase produces one shared artifact state and one joint handoff. The navigator's accepted decisions are recorded; they are not lost in chat.

### 8.6 Pair-trigger policy

Require a pair when any of these holds:

- an artifact has both feature and layer/component classifications;
- a public interface or cross-layer edge changes;
- performance, memory, concurrency, security, or mission-critical invariants are affected;
- more than one component is changed for one feature;
- a balance move changes an ownership boundary;
- a common-knowledge candidate is being generalized.

Allow a single expert for trivial spelling, generated output refresh, or narrowly scoped metadata repair, subject to normal lint/admission.

---

## 9. Markdown parser and link model

### 9.1 Use an AST, not regular expressions

Markdown contains inline links, full/collapsed/shortcut reference links, definitions that may appear elsewhere, escaped brackets, code spans, HTML, images, and dialect-specific heading slugs. Regex-only rewriting will eventually corrupt valid content.

Baseline options:

1. use `vscode-markdown-languageservice` behind an adapter for link/reference/rename behavior; or
2. use `remark-parse`/mdast plus custom source-position-preserving rules.

The dependency-free baseline may ship a small CommonMark-compatible parser subset, but it must pass the same fixture corpus. Optional packages must not become correctness authorities unless SPipe's portability policy is revised.

**AMENDED — the conclusion stands, but both listed options are gone and the
reason has changed.** `vscode-markdown-languageservice` and `remark-parse` are
JS packages; neither is available to a Simple implementation. The decision is an
**offset-carrying link/region scanner** in `src/app/spipe/scan/`.

The reason is no longer "no new dependencies" — it is that **no
offset-preserving parser exists in either language**. `std.common.markdown` (586
lines, verified) parses blocks and inline content but records **no source byte
offsets and no link records**, and link rewriting requires exact byte ranges.
Retrofitting offsets into the stdlib parser is an API change with its own blast
radius, recorded as the preferred long-term fix. Meanwhile the stdlib parser is
a free cross-check **oracle** in tests: every link the scanner finds must appear
in the stdlib parse's inline output (existence, not offsets), catching scanner
false positives at no cost.

**A hazard this section could not have anticipated:** in Simple, `text.len()`
returns **bytes** while `s[i]` indexes **chars**, so the classic
`while i < s.len()` + `s[i]` scanner silently corrupts on non-ASCII — and doc
prose *is* non-ASCII (em-dashes, arrows, box drawing throughout `doc/`). All
`SourceRange` offsets are therefore **byte** offsets and scanning iterates bytes
consistently; char-indexed `s[i]` never appears in the scanner.

### 9.2 Parse these constructs

- ATX and Setext headings;
- inline links and images;
- full, collapsed, and shortcut reference links;
- link-reference definitions;
- autolinks;
- configured HTML `href` and `src`;
- `spipe://` logical references;
- stable artifact and section markers;
- SDN metadata blocks;
- includes/transclusions when enabled;
- code fences and code spans, which must not be rewritten as prose links.

### 9.3 Anchor profiles

Configure the renderer profile:

```sdn
markdown:
  dialect: commonmark
  anchor_profile: github
  html_links: validate
```

Supported profiles should include:

- GitHub;
- CommonMark/no implicit cross-file slug assumption;
- MkDocs;
- configurable project-specific function.

Stable section UIDs are authoritative. Slug links are compatibility serializations.

### 9.4 Source-preserving edits

The refactor engine edits exact source ranges. It must not parse and reserialize an entire Markdown file merely to change a link, because full serialization creates unrelated formatting churn.

For each rewrite, record:

```text
source file UID
source content hash
byte range
old raw target
resolved target UID/section UID
new raw target
```

Reparse after application and prove that the link resolves to the same target identity.

### 9.5 External links

External HTTP links are a different policy:

- cache by normalized URL and validator metadata;
- use bounded concurrency and timeouts;
- distinguish transient network failure from definite invalidity;
- do not make external availability a default PR blocker;
- permit a stricter release or publishing profile;
- never fetch URLs selected from untrusted content in a privileged network context without policy.

---

## 10. Link-safe human and LLM editing

### 10.1 Interaction policy

| Stage | Human | LLM/agent |
|---|---|---|
| Typing/working tree | temporary break allowed | edits occur in transaction overlay |
| Save | immediate diagnostics | validate before publishing edit |
| Structural change | editor refactor command preferred | raw move/delete rejected |
| Pre-commit | hard staged validation | hard validation |
| Pre-push | changed graph + score preview | changed graph + score preview |
| PR | authoritative admission | authoritative admission |
| Merge queue | synthetic-head full admission | same |
| Release | full linked-workspace verification | same |

### 10.2 LLM edit transaction

```text
1. pin snapshot and target UID
2. read current hash and reverse references
3. apply proposed edit to an overlay
4. parse changed files
5. rebuild affected graph and reverse index
6. run hard diagnostics
7. run affected score calculation
8. accept overlay or return structured violations
```

The agent receives exact diagnostics and repair suggestions rather than a vague failure.

### 10.3 Structural refactor transaction

```text
1. resolve artifact/section UID
2. enumerate incoming/outgoing references
3. validate current revision, path, file identity and hashes
4. calculate destination and link rewrites
5. validate fixed-root, pin, trust and collision policy
6. journal complete old and proposed state
7. stage descriptor-relative writes
8. apply moves and replacements atomically where supported
9. preserve required metadata
10. update aliases and canonical paths
11. reparse and rebuild affected graph/cache
12. verify hard invariants and semantic neutrality
13. commit receipt or roll back
```

### 10.4 Editor integration

Expose:

- find references to artifact, file, heading, section, trait, aspect, symbol, or requirement;
- rename heading;
- move document;
- rename feature/layer/component taxonomy;
- preview impact;
- apply `WorkspaceEdit` before file rename where the client supports LSP file operations;
- reject writes to generated virtual files and route the user to the canonical UID.

### 10.5 Raw filesystem changes

SPipe cannot prevent a human or unrestricted shell from changing bytes. Therefore:

1. watchers provide fast hints;
2. the staged Git diff and content hashes are authoritative;
3. raw move recovery uses:
   - stable UID;
   - exact semantic/content hash;
   - Git rename evidence;
   - bounded fingerprint similarity;
   - lexical/semantic candidates;
   - explicit review when ambiguous;
4. protected-branch PR admission is the hard organizational boundary.

Do not use Git `assume-unchanged` or `skip-worktree` as edit protection.

---

## 11. Incremental cache and watcher design

### 11.1 Cache structure

```text
.spipe/cache/doc-graph/v1/
├── manifest.sdn
├── objects/             # content-addressed parsed objects
├── files/               # path -> file record
├── folders/             # hierarchical aggregate records
├── graph/               # immutable graph segments
├── reverse/             # incoming edge index
├── score/               # score inputs/results by snapshot and scope
├── plans/               # immutable plan objects
└── snapshots/
```

Transaction journals belong under `.spipe/transactions/`, not disposable cache.

### 11.2 File record

```sdn
file_record:
  path: doc/05_design/gui/event_ring.md
  artifact_uid: A-...
  raw_hash: sha256:...
  semantic_hash: sha256:...
  parser_version: 3
  metadata_hash: sha256:...
  headings_hash: sha256:...
  outgoing_edges_hash: sha256:...
```

### 11.3 Folder record

```sdn
folder_record:
  path: doc/05_design/gui
  fixed_root: doc/05_design
  child_digest: sha256:...
  aggregate_digest: sha256:...
  direct_docs: 17
  child_dirs: 5
  max_depth: 3
  outgoing_weight_milli: 18400
  incoming_weight_milli: 22600
  semantic_entropy_milli: 284
```

The aggregate digest is computed from sorted child identities and hashes. A file change invalidates only its file record and ancestor folder records.

### 11.4 Worktrees

- committed content-addressed objects may be shared;
- dirty overlays, locks, plans, journals, views, and authorization caches are per worktree;
- a plan is bound to project UID, worktree UID, base revision, head revision, snapshot ID, and configuration hash;
- one worktree must never observe another's dirty document state.

### 11.5 Watchers are hints

**AMENDED — the substrate changed, the conclusion did not.** The Node specifics
below are no longer the implementation, but the reasoning is substrate-independent
and still binding: watcher delivery is never correctness-critical, and Git's
staged/head diff plus content hashes remain authoritative.

Node's file watcher behavior differs across platforms and can lose useful identity information after delete/recreate operations or on network/virtualized filesystems. Therefore:

- do not make watcher delivery correctness-critical;
- on missing filename, overflow, recrawl, root replacement, or clock loss, rescan the affected root;
- prefer Watchman clock IDs when available to avoid timestamp races;
- batch changes after a settle period;
- always reconcile with Git's staged/head diff and hashes before commit or admission.

---

## 12. Lint and diagnostics

### 12.1 Hard integrity checks

These reject regardless of score:

| Diagnostic | Meaning |
|---|---|
| `SPK001` | Duplicate artifact UID |
| `SPK002` | Ambiguous key or alias |
| `SPK101` | Broken artifact/file link |
| `SPK102` | Broken section/heading link |
| `SPK103` | Registered cross-project target unavailable at required revision |
| `SPK104` | Required stable section marker missing |
| `SPK301` | Required feature or technical-axis classification missing |
| `SPK302` | Conflicting classification |
| `SPK401` | Virtual path collision |
| `SPK606` | Move crosses a fixed top-level root |
| `SPK701` | Generated view or generated skill edited directly |
| `SPK702` | One commit mixes structural and semantic content changes |
| `SPK703` | Balance commit does not match its plan/hash/parent |
| `SPK704` | Balance plan is stale relative to current head |
| `SPK705` | Non-empty mandatory plan has not been applied |
| `SPK706` | Structural commit changes resolved AST semantics |
| `SPK707` | Raw deletion loses an artifact UID without accepted supersession |
| `SPK801` | Reverse-reference index differs from a clean derivation |
| `SPK802` | New reference uses deprecated `spect` path |
| `SPK901` | Required feature/technical expert pair is absent |
| `SPK902` | Pair handoff lacks feature acceptance or technical invariant review |

Before reserving new numeric codes, verify the complete diagnostic registry; rename proposed codes if a collision exists.

**AMENDED — the collision is real, and this table is wrong about five codes.**
That verification was done. `SPK704`, `SPK803`, `SPK804`, `SPK901` and `SPK902`
are **already in use by shipped code** for unrelated meanings (cursor/pin
validity, snapshot CAS conflict, stale-delta/`before_hash`) — see `graph/store.js`
and `storage/graph_snapshot_store.js`. The assignments above for those five codes
**must not be implemented as written**; take replacements from the verified-free
ranges named in the plan. A single registry file is the source of truth, with a
spec that fails on duplicates so this cannot recur. `REQ-SPKC-031` does not exist
— the requirements doc runs 001–030 — so §23.2's new IDs sit above a gap, not a
collision.

### 12.2 Score diagnostics

| Diagnostic | Meaning |
|---|---|
| `SPK601` | Directory exceeds configured size/fanout threshold |
| `SPK602` | Canonical depth exceeds threshold |
| `SPK603` | Repeated tiny sibling directories should merge |
| `SPK604` | Post-balance score below effective floor |
| `SPK605` | Balance score regresses beyond budget |
| `SPK607` | Rebalancer does not converge/idempotently stabilize |
| `SPK608` | Required change exceeds safe PR auto-balance budget |
| `SPK609` | Protected/public path creates excessive migration cost |

Score findings are explainable and point to the exact component, scope, and proposed repair.

---

## 13. Document balance score

### 13.1 Separate safety from quality

The balance score does not include broken links, security, authorization, duplicate identity, or generated-view integrity. Those are binary gates.

For each scope, calculate:

```text
BalanceScore =
    0.30 × Cohesion
  + 0.15 × TracePathAlignment
  + 0.15 × Shape
  + 0.15 × SemanticPurity
  + 0.10 × AxisCoverage
  + 0.10 × Stability
  + 0.05 × Reachability
```

Each component is an integer in `[0, 100000]` milli-points. The displayed score is `[0, 100]`.

**AMENDED — weights and units.** The revised plan keeps only a subset of these
seven components for the first slice and **renormalizes** the surviving weights;
use the plan's numbers, not the seven-way split above. Units are **int tenths**
(`824` = 82.4) end to end, rendered by dividing at the edge. Integer arithmetic
was already required for determinism; in Simple it is doubly required, because
native codegen still has an open `f64`-value `Dict.get()` miss. Every deduction
carries an SPK code and evidence — no unexplained points.

### 13.2 Components

#### Cohesion — 30%

Measures whether strong organization edges remain together below a fixed root.

Eligible edge evidence:

- accepted explicit document links;
- same component ownership;
- same feature + technical dimension;
- co-change evidence;
- high-confidence lexical similarity;
- source/test relationships when physical locality is meaningful.

Intentionally cross-lifecycle trace edges are excluded from ordinary cross-directory cut cost.

```text
Cohesion =
  100 × (1 - weighted_cut / eligible_weight)
```

#### Trace path alignment — 15%

Lifecycle roots are intentionally separate, so trace documents are not required to occupy one directory. Instead, compare their normalized suffix taxonomies and classifications.

Example of good alignment:

```text
01_research/infra/spipe/...
02_requirements/feature/spipe/...
04_architecture/infra/spipe/...
05_design/infra/spipe/...
06_spec/.../spipe/...
```

A research→requirement→design→spec chain scores well when its feature/component identity is consistently represented even though each node resides under a different fixed root.

#### Shape — 15%

Penalizes:

- excessive depth;
- excessive direct document count;
- excessive child-directory fanout;
- long single-child chains;
- repeated one-file sibling directories.

Initial defaults:

| Metric | Target | Warning | Strong candidate |
|---|---:|---:|---:|
| Depth below fixed root | 1–3 | 4 | 5+ |
| Direct docs | 6–24 | 25–32 | 48+ |
| Child dirs | 3–12 | 13–16 | 24+ |
| Tiny sibling | 3+ docs | 2 | repeated 1-doc |

These are configuration defaults, not universal truths.

#### Semantic purity — 15%

Uses normalized entropy of feature/component/topic evidence inside each folder. A folder containing unrelated topics receives a penalty; a folder split into meaningless one-file microfolders is already penalized by Shape and Stability.

#### Axis coverage — 10%

For managed app artifacts:

- feature classification present;
- at least one layer or component present;
- owner mapping resolvable;
- required pair mapping present for cross-axis work.

Common knowledge uses common taxonomy/provenance instead.

#### Stability — 10%

Penalizes:

- recent moves;
- oscillation between folders;
- repeated relabeling;
- public path churn;
- large move sets;
- movement without sufficient objective gain.

#### Reachability — 5%

Measures whether artifacts appear in expected indexes/views and have a reasonable navigation path. A truly broken reference remains a hard error, not a score deduction.

### 13.3 Scopes

Calculate and report:

- global host project;
- each touched fixed root;
- each affected subtree;
- common knowledge separately;
- each linked project separately;
- aggregate workspace view as advisory.

A high global score cannot hide a badly damaged touched root.

### 13.4 Merge thresholds

Stable default policy:

```text
target_score                    = 85.0
normal_touched_scope_floor      = 80.0
absolute_deny_floor             = 70.0
max_global_regression           = 0.5
max_touched_scope_regression    = 1.0
legacy_required_improvement     = 2.0
```

Admission rules:

1. hard diagnostics must be zero;
2. every touched scope must be at least 80 after safe auto-balance;
3. global score must not regress by more than 0.5;
4. no touched scope may regress by more than 1.0;
5. any scope below 70 rejects unconditionally;
6. a legacy scope below 80 is accepted only with an active debt record and at least 2.0 points of improvement;
7. once a scope reaches 80, it cannot return to legacy debt mode;
8. target 85 is used for warnings, optimizer stopping, and migration completion.

### 13.5 Debt records and waivers

```sdn
doc_balance_debt:
  scope: doc/04_architecture/compiler
  baseline_score_milli: 73400
  minimum_next_score_milli: 75400
  owner: compiler-architecture
  issue: DOC-184
  reason: legacy oversized tree
  expires: 2026-11-30
  max_prs: 6
```

A waiver/debt record cannot suppress:

- broken links;
- duplicate identity;
- generated-view edits;
- fixed-root crossing;
- authorization or containment failure;
- semantic changes in a structural commit;
- untrusted privileged execution.

---

## 14. Rebalancing algorithm

### 14.1 Two modes

#### PR mode — automatic and conservative

Runs on every PR and is allowed to produce/apply small physical changes.

#### Full mode — global and advisory/dedicated

Runs periodically or explicitly, using broader clustering and capable of proposing a dedicated organization PR.

Do not run a large stochastic/global partitioning rewrite inside every feature PR.

### 14.2 PR affected graph

Start with:

- changed managed documents;
- documents whose incoming links changed;
- one- and two-hop strong graph neighbors;
- must-link bundles;
- changed feature/layer/component classifications;
- ancestor folders up to the fixed root;
- sibling candidate folders;
- co-changed artifacts within a bounded history window.

All candidate construction is sparse and budgeted.

### 14.3 Candidate destinations

A PR-mode candidate may target only:

- an existing sibling/nearby directory under the same fixed root;
- an existing parent or child directory under the same fixed root;
- one new controlled-taxonomy directory when minimum-size policy is met.

It may not:

- cross a fixed root;
- move to common;
- move across trust or project boundaries;
- move a pinned/public artifact without its compatibility policy;
- split a must-link bundle;
- create a tiny directory below minimum size;
- change feature/layer/component semantics.

### 14.4 Deterministic local optimizer

```text
1. calculate current score and objective
2. enumerate candidate bundle moves
3. discard hard-invalid candidates
4. calculate exact score/objective delta
5. sort by:
     highest gain,
     highest confidence,
     lowest churn,
     UID,
     normalized destination
6. apply best candidate to an in-memory tree
7. update only affected metrics
8. repeat until:
     no qualifying move,
     move budget reached,
     time/memory budget reached
9. run a second pass and require no further change
10. emit immutable plan
```

Initial automatic acceptance:

```text
minimum score gain per move      = 2.0 points in affected scope
minimum confidence               = 0.90
maximum moved files              = 10
maximum moved fraction           = 5% of affected scope
maximum new directories          = 2
maximum iterations               = 50
minimum stable snapshots         = 2, unless the issue is deterministic shape debt
cooldown                         = 3 commits
strict trace breaks              = 0
hard violations                  = 0
```

Tune with Wave-0 history. Keep the defaults in tracked configuration.

### 14.5 Full audit optimizer

For periodic/global analysis:

1. collapse must-link bundles;
2. build a weighted graph/hypergraph;
3. find connected communities with Leiden or a capability-equivalent provider;
4. subdivide oversized communities using balanced multilevel partitioning;
5. merge undersized communities by lowest objective increase;
6. perform bounded deterministic local refinement;
7. preserve stable cluster UIDs by overlap matching;
8. apply hysteresis, cooldown, and migration cost;
9. emit a dedicated structural proposal.

Leiden is suitable for broad advisory clustering because it provides connected-community guarantees that Louvain does not. It must still be wrapped in deterministic seeding, integer weights, hard constraints, and stable tie-breaking.

### 14.6 Objective

```text
Cost(T) =
    λcut       × weighted_cross_directory_edges
  + λdepth     × depth_penalty
  + λfanout    × fanout_penalty
  + λcount     × direct_count_penalty
  + λentropy   × semantic_entropy
  + λtrace     × trace_path_misalignment
  + λambig     × naming/classification_ambiguity
  + λmove      × move_weight
  + λchurn     × recent_move_penalty
  + λpublic    × public_path_migration_cost
  - λcohesion  × within_directory_cohesion
```

The score is user-facing; this cost is the optimizer's detailed objective. The report explains how each accepted move changes both.

### 14.7 Large-plan handling

When the safe automatic budget is exceeded:

- do not partially hide a major reorganization in the feature PR;
- emit `SPK608`;
- generate a complete plan and patch;
- create or request a dedicated `docs(balance): ...` PR;
- after that structural PR merges or is applied to the feature branch, rerun admission.

Virtual feature/layer/component/reverse-reference views still rebuild automatically.

---

## 15. Commit separation policy

### 15.1 Commit classes

#### Content commit

Allowed:

- prose;
- requirements;
- design;
- code examples;
- headings, when not a structural rename operation;
- classifications when they reflect a real semantic change;
- source/test changes.

Forbidden:

- moving/renaming an existing managed UID;
- generated balance rewrites;
- changing generated views.

Example:

```text
docs(gui): define event-ring backpressure behavior
```

#### Structural commit

Allowed:

- file/directory moves and renames;
- relative link destination rewrites resolving to the same UID/section;
- canonical-path and alias registry updates;
- read-only generated manifest/checksum refresh where tracking is required;
- case-only rename staging on platforms that require an intermediate name.

Forbidden:

- changing visible prose;
- changing headings except a dedicated heading-rename transaction;
- changing code blocks;
- changing requirement meaning;
- changing feature/layer/component classification;
- adding unrelated content.

Examples:

```text
docs(move): group GUI event-ring design under runtime
docs(balance): rebalance design/gui subtree
```

#### Mixed commit

Rejected when managed artifacts are both structurally moved and semantically edited in one commit.

### 15.2 Semantic-neutrality proof

Git similarity is useful for review but is not authoritative.

For each moved UID:

1. parse parent and child versions;
2. resolve all links to target UID/section UID;
3. normalize only path-dependent metadata and equivalent link destinations;
4. retain visible text, heading text, code, classifications, and semantic metadata;
5. compare normalized AST hash.

A structural commit passes only when the semantic hash is unchanged, except for an explicitly typed heading-rename transaction whose section UID and incoming references are preserved.

Git's rename detection should run with a high review threshold such as `-M90%`, while exact UID/semantic-hash matching remains the authority. Separating moves from edits improves rename recognition and avoids Git's expensive ambiguous fallback.

### 15.3 Automatic balance commit

When a safe plan is non-empty, the writer appends:

```text
docs(balance): rebalance <scope>

SPipe-Generated: doc-balance/v1
SPipe-Source-Head: <sha-before-balance>
SPipe-Plan-SHA256: <plan-hash>
SPipe-Policy-SHA256: <policy-hash>
SPipe-Score-Before: 81.200
SPipe-Score-After: 86.700
SPipe-Moves: 4
SPipe-Link-Rewrites: 17
```

Rules:

- the commit parent must equal `SPipe-Source-Head`;
- plan and policy hashes must match;
- the writer uses expected-head compare-and-swap before push;
- the next PR event recomputes the graph;
- if the plan is then empty, admission may pass;
- if another qualifying plan appears, allow one bounded retry, then reject as non-convergent;
- a later human content commit makes the balance commit stale and triggers a new balance operation.

No empty commit is created for an empty plan.

### 15.4 Intentional move plus edit

Preferred order:

```text
1. docs(move): rename or move without semantic edit
2. docs(...): edit content at the new location
3. docs(balance): optional final automatic balance
```

For an ordinary feature change with no intentional move:

```text
1..N. content/code commits
N+1. docs(balance): generated structural commit, only when needed
```

### 15.5 Merge strategy

Commit separation is an admission/review invariant.

Preferred merge modes for structural PRs:

- rebase merge preserving commits; or
- merge commit preserving commits.

When repository policy requires squash merge, preserve the verified plan hash and balance receipt in the squash message/check provenance. The PR must still have passed commit-separation analysis before squash.

---

## 16. Pull-request state machine

```text
PR opened or synchronized
        │
        ▼
pin base SHA + head SHA + trusted policy/tool version
        │
        ▼
read-only parse/index/integrity/score
        │
        ├── hard failure ───────────────► FAIL
        │
        ▼
deterministic balance plan
        │
        ├── empty
        │     ▼
        │   commit-policy + score gate
        │     ├── pass ────────────────► ADMIT
        │     └── fail ────────────────► FAIL
        │
        └── non-empty
              │
              ├── safe + writable trusted branch
              │       ▼
              │   trusted writer recomputes plan
              │       ▼
              │   RefactorService transaction
              │       ▼
              │   push separate balance commit
              │       ▼
              │   PR synchronize event restarts
              │
              └── not writable / fork / large / ambiguous
                      ▼
                  publish patch + exact command
                      ▼
                  FAIL until author applies or
                  dedicated structural work completes
```

### 16.1 Required checks

Use three visible checks and one authoritative aggregate:

```text
SPipe Doc Integrity
SPipe Doc Balance
SPipe Commit Structure
SPipe Doc Admission
```

`SPipe Doc Admission` is required and bound to:

- latest head SHA;
- base SHA;
- policy hash;
- parser/analyzer version;
- graph snapshot;
- score report;
- balance plan or empty-plan proof;
- commit-separation result.

Configure branch rules to require the check from the expected GitHub App source.

### 16.2 Merge queue

The analysis/admission workflow must run on:

```yaml
on:
  pull_request:
  merge_group:
```

The merge-group run evaluates the synthetic combination against the latest queued base. A PR-level pass is not reused as proof for a different merge-group SHA.

### 16.3 Concurrency

```yaml
concurrency:
  group: spipe-doc-${{ github.event.pull_request.number || github.ref }}
  cancel-in-progress: true
```

The writer additionally uses head-SHA compare-and-swap. It never force-pushes.

---

## 17. Secure PR writeback

### 17.1 Trust modes

#### Same-repository trusted branch

A GitHub App may push the balance commit when:

- the branch is in the same repository;
- the app is explicitly allowed;
- the PR author/branch policy permits modification;
- the head SHA is unchanged;
- the recomputed trusted plan passes all limits.

#### Fork or untrusted branch

Default:

- run analysis automatically;
- generate a deterministic patch and command;
- do not push;
- fail admission until the author applies it.

Optional fork writeback requires an explicit repository policy and author-granted maintainer modification. Even then, the privileged writer must treat PR files only as passive data.

### 17.2 Two-plane workflow

#### Unprivileged analyzer

- event: `pull_request`;
- permissions: `contents: read`;
- no secrets;
- may execute the PR version only in an unprivileged environment;
- produces an advisory report.

#### Trusted writer/admission service

- runs trusted code pinned from the base/default branch or an immutable package digest;
- re-fetches base and head objects as data;
- does not run `npm install`, hooks, tests, or scripts from the PR;
- reparses and recomputes the plan independently;
- obtains a short-lived GitHub App token only for the exact operation;
- pushes only the generated structural commit;
- emits the authoritative required check.

Do not check out and execute fork-controlled code in a `pull_request_target` job with write credentials or secrets. Workflow artifacts derived from an untrusted run are also untrusted inputs and must be independently validated.

### 17.3 Writer allowlist

The trusted writer may invoke only internal, pinned operations:

```text
parse bytes
read Git tree/blob
calculate graph
calculate score
calculate plan
apply source-range rewrites
create Git tree/commit
update exact expected branch head
create check run
```

It may not invoke arbitrary commands found in project configuration or document content.

---

## 18. GitHub Actions sketch

Read-only workflow:

```yaml
name: SPipe document admission analysis

on:
  pull_request:
  merge_group:

permissions:
  contents: read

jobs:
  analyze:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@<pinned-sha>
        with:
          fetch-depth: 0
          persist-credentials: false

      - name: Analyze document graph and balance
        run: >
          spipe doc admission
          --base "$BASE_SHA"
          --head "$HEAD_SHA"
          --mode analyze
          --format json
          --out .spipe/out/doc-admission.json

      - uses: actions/upload-artifact@<pinned-sha>
        with:
          name: spipe-doc-admission-advisory
          path: .spipe/out/doc-admission.json
```

The authoritative writer should preferably be a GitHub App service or a separately trusted reusable workflow that does not execute PR-controlled code. Its check must be bound to the actual current head.

---

## 19. PR report

Example:

```text
SPipe Doc Admission: PASS

Head:              15d8...
Base:              b440...
Policy:            sha256:...

Hard integrity
  broken links:                  0
  broken sections:               0
  duplicate UIDs:                0
  generated-view edits:          0
  mixed structure/content:       0

Balance
  global base:                 82.4
  head before balance:         80.9
  head after balance:          86.1
  touched design root:         85.7
  touched architecture root:   86.8

Automatic plan
  moves:                          4
  link rewrites:                 17
  new directories:                1
  plan hash:              sha256:...
  structural commit:       verified

Pair coverage
  feature expert:               gui
  technical expert:     event_ring
  acceptance reviewed:          yes
  invariants reviewed:          yes
```

Failure reports include:

- exact diagnostic locations;
- score component deltas;
- proposed moves;
- blocked reason;
- whether a dedicated structure PR is required;
- exact local command:

```text
spipe doc balance --base <sha> --head HEAD --apply --commit
```

---

## 20. CLI and MCP surface

**AMENDED.** This surface assumed extending the JS `dispatcher.js` under
byte-identical legacy-output constraints. The Simple CLI is a **new
`src/app/spipe` entrypoint**; the legacy-output and `legacy_cli_perf_test.js`
constraints bind only the frozen JS package and no longer constrain new work.
The verbs below stand as the intended surface.

### 20.1 CLI

```text
spipe knowledge link [host]
spipe knowledge unlink [host]
spipe knowledge verify [host]
spipe knowledge repair [host]

spipe project register <name> <path>
spipe project verify
spipe project list

spipe doc index --changed|--staged|--all
spipe doc lint --changed|--staged|--all
spipe doc score [scope] [--base <sha>]
spipe doc balance --plan|--apply [--commit]
spipe doc admission --base <sha> --head <sha>
spipe doc reverse-ref build
spipe doc reverse-ref show <target>
spipe doc move <uid> <path>
spipe doc rename <uid> <new-key-or-title>
spipe doc rename-heading <section-uid> <heading>
spipe doc repair-links
spipe doc doctor

spipe feature create <feature> ...
spipe feature classify <artifact> ...
spipe feature view <feature>

spipe pair select <task-or-artifact>
spipe pair start <task>
spipe pair check <task>

spipe knowledge candidates
spipe knowledge promote <candidate> --scope family|common

spipe skill generate
spipe skill check
```

All support stable `--format text|sdn|json`.

### 20.2 MCP resources

```text
spipe://workspace/{workspace}/
spipe://workspace/{workspace}/common/doc/{path}
spipe://workspace/{workspace}/app/doc/feature/{path}
spipe://workspace/{workspace}/app/doc/layer/{path}
spipe://workspace/{workspace}/app/doc/component/{path}
spipe://workspace/{workspace}/reverse_ref/{kind}/{target}
spipe://project/{project}/artifact/{uid}
spipe://project/{project}/section/{uid}
```

### 20.3 MCP tools

```text
spipe_doc_list
spipe_doc_read
spipe_doc_search
spipe_doc_resolve
spipe_doc_references
spipe_doc_reverse_references
spipe_doc_diagnostics
spipe_doc_score
spipe_doc_balance_plan
spipe_doc_refactor_plan
spipe_doc_refactor_apply
spipe_feature_create_plan
spipe_pair_select
spipe_skill_check
```

Mutation tools require operation-bound authorization and dry-run by default.

---

## 21. Configuration

```sdn
spipe:
  schema: spipe-config/4
  module:
    resolution:
      - explicit
      - package
      - .spipe/spipe
    require_pinned_revision_for_executable_policy: true

docs:
  canonical_root: doc
  fixed_roots:
    - 00_llm_process
    - 01_research
    - 02_requirements
    - 03_plan
    - 04_architecture
    - 05_design
    - 06_spec
    - 07_guide
    - 08_tracking
    - 09_report
    - 10_metrics
  managed_extensions: [.md, .sdn, .spl]
  generated_view_root: .spipe/view/knowledge
  generated_views_tracked: false
  default_anchor_profile: github

views:
  app:
    feature: app/doc/feature
    layer: app/doc/layer
    component: app/doc/component
    matrix: app/doc/matrix
    project: project
  reverse_ref:
    root: reverse_ref
    legacy_aliases: [spect]
    kinds:
      - aspect
      - trait
      - interface
      - type
      - symbol
      - requirement
      - test
      - config
      - command
      - document
      - section

balance:
  mode: pr_auto_small
  target_score_milli: 85000
  touched_scope_floor_milli: 80000
  absolute_deny_floor_milli: 70000
  max_global_regression_milli: 500
  max_scope_regression_milli: 1000
  legacy_required_gain_milli: 2000

  auto:
    min_move_gain_milli: 2000
    min_confidence_milli: 900
    max_files: 10
    max_scope_fraction_milli: 50
    max_new_directories: 2
    max_iterations: 50
    stable_snapshots: 2
    cooldown_commits: 3

  constraints:
    cross_fixed_root_moves: deny
    cross_project_moves: deny
    common_promotion: deny
    generated_view_writes: deny
    preserve_must_link: true
    preserve_public_paths: true

admission:
  require_balance_analysis_every_pr: true
  require_balance_commit_when_plan_nonempty: true
  require_separate_structure_commits: true
  require_latest_head_binding: true
  require_expected_check_app: true
  allow_fork_writeback: false
  large_plan_policy: dedicated_structure_work

pair:
  required_for_cross_axis: true
  prefer_component_over_layer_when_specialized: true
  require_joint_acceptance: true
  require_joint_invariants: true

cache:
  root: .spipe/cache/doc-graph/v1
  per_worktree_overlay: true
  shared_committed_objects: true
  watcher: auto
  authoritative_reconciliation: git_hash
```

---

## 22. Standalone SPipe repository refactor

### 22.1 Target source structure

**AMENDED — this is a JS tree and is no longer the target.** The canonical
implementation lives in **this** repo at `src/app/spipe/` as `.spl`, alongside
its existing siblings `spipe_docgen`, `spipe_knowledge_provider` and
`spipe_process_harness`; specs go to `test/01_unit/app/spipe/*_spec.spl`. The
npm package becomes a distribution/legacy shell, not the home. The layout below
survives only as a **namespace sketch** — read it for module decomposition, not
for file extensions or location. Simple rules apply: no inheritance
(composition, traits, mixins), generics `<>`, `Result<T,E>` + `?` rather than
try/catch, and no collection mutation through a temporary alias.

```text
src/
├── application/
│   └── knowledge_compiler.js
├── model/
│   ├── identity.js
│   ├── artifact.js
│   ├── section.js
│   ├── edge.js
│   ├── diagnostic.js
│   ├── snapshot.js
│   ├── balance_plan.js
│   └── admission_report.js
├── parser/
│   ├── markdown.js
│   ├── markdown_links.js
│   ├── markdown_sections.js
│   ├── sdn.js
│   ├── sspec.js
│   └── source_metadata.js
├── workspace/
│   ├── registry.js
│   ├── linked_project.js
│   ├── git.js
│   └── worktree.js
├── storage/
│   ├── object_store.js
│   ├── snapshot_store.js
│   ├── alias_store.js
│   ├── folder_cache.js
│   └── transaction_store.js
├── graph/
│   ├── store.js
│   ├── delta.js
│   ├── query.js
│   ├── trace.js
│   └── reverse_index.js
├── view/
│   ├── projection.js
│   ├── feature.js
│   ├── layer.js
│   ├── component.js
│   ├── matrix.js
│   ├── project.js
│   ├── reverse_ref.js
│   └── materialize.js
├── diagnostics/
│   ├── identity.js
│   ├── links.js
│   ├── sections.js
│   ├── classification.js
│   ├── generated.js
│   ├── commit_policy.js
│   ├── tree.js
│   └── admission.js
├── refactor/
│   ├── planner.js
│   ├── source_edits.js
│   ├── executor.js
│   ├── recovery.js
│   └── rollback.js
├── balance/
│   ├── metrics.js
│   ├── score.js
│   ├── affected_graph.js
│   ├── candidates.js
│   ├── local_optimizer.js
│   ├── full_provider.js
│   ├── proposal.js
│   └── commit.js
├── admission/
│   ├── service.js
│   ├── commit_classifier.js
│   ├── trust_mode.js
│   ├── check_receipt.js
│   └── github_writer.js
├── feature/
│   ├── registry.js
│   ├── create.js
│   └── classify.js
├── pair/
│   ├── selector.js
│   ├── contract.js
│   └── check.js
├── promote/
└── skill/
    ├── compiler.js
    ├── manifest.js
    └── adapters.js
```

### 22.2 CLI and MCP

**AMENDED — these are the frozen JS package's files.** Read the split below as
the intended shape (thin dispatchers over a shared core), then build it in
`src/app/spipe/` as `.spl`. The plan deliberately keeps the first slice off the
shared dispatch table so the parallel packages stay independent.

Make:

```text
cli/spipe.js
mcp/server.js
```

thin dispatchers. Add:

```text
src/cli/doc_commands.js
src/cli/feature_commands.js
src/cli/pair_commands.js
mcp/protocol/knowledge_resources.js
mcp/protocol/knowledge_tools.js
```

### 22.3 Canonical skill compiler

Replace hand-maintained equivalent payloads with:

```text
skill_src/ -> generated .claude/.codex/.gemini/.agents/plugin
```

Each generated file contains:

- source UID;
- source snapshot;
- generator ID/version;
- trust scope;
- authorization scope;
- content hash.

`spipe skill check` regenerates in memory and verifies:

- complete manifest;
- no stale output;
- no extra undeclared output;
- byte equality where syntax is canonical;
- semantic equivalence across harness adapters.

### 22.4 Plugin projection

`plugin/` is a release projection, not a second source repository.

Replace current direct duplicate ownership and `cmp` maintenance with:

```text
spipe package generate
spipe package check
```

The release build generates the plugin tree into a staging directory, verifies it, then packages it. The tracked plugin tree may be retained temporarily for compatibility, but edits to it are rejected.

### 22.5 Setup links

Refactor shell and PowerShell scripts into thin wrappers around one cross-platform CLI implementation:

```text
scripts/setup-spipe-links.sh
scripts/setup-spipe-links.ps1
  -> spipe knowledge link
```

Retain:

- dry-run;
- force with explicit policy;
- containment checks;
- idempotency;
- Unix symlink and Windows junction compatibility;
- configurable host root and document root;
- legacy `subproject_links.sdn` import.

Add:

- `.spipe/projects.sdn`;
- logical mount verification;
- alias repair;
- generated-view root creation;
- no-follow/path-escape checks;
- `spipe knowledge verify/repair`.

---

## 23. Amendments to existing Knowledge Compiler documents

The existing documents should be revised in place.

### 23.1 Research amendment

Revise the physical balancing decision:

Old direction:

```text
physical trees receive proposals and require explicit apply
```

Final direction:

```text
physical PR trees receive deterministic safe-small plans;
trusted writable PRs auto-apply those plans as a separate structural commit;
large, ambiguous, public, cross-root, cross-project, or high-churn plans remain
explicit dedicated structural work.
```

Retain full/global Leiden analysis as advisory/dedicated, not a per-PR auto-writer.

### 23.2 Requirement amendment

Revise `REQ-SPKC-022` to require:

- balance analysis on every PR;
- automatic safe-small same-root rebalancing;
- separate structure commit;
- low-score rejection;
- large-plan escalation.

Add requirements after the currently allocated range, verifying exact numbering first:

#### `REQ-SPKC-032 — Document integrity admission`

Every managed PR must pass deterministic identity, link, section, reverse-index, generated-view, fixed-root, and transaction-integrity checks bound to the latest head.

#### `REQ-SPKC-033 — Separate structural and semantic commits`

Managed artifact moves/renames and semantic edits must be isolated into different commits. Structural commits must preserve UID-resolved AST semantics.

#### `REQ-SPKC-034 — PR auto-balance and trusted writeback`

Every PR must calculate a balance plan. Safe-small plans must be automatically applied when a trusted writer has branch authority; otherwise a deterministic patch must be produced and admission must remain blocked.

#### `REQ-SPKC-035 — Balance score, floors, ratchet, and debt`

The system must expose deterministic component scores, reject below configured floors, prevent regression, and bound/expire legacy debt. Hard integrity may not be waived through score.

#### `REQ-SPKC-036 — Configurable reverse references`

Reverse-reference projections must be generated from forward edges, default to `reverse_ref`, support configurable relation folders, and migrate `spect` through a deprecated compatibility alias.

#### `REQ-SPKC-037 — Feature/technical expert pairing`

Cross-axis feature work must select a feature expert and a layer or component expert, record their responsibility split, and require joint acceptance/invariant completion.

#### `REQ-SPKC-038 — Privileged PR isolation`

A privileged writer must use trusted pinned code, treat PR content as passive untrusted data, bind writes/checks to exact head, and never execute PR-controlled code with secrets or write authority.

### 23.3 Architecture amendment

Add:

```text
DocAdmissionService
BalanceApplyCoordinator
CommitPolicyService
PairExpertService
FeatureService
ReverseReferenceService
```

Preserve:

```text
RebalanceService -> proposal only
RefactorService -> sole canonical writer
KnowledgeCompiler -> sole snapshot publisher
```

### 23.4 Design amendment

Add normative sections for:

- balance score formulas;
- PR affected-graph optimizer;
- commit semantic-hash classifier;
- PR state machine;
- same-repo and fork trust modes;
- GitHub App check receipt;
- score debt and waiver schemas;
- reverse-reference migration;
- feature creation and pair session;
- separate bot commit contract.

### 23.5 Specification amendment

Replace the current unreleased-command expectation when the feature is admitted.

Add executable scenarios for:

1. broken file link rejects;
2. broken section link rejects;
3. generated view edit rejects;
4. fixed-root crossing rejects;
5. safe same-root plan is deterministic;
6. safe writable PR receives a separate balance commit;
7. balance commit contains only structural-equivalent changes;
8. mixed content/move commit rejects;
9. stale plan/head rejects;
10. repeated run is idempotent;
11. low post-balance score rejects;
12. legacy debt requires improvement and expiry;
13. fork PR receives patch but no privileged write;
14. merge-group head is independently evaluated;
15. reverse_ref equals clean graph derivation;
16. `spect` compatibility and deprecation work;
17. feature/layer pair selection is deterministic;
18. cache corruption falls back to clean rebuild;
19. watcher event loss is recovered by Git/hash reconciliation;
20. Windows case-only rename and junction containment are safe.

---

## 24. Implementation plan

### Wave 0 — Baseline and decision lock

Deliver:

- snapshot current standalone CLI/MCP/setup/build outputs;
- inventory duplicate canonical/projection files;
- compare standalone SPipe and `simple/examples/05_stdlib/spipe`;
- inventory all current diagnostics and requirement IDs;
- baseline document graph, links, tree shape, and score;
- create representative PR histories and linked-worktree fixtures;
- record startup, full scan, incremental scan, max RSS, and package size.

Gate:

- no behavior ambiguity;
- canonical owner chosen per file;
- no requirement/diagnostic ID collision;
- migration rollback point recorded.

### Wave 1 — Consolidate implementation ownership

Deliver:

- move the usable modular knowledge core from the Simple example into standalone SPipe;
- integrate standalone release/review features;
- make CLI/MCP thin dispatchers;
- retain all existing commands and setup behavior;
- replace the writable embedded copy with a package/submodule/generated fixture.

Gate:

- standalone tests pass;
- Simple host tests pass against canonical Spipe;
- no independently versioned writable duplicate remains;
- no new mandatory runtime dependency.

### Wave 2 — Canonical skill and plugin projections

Deliver:

- `skill_src/common`, phases, domains, tools, harness adapters;
- app skill source schema;
- deterministic skill compiler;
- generated plugin/harness manifests;
- `skill check` and package projection check;
- direct generated-output edit lint.

Gate:

- every current Claude/Codex/Gemini/plugin surface maps to one source UID;
- semantic-equivalence fixtures pass;
- old `cmp` source ownership is removed or compatibility-only.

### Wave 3 — Markdown graph, UIDs, reverse references, and cache

Deliver:

- AST parser and source spans;
- artifact/section metadata;
- forward edge extraction;
- reverse incoming-edge index;
- hierarchical content-addressed cache;
- worktree overlay;
- full/incremental parity;
- `reverse_ref` view and `spect` alias.

Gate:

- clean and incremental graph roots match;
- all current links are inventoried;
- reverse index clean rebuild matches cache;
- watcher loss cannot cause a false pass.

### Wave 4 — Link-safe refactoring

Deliver:

- document move;
- heading rename;
- feature/layer/component rename;
- link-source-range rewrites;
- aliases;
- journal/apply/recovery/rollback;
- editor/LSP adapter;
- LLM transaction overlay;
- pre-commit integration.

Gate:

- fault injection at every phase yields old state, new valid state, or explicit recoverable failure;
- accepted edges and UIDs survive;
- no approved refactor can create a broken link.

### Wave 5 — Common/app logical views and link setup

Deliver:

- workspace registry;
- logical common/app/project mounts;
- feature/layer/component/matrix views;
- refactored setup wrappers;
- Unix/Windows safe link creation;
- `knowledge verify/repair`;
- remove the conceptual `doc/app/project` dependency.

Gate:

- SPipe works from package, submodule, and explicit path;
- linked projects resolve by UID/revision;
- missing linked project never resolves by accidental local name;
- all generated views are read-only.

### Wave 6 — Feature creation and pair experts

Deliver:

- feature registry and `feature create`;
- feature/layer/component skill sources;
- pair selector and pair-session schema;
- joint acceptance/invariant checks;
- phase role-switch rules;
- feature and technical expert virtual views.

Gate:

- representative GUI, compiler, and NVMe tasks select the expected pair;
- one canonical artifact is shared;
- missing pair coverage is diagnosable;
- trivial-change exemption is bounded.

### Wave 7 — Score engine and advisory balance

Deliver:

- all seven score components;
- per-root/subtree/global reports;
- score explanations;
- debt/waiver schema;
- historical calibration;
- affected graph;
- deterministic candidate generator;
- plan-only CLI.

Gate:

- score is reproducible on Linux and Windows;
- accepted historical organization decisions score better than rejected alternatives on calibration fixtures;
- no hard error is hidden in score;
- reviewers can explain every point change.

### Wave 8 — Automatic local PR rebalancing

Deliver:

- local optimizer;
- safe-small limits;
- semantic-neutral structural commit classifier;
- commit generator and trailers;
- idempotence/non-convergence protection;
- local `--apply --commit`;
- pre-push integration.

Gate:

- repeated runs are no-op;
- no fixed-root or common promotion;
- structural commit has unchanged semantic hashes;
- every accepted move produces positive bounded gain;
- large plans escalate.

### Wave 9 — GitHub admission and writer

Deliver:

- read-only PR/merge-group workflow;
- trusted GitHub App writer;
- expected-head compare-and-swap;
- same-repo auto-push;
- fork patch-only default;
- required checks;
- branch/ruleset configuration guide;
- report/comment rendering.

Gate:

- no privileged job executes PR code;
- stale head cannot be updated or admitted;
- required check is bound to latest head and expected app;
- merge queue works;
- malicious fork fixtures cannot read secrets or write refs.

### Wave 10 — Full rebalancing and dedicated structure PRs

Deliver:

- full sparse graph;
- Leiden-capable provider;
- balanced partitioning;
- constrained local refinement;
- cluster stability;
- dedicated structure PR generation;
- nightly/weekly audit.

Gate:

- connected communities;
- hard constraints preserved;
- no oscillation;
- large changes are reviewable and reversible;
- feature PRs are not polluted by global reorganizations.

### Wave 11 — Common promotion

Deliver:

- candidate discovery;
- provenance/conflict/security/license scans;
- review workflow;
- common catalog;
- project `extends` and overrides;
- consumer validation.

Gate:

- no automatic promotion;
- no secret/license/visibility violation;
- all consumers pass;
- local constraints survive.

### Wave 12 — Compatibility retirement

Deliver:

- stop materializing `spect`;
- remove old hand-maintained plugin/doc mirrors;
- remove deprecated CLI path assumptions;
- convert build equality checks to generator/admission checks;
- publish migration report.

Gate:

- no active consumer depends on removed paths;
- aliases cover historical references as configured;
- package, submodule, and host fixtures pass cleanly.

---

## 25. Parallel implementation ownership

**AMENDED — superseded.** This nine-workstream table assumed the JS tree. The
live ownership map is §4 of the plan of record: five packages (S1-A links +
reverse index, S1-B move transaction + journal, S1-C balance score, S1-D
diagnostics registry + admission verdict + CLI, S1-E record model + identity),
with no two touching the same file and S1-E's `model/types.spl` landing first so
the others import the frozen types rather than forking them. Use that map.

| Workstream | Owns | Must not edit concurrently |
|---|---|---|
| A — core/model/storage | identities, snapshots, cache, schemas | balance algorithms |
| B — parser/link/refactor | Markdown AST, source edits, transactions | skill adapters |
| C — graph/reverse/views | graph, incoming index, projections | canonical mutation executor |
| D — score/rebalance | metrics, optimizer, proposals | graph schema |
| E — admission/GitHub | commit policy, checks, writer | PR-controlled implementation |
| F — feature/pair | feature registry, expert skills, pair state | common promotion |
| G — skill/package | canonical skills, harness/plugin generator | generated outputs by hand |
| H — verification/security/performance | fixtures, fault injection, benchmarks | product code except test hooks |
| I — Simple provider integration | search/source/DB acceleration | SPipe correctness authority |

Shared schema changes are integrated first. Parallel work begins only after port and record names are frozen.

---

## 26. Test strategy

### 26.1 Unit tests

- CommonMark links and reference definitions;
- escaped/nested brackets;
- code spans/fences excluded from rewrites;
- GitHub/non-ASCII/duplicate heading slugs;
- UID and alias resolution;
- section marker preservation;
- reverse-edge derivation;
- each score component;
- deterministic tie-breaking;
- move candidate constraints;
- semantic AST normalization;
- commit classification;
- debt and threshold calculation;
- pair selection.

### 26.2 Property/metamorphic tests

- move then inverse move restores graph and bytes except journal metadata;
- rename heading preserves section UID and incoming references;
- clean rebuild equals arbitrary incremental sequence;
- generated view is byte-identical on repeated generation;
- balance run twice yields an empty second plan;
- accepted move never lowers its declared affected score;
- candidate order permutation does not change the plan;
- unrelated artifact addition does not change exact identity resolution;
- watcher omission followed by reconciliation matches clean scan;
- structural commit preserves semantic hash.

### 26.3 Transaction fault injection

Inject failure before/after:

- journal durable write;
- staging;
- first rewrite;
- file move;
- link rewrite;
- directory sync;
- graph publication;
- score verification;
- commit receipt;
- rollback step.

No injected failure may be reported as success.

### 26.4 Platform tests

- Linux/macOS inode replacement;
- Windows case-insensitive and case-only rename;
- CRLF/LF normalization;
- Unicode NFC/NFD paths;
- symlink/junction ancestor escape;
- network/virtualized filesystem watcher loss;
- cross-device move rejection or explicit copy protocol;
- file permission/metadata preservation.

### 26.5 PR security tests

- malicious `package.json`/workflow/script in fork is never executed by writer;
- artifact report contains hostile paths/commands but is treated as data;
- stale SHA race;
- branch force-update attempt;
- plan substitution;
- replayed apply token;
- maintainer-edit disabled fork;
- merge-group recomputation;
- unexpected status-check source;
- untrusted Markdown pretending to be policy.

### 26.6 Balance fixtures

- oversized clear-cluster directory;
- deep single-child tree;
- many one-file siblings;
- cross-cutting feature;
- protected public path;
- must-link bundle;
- conflicting cannot-link;
- recently moved artifact;
- low-score legacy root;
- plan exceeding PR budget;
- two equivalent candidate destinations requiring UID tie-break.

### 26.7 Performance gates

After Wave 0 sets hardware-specific absolute values:

- no-op legacy CLI commands regress by no more than 10%;
- one-file warm incremental analysis is at least 20× cheaper than full rebuild on the benchmark corpus;
- PR affected graph does not become an all-project all-pairs comparison;
- plan generation is bounded by configured time, memory, node, and edge limits;
- changed view materialization rewrites only changed files;
- cache corruption is detected and rebuilt;
- external semantic providers are optional and failure degrades to lexical/graph operation.

---

## 27. Pull-request acceptance matrix

| Case | Analyze | Auto-write | Admission |
|---|---:|---:|---|
| No managed change; plan empty | yes | no | pass if global checks pass |
| Managed edit; plan empty; score pass | yes | no | pass |
| Safe small plan; same-repo writable | yes | separate balance commit | rerun then pass |
| Safe small plan; fork/default policy | yes | patch only | fail until applied |
| Plan exceeds move budget | yes | no | fail; dedicated structural work |
| Score remains below floor | yes | no | fail |
| Legacy score below floor + valid debt + required gain | yes | bounded | pass while debt valid |
| Broken link/section | yes | no | fail regardless of score |
| Mixed move/content commit | yes | no | fail |
| Generated view edited | yes | no | fail |
| Fixed-root crossing | yes | no | fail |
| Stale plan/head | yes | no | fail and recompute |
| Merge-group SHA differs | yes | no direct branch write | evaluate synthetic head |
| Common promotion disguised as balance | yes | no | fail; promotion workflow |

---

## 28. Operational rollout

### Stage A — Observe

- report links, identities, reverse references, and score;
- no canonical writes;
- no merge rejection except existing hard failures.

### Stage B — Integrity gate

- reject newly broken links, duplicate UIDs, generated edits, and fixed-root crossing;
- keep balance advisory.

### Stage C — Commit separation gate

- reject mixed structure/content commits;
- provide local refactor commands.

### Stage D — Score ratchet

- add debt records for existing low roots;
- require no regression and measured improvement;
- publish target/floor dashboard.

### Stage E — Auto-balance dry run

- calculate every PR;
- publish exact prospective structural commit;
- measure acceptance and false positives.

### Stage F — Trusted same-repo auto-write

- enable safe-small writer;
- fork remains patch-only;
- make admission check required.

### Stage G — Floor enforcement

- normal touched-scope floor 80;
- target 85;
- expire debt progressively.

### Stage H — Full audit and common promotion

- enable dedicated global balance PRs;
- begin reviewed common-knowledge promotion;
- retire old aliases/mirrors after compatibility window.

At each stage, retain an emergency switch that disables physical auto-write while keeping integrity analysis and required checks active.

---

## 29. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Optimizer creates noisy churn | safe-small budget, migration cost, cooldown, idempotence, dedicated large PR |
| Score is gamed | separate hard gates; multiple explainable components; historical calibration; review acceptance metrics |
| One score hides local damage | per-touched-root and subtree floors |
| Bot loops on its own commit | plan/head trailers, deterministic second-pass no-op requirement, bounded retry |
| Fork automation exposes secrets | read-only analysis; trusted writer never executes PR code; patch-only default |
| Markdown rewrite damages formatting | AST/source ranges; no whole-document serialization |
| Watcher misses changes | Git/hash reconciliation is authoritative |
| Git rename detection is ambiguous | UID and semantic hash first; separate structural commit |
| Common becomes a dumping ground | reviewed promotion, provenance, multi-project evidence, no auto promotion |
| Experts become bottlenecks | temporary task pairing, role switching, explicit scope, reusable common knowledge |
| Generated skill drift | one skill source, deterministic generator, semantic-equivalence checks |
| Standalone/example drift | one canonical Spipe implementation and generated/test fixture |
| Large legacy tree cannot meet floor | expiring debt record, ratchet, dedicated balance PR |
| Public links break after move | stable UID, aliases, redirects, public-path cost/pin |
| Cross-platform path behavior differs | normalized POSIX canonical paths plus platform safe-filesystem adapters |

---

## 30. Definition of done

The feature is complete only when:

1. standalone Spipe is the canonical implementation;
2. host repositories can mount/install it without layout assumptions;
3. common and app knowledge/skill views are available;
4. feature/layer/component/project/reverse-reference views are generated and read-only;
5. `reverse_ref` is configurable and `spect` migration is implemented;
6. artifacts and referenced sections have stable identity;
7. link and heading rename/move operations are transactional;
8. LLM writes reject invalid graph results;
9. staged commits reject broken links and mixed structural/content changes;
10. every PR receives a deterministic balance report;
11. safe-small same-repo plans produce a separate structural commit;
12. forks are analyzed automatically without privileged execution;
13. low score and unapplied mandatory plans reject;
14. merge queue evaluates the synthetic head;
15. pair experts are selected and jointly validate cross-axis feature work;
16. generated harness/plugin skills derive from one canonical source;
17. full/incremental graph, reverse index, views, and score are equivalent;
18. rebalancing is idempotent and cannot cross fixed roots;
19. large reorganization is isolated in dedicated structural work;
20. common promotion is reviewed, provenance-preserving, and consumer-validated.

---

## 31. Research basis

### Repository sources reviewed

- `ormastes/Spipe`
  - `doc/00_llm_process/`
  - `doc/00_llm_process/template/feature_skill.md`
  - `doc/00_llm_process/project_expert/README.md`
  - `scripts/setup-spipe-links.sh`
  - `cli/spipe.js`
  - `mcp/protocol/resources.js`
  - `scripts/build.sh`
  - `.github/workflows/build.yml`
  - `plugin/manifest.sdn`
- `ormastes/simple`
  - `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`
  - `doc/02_requirements/feature/spipe_knowledge_compiler.md`
  - `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md`
  - `doc/05_design/infra/spipe/spipe_knowledge_compiler.md`
  - `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md`
  - `doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md`
  - `examples/05_stdlib/spipe/`

### External references

1. VS Code Markdown Language Service — reference finding, rename, diagnostics, and link updates on file moves:
   https://github.com/microsoft/vscode-markdown-languageservice
2. VS Code Markdown language server:
   https://github.com/microsoft/vscode-markdown-languageserver
3. CommonMark specification — Markdown links and reference-definition grammar:
   https://spec.commonmark.org/spec
4. remark-lint/unified/mdast — AST-based Markdown linting model:
   https://github.com/remarkjs/remark-lint
5. Language Server Protocol file operations — pre/post rename workspace edits:
   https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/
6. Git rename detection and similarity thresholds:
   https://git-scm.com/docs/git-diff
7. GitHub required checks, expected check source, and merge queues:
   https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/available-rules-for-rulesets
   https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/incorporating-changes-from-a-pull-request/troubleshooting-required-status-checks
8. GitHub secure use of `pull_request_target`:
   https://docs.github.com/en/actions/reference/security/securely-using-pull_request_target
9. GitHub Security Lab, preventing "pwn request" workflow vulnerabilities:
   https://securitylab.github.com/resources/github-actions-preventing-pwn-requests/
10. Node.js filesystem watcher caveats:
    https://nodejs.org/api/fs.html
11. Watchman clock specifications and triggers:
    https://facebook.github.io/watchman/docs/clockspec
    https://facebook.github.io/watchman/docs/cmd/trigger.html
12. Traag, Waltman, and van Eck, "From Louvain to Leiden: guaranteeing well-connected communities," *Scientific Reports* 9, 5233 (2019):
    https://doi.org/10.1038/s41598-019-41695-z
13. Plonka et al., "Collaboration in Pair Programming: Driving and Switching," XP 2011:
    https://doi.org/10.1007/978-3-642-20677-1_4
14. Jones and Fleming, "What use is a backseat driver? A qualitative investigation of pair programming," VL/HCC 2013:
    https://doi.org/10.1109/VLHCC.2013.6645252
15. Sablis, Smite, and Moe, "Team-external coordination in large-scale software development projects," *Journal of Software: Evolution and Process* 33 (2021):
    https://doi.org/10.1002/smr.2297
16. Team Topologies summary of stream-aligned and complicated-subsystem collaboration:
    https://www.atlassian.com/devops/frameworks/team-topologies

---

## 32. Final recommendation

Implement **automatic analysis on every PR** and **automatic physical writeback only for safe-small, deterministic, authorized plans**. Require a separate structural commit whenever the plan is non-empty, and reject the PR when:

- any hard link/identity/transaction invariant fails;
- the structural commit changes semantics;
- the balance plan is stale or unapplied;
- the post-balance touched-scope score remains below policy;
- the required reorganization is too large to review safely inside the feature PR.

This achieves continuous documentation hygiene without turning each feature PR into an opaque global tree rewrite. It also preserves the strongest parts of the existing Knowledge Compiler design: immutable identity, one canonical content copy, MDSOC ownership, transactional mutation, generated multidimensional views, reviewed common promotion, and independent SPipe portability.
