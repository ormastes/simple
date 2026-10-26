# Simple Traceability, SDN Evidence, Fast Admission Gates, and Slop Viewer

## Final research, architecture, detailed design, and implementation plan

**Date:** 2026-10-03  
**Repository:** `ormastes/simple`  
**Audited source revision:** `02f6687d846ba55faea4a08c44e4a3c0982a488d`  
**Status:** Proposed implementation baseline; not a claim that the proposed commands or components are implemented.  
**Intended repository destination:** `doc/09_report/simple_traceability_sdn_slop_final_2026-10-03.md`

> **Decision:** Use one typed, incrementally derived trace graph. Keep authored intent and exceptional links in SDN, derive unambiguous structural links from conventions, attach immutable evidence to actual test executions, and make checking, generated Markdown/HTML, and **slop viewer** consume the same graph. **SDN is the only Simple-owned structured interchange and persistence format in this design. There is no JSON output mode or JSON fallback.**

## Contents

1. [Executive decisions](#1-executive-decisions)
2. [Verified baseline and corrections](#2-verified-baseline-and-corrections)
3. [Research and resulting decisions](#3-research-and-resulting-decisions)
4. [Requirements and non-goals](#4-requirements-and-non-goals)
5. [Architecture and ownership](#5-architecture-and-ownership)
6. [Trace semantics and identity](#6-trace-semantics-and-identity)
7. [Convention-first links and explicit exceptions](#7-convention-first-links-and-explicit-exceptions)
8. [SDN contracts and serialization](#8-sdn-contracts-and-serialization)
9. [Text database evolution and update transactions](#9-text-database-evolution-and-update-transactions)
10. [Incremental graph construction and invalidation](#10-incremental-graph-construction-and-invalidation)
11. [Minimum local commit and push gates](#11-minimum-local-commit-and-push-gates)
12. [Remote admission and full audit](#12-remote-admission-and-full-audit)
13. [Test execution, evidence, and feature completion](#13-test-execution-evidence-and-feature-completion)
14. [Generated traceability Markdown](#14-generated-traceability-markdown)
15. [Static HTML publication](#15-static-html-publication)
16. [Slop viewer interaction design](#16-slop-viewer-interaction-design)
17. [Slop implementation and SDN protocol](#17-slop-implementation-and-sdn-protocol)
18. [Proposed command contracts](#18-proposed-command-contracts)
19. [Performance and resource contracts](#19-performance-and-resource-contracts)
20. [Diagnostics, baseline debt, and exceptions](#20-diagnostics-baseline-debt-and-exceptions)
21. [Implementation work packages](#21-implementation-work-packages)
22. [Verification and acceptance matrix](#22-verification-and-acceptance-matrix)
23. [Rollout, risks, and completion criteria](#23-rollout-risks-and-completion-criteria)
24. [Source register](#24-source-register)

---

# 1. Executive decisions

| Decision | Required behavior |
|---|---|
| One semantic model | `traceability-check`, tracking validation, SSpec reporting, Markdown/HTML generation, and Slop query the same typed graph. |
| SDN only | Native configuration, DB records, graph snapshots/deltas, diagnostics, run manifests, receipts, and Slop messages use SDN. |
| Minimal authored metadata | Do not store a deterministic source-to-unit-test path or generated-document mirror in every feature row. |
| No semantic guessing | A conventional filename establishes a structural association, not proof that a requirement is tested or a symbol executed. |
| Explicit irregular links | Nonstandard, shared, many-to-many, overridden, and suppressed mappings are declared once with provenance. |
| Short hooks | Validate exact staged/pushed content; use changed artifacts, reverse dependencies, and cached facts. No full test/build/doc-generation sweep inside a hook. |
| Existing gate ownership | Extend the existing must-check registry and dispatcher; preserve conflict/tree-integrity, secret, and installation checks. |
| Independent remote authority | A local receipt never substitutes for remote validation merely because it exists. Gate code and policy must be trusted independently of candidate changes. |
| Truthful test reporting | `linked`, `not_run`, `pass`, `fail`, `incomplete`, and `stale` are different states. Acceptance-only execution does not imply unit/integration/component execution. |
| Two document classes | Stable structural trace pages and immutable run-specific evidence reports are separate products. |
| MDSOC-aware Slop | Left navigation tree; upper-right left-to-right trace or architecture layers; lower-right attributes, relations, evidence, and revision-pinned source. |
| Future-compatible DB | Reuse current test/tracking ownership and preserve the SCV/SJ direction; do not wait for the distributed DB design to be implemented. |

The primary **reading order** is:

```text
Feature -> Requirement -> Acceptance criterion / acceptance SSpec
        -> Unit / Integration / Component verification -> Implementation
```

Research, architecture, design, plans, bugs, and decisions are attached branches. This visual order is not a license to invent edges between every node in adjacent columns.

---

# 2. Verified baseline and corrections

## 2.1 Audit method and boundaries

The repository was inspected through the connected GitHub interface. Current branch metadata resolved to the revision above; key source files were then read at that immutable revision. Search results sometimes referenced its parent, `4f626ae778bc52c63d66af8013e6bb466644d865`; those results were used for discovery, not as proof of a newer implementation. Remote rulesets were read separately because repository settings are not versioned in the source tree. [R01] [R11]

This was a source/configuration review, **not a fresh execution of Simple, its tests, its hooks, or its viewer**. Timing values later in the report are proposed acceptance targets. Historical reports and comments are not treated as current passing test evidence.

## 2.2 Findings that materially affect this design

| ID | Verified finding | Consequence |
|---|---|---|
| F01 | `config/traceability.sdn` has the main source warning roots commented out. | Source-to-test enforcement is opt-in, not a repository-wide invariant. [R02] |
| F02 | The trace collector accepts `src/**/*.spl`, `test/**/*.spl`, and `doc/**/*.md`; it does not include the tracking `.sdn` files. | The new ingestion layer must reconcile the actual textual DB with parsed docs/tests/source. [R03] |
| F03 | `parse_trace_file` extracts `REQ-` and `NFR-` strings from file content and reads document-level headers. | Do not describe this alone as a verified scenario-level semantic `@req` graph. Structured association needs an explicit extraction contract. [R03] |
| F04 | The feature DB has requirement, research, plan, architecture, design, system-spec, generated-spec, implementation, unit-test, and integration-test columns. Sampled rows leave many fields empty. | Preserve useful identity/status data, but replace duplicated path lists with authoritative claims plus derived relationships. No full-repository completeness percentage was measured. [R04] |
| F05 | `tracking check` checks nonblank pipeline fields for valid `done` rows using numeric column positions. The inspected function does not inspect the unit/integration columns or prove referenced paths and symbols exist. | Use typed, name-addressed schema validation and graph-based completeness. A nonblank string is not evidence. [R05] |
| F06 | The pre-commit hook runs TODO scanning/generation, feature/task/bug generation, strict DB checks, and full-scope traceability checking. It invokes legacy structured-log options. | Move generation out of the minimum commit gate and replace the legacy structured format throughout this path. [R06] |
| F07 | Pre-push already delegates to a canonical driver with bounded checks and ledger/receipt handling; the must-check registry separates push and heavier work. | Reuse this mechanism rather than layering another pre-push implementation over it. [R07] [R08] |
| F08 | `.github/workflows/required-gates.yml` now owns `Code Idiom & Structural Ratchet Gates`; the older hygiene workflow says the required job moved on 2026-09-27. | Modify the current required workflow, not a stale workflow location. [R09] [R10] |
| F09 | The required workflow pins the manifest to BASE but explicitly documents that gate scripts still execute from candidate checkout content. | Close both the policy and executable trust boundaries; manifest pinning alone is insufficient. [R09] |
| F10 | The active main ruleset requires `Code Idiom & Structural Ratchet Gates` and `SPipe Self Review Admission`, with strict status-check policy. | Integrate traceability into the established admission contract. Do not assert that the repository has no remote protection. [R11] |
| F11 | The evidence loader calls its `.evidence.sdn` input “line-based ... not full SDN”: `key=value` records separated by `---`. Its rendering path parses a manifest but renders blocks without provenance admission. | Migrate the actual encoding, not just extensions; validate provenance before publishing verified evidence. [R12] |
| F12 | `RunnerTestDb` already wraps a unified database, tracks run IDs, records test results, and distinguishes unreadable existing data from cold start. | Extend this boundary rather than introducing a competing test-results writer. [R13] |
| F13 | The distributed textual DB design explicitly labels itself design-only and preserves SCV identity plus SJ mutation ownership. | Use its compatibility direction, but do not claim the proposed distributed reducer/settlement system is deployed. [R14] |

The existing required workflow's displayed comments target a short lane, but its inspected invocation uses a 240-second runner budget and a five-minute job timeout. Those are configuration limits, not measured execution times. Its current non-PR path returns success without a PR-range check; adding another trigger without revising that dispatch would not provide coverage for the new event. [R09]

## 2.3 Corrections to the earlier proposals

**Remove JSON entirely from the proposed Simple interfaces.** Do not retain an optional JSON mode, a JSON graph export, a JSON browser API, a JSON schema file, or a renamed `.sdn` file containing JSON.

**Do not infer all implementation and acceptance links from directories.** Paths can reliably associate conventional structural units; they cannot establish semantic requirement satisfaction. Requirement-to-scenario and requirement-to-implementation claims need declared metadata or a validated semantic index.

**Do not mark lower-level tests passing after only feature tests ran.** A generated report must identify the actual execution set and separately list supporting tests not executed.

**Do not make every PR run a full repository audit.** A sound incremental remote gate is the default. Full rebuild/audit is mandatory for index/rule/schema changes, missing trustworthy baselines, release qualification, and scheduled reconciliation.

**Do not equate the current source with a working release binary.** The final rollout includes source-matched CLI, hook, and runner execution tests on supported hosts.

---

# 3. Research and resulting decisions

## 3.1 Textual requirements and source navigation

StrictDoc demonstrates textual requirements, explicit relations, generated documentation, and requirements-to-source navigation; its guide labels source traceability experimental. It is a useful behavioral reference for a readable trace system. **It is not selected as a dependency or as Simple's data model.** Keep Simple's SSpec, SDN, symbol identities, and runtime evidence rather than introducing another requirements store. [W01]

Adopt the useful separation: author intent once, derive navigable views, and show unresolved relationships. Add test-run provenance and MDSOC dimensions as Simple-specific capabilities.

## 3.2 Incremental computation

The build-systems literature separates dependency discovery, scheduling, and reuse decisions. Rust's incremental compilation documentation illustrates dependency-aware validation and fingerprints. These are references for the index algorithm, not evidence that the current Simple checker already implements it. [W02] [W03]

Design consequence: cache **facts and their dependencies**, not just a last-good exit code. Record negative lookups and collection membership queries, so adding a duplicate ID or a second mapping candidate invalidates an earlier “clean” result.

## 3.3 Git snapshots and hooks

Git's hook contract provides staged-commit interception, outgoing ref/OID rows for pre-push, and incoming old/new/ref rows for pre-receive. Local hooks are bypassable. `git diff-index --cached` and batch object reads provide the foundations for inspecting the index and repository objects rather than a mutable working directory. [W04] [W05] [W06]

Design consequence: distinguish index, worktree, proposed ref updates, and candidate merge snapshots. A changed-path list is only a selector; bytes and policy must come from the selected snapshot.

## 3.4 Jujutsu is not a Git-commit hook contract

The current Jujutsu configuration documentation states that remote interactions use a Git subprocess. That does not establish that every installed version, wrapper, or operation invokes every Git hook. [W07]

Design consequence: integrate through SJ/SPipe's existing mutation/admission boundary, and test actual `git commit`, `git push`, `jj` publication, and `sj` paths. Do not copy the blanket historical assertion “jj bypasses every Git hook” into a new normative design.

## 3.5 Remote status checks

GitHub required checks have exact revision and expected-source behavior; skipped jobs and skipped workflows behave differently. Merge queues need the separate `merge_group` trigger. GitHub Enterprise Server documents administrator-managed pre-receive hooks. [W08] [W09] [W10] [W11]

Design consequence: GitHub.com admission uses required checks, not an invented installable server hook. A GHES/bare-Git pre-receive adapter is optional. A real “no relevant changes” verdict must be produced by a running trusted gate, not by skipping the required job.

## 3.6 Layered graph layout and accessibility

ELK Layered documents directional, layered layouts, orthogonal routing, and compound graphs with cross-hierarchy edges. W3C's tree-view pattern specifies keyboard behavior and distinguishes focus from selection. [W12] [W13]

Design consequence: Slop uses stable, left-to-right columns and collapsible component groups, not a constantly moving force-directed cloud. Its left tree and nonvisual relationship list remain fully operable from the keyboard. ELK is an algorithm/reference option, not a requirement to use a foreign structured protocol or deploy its runtime.

---

# 4. Requirements and non-goals

## 4.1 Normative requirements

| ID | Requirement |
|---|---|
| REQ-TRC-001 | All Simple-owned structured traceability interfaces and storage shall use schema-versioned SDN. |
| REQ-TRC-002 | Every enforced feature shall resolve to requirements and acceptance criteria without relying on prose substring matching as proof. |
| REQ-TRC-003 | The graph shall distinguish acceptance, unit, integration, and component test definitions and their actual executions. |
| REQ-TRC-004 | Deterministic conventional links shall not require redundant authored DB rows. |
| REQ-TRC-005 | Irregular and many-to-many relationships shall support explicit, attributable declarations. |
| REQ-TRC-006 | Conflicting or ambiguous relationships shall not be silently resolved by choosing the first match. |
| REQ-TRC-007 | Every diagnostic shall identify its snapshot, rule, affected entity, and evidence/provenance. |
| REQ-TRC-008 | Local commit validation shall inspect the staged snapshot or the equivalent SJ-frozen candidate, not unstaged file bytes. |
| REQ-TRC-009 | Push validation shall cover every relevant proposed ref update and handle creation, deletion, and non-fast-forward cases explicitly. |
| REQ-TRC-010 | Admission shall be bounded, offline locally, read-only with respect to tracked source, and fail explicitly when required scope cannot be checked. |
| REQ-TRC-011 | Remote admission shall use trusted checker code/policy and validate the exact candidate subject. |
| REQ-TRC-012 | Feature-level test execution shall always emit a traceability SDN artifact and a Markdown run report, including failures and partial runs. |
| REQ-TRC-013 | A requirement shall not receive verified coverage from a merely linked, skipped, missing, stale, or unexecuted test. |
| REQ-TRC-014 | Generated structural documents shall be deterministic and separate from mutable “latest run” pointers. |
| REQ-TRC-015 | Slop shall expose tree navigation, a layered graph, and a detail/source inspector over the same graph as CLI and documentation. |
| REQ-TRC-016 | Feature, layer, component/entity, and transform dimensions shall coexist without duplicating canonical artifacts or weakening MDSOC boundaries. |
| REQ-TRC-017 | The incremental result shall match a full rebuild for the same complete input snapshot and rule versions. |
| REQ-TRC-018 | Existing feature/test DB data shall migrate without silent link loss, duplicate writers, or invalidating historical evidence by relabeling it. |
| REQ-TRC-019 | Exceptions and baseline debt shall be scoped, reviewable, expiring where applicable, and unable to turn unknown evidence into pass. |
| REQ-TRC-020 | Static HTML and Slop shall retain revision, provenance, visibility, and source-navigation semantics without requiring a JSON service. |

## 4.2 Non-goals for the first release

The first release does not replace the compiler, test runner, SJ, SCV, or the existing diagram/document infrastructure. It does not attempt automatic proof that a test is sufficient, whole-program dynamic coverage in hooks, an LLM-based admission decision, mandatory GPU indexing, or implementation of the full distributed settlement protocol.

A graph can show a declared requirement-to-code link; only suitable verification can justify the associated correctness claim. Keep that limitation visible rather than concealing it behind a coverage percentage.

---

# 5. Architecture and ownership

## 5.1 One derived graph, several authoritative inputs

```text
AUTHORED INTENT                           OBSERVED REALITY
Feature identities / requirements       Source/module/symbol index
Research / architecture / design        SSpec definitions and metadata
Explicit SDN relations / exceptions     Test executions and evidence manifests
                 \                       /
                  \                     /
                   -> Snapshot adapters
                            |
                   Typed fact extraction
                            |
                 Resolution + convention rules
                            |
                    TraceGraph snapshot
                            |
             +--------------+----------------+
             |              |                |
       Admission checks  MD / HTML       Slop viewer
             |
      Existing SJ / hook / CI driver
```

“One graph” does not mean one enormous editable file. It means one semantic contract and one resolution engine. Authored requirement text stays in its requirement document; source stays in source files; runner observations stay in the test evidence store. The graph is a reproducible materialized view of those owners.

## 5.2 Authority table

| Fact | Authoritative owner | Not authoritative |
|---|---|---|
| Feature identity and lifecycle intent | Existing feature DB, then explicitly migrated feature records | A generated feature page |
| Requirement/acceptance text | Requirement document and stable IDs | An ID occurring in a code example |
| Test definition and acceptance association | SSpec metadata/AST or an explicitly owned SDN declaration | A generated scenario manual |
| File/module/symbol existence | Exact snapshot plus admitted source index | A cached path from another checkout |
| Conventional association | Versioned mapping rule evaluated against the snapshot | A copied path field maintained by hand |
| Irregular semantic link | Its single registered SDN/SSpec owner | Conflicting declarations in multiple files |
| Actual test outcome | Runner observation plus terminal run manifest | Feature `done` status, a screenshot, or a printed `PASS` string |
| Expected outcome / exemption | Reviewed policy record | An untrusted CI producer |
| Remote qualification | Trusted admission receipt for the candidate | Any local “latest success” marker |

## 5.3 Module boundaries

Proposed logical packages; exact physical placement must pass the repository's current layer/import rules:

```text
src/lib/common/traceability/
    model.spl                 # typed entities, claims, edges, diagnostics
    identity.spl              # reuse/resolve existing identities
    schema.spl                # schema and endpoint validation
    conventions.spl           # pure structural mapping rules
    resolve.spl               # conflicts, overrides, canonical edges
    obligations.spl           # applicable requirements and test obligations
    evidence.spl              # observation eligibility and evaluation
    incremental.spl           # fact/query invalidation and graph deltas
    query.spl                 # bounded read-only views
    sdn_codec.spl             # shared native codec integration
    markdown.spl              # deterministic trace section projection

src/app/traceability/
    main.spl                  # retain current command boundary
    snapshot/                 # Git index/tree, SJ candidate, worktree preview
    extract/                  # docs, SSpec, source index, existing DB adapters
    store/                    # SDN shards, transactions, cache publication
    admission/                # gate profiles and receipts

src/app/slop/
    main.spl
    feature/                  # selection, tracing, inspection, navigation
    transform/                # graph/domain -> view models
    view/                     # tree, layered canvas, details, source pane
    provider/                 # existing Simple UI/web rendering interfaces
```

Keep the domain kernel free of filesystem, Git, network, clocks, process launching, and arbitrary plugins. App adapters supply immutable inputs and commit side effects through the existing owner. A hook entry must not load the full GUI/compiler closure merely to validate a few records.

## 5.4 MDSOC composition

Represent **feature**, **layer**, **component/entity**, and **transform** as dimensions. A shared parser component may implement several features, and one feature may cross frontend, runtime, and UI layers. That is a many-to-many relationship, not a reason to clone artifacts into several directory trees.

Only the existing composition rules determine which imports or cross-dimension transforms are legal. A trace link to another layer is informational and does not grant a new import capability. Slop's view transforms depend on public graph contracts, not private compiler or sibling-capsule implementations.

Use typed facets for document extraction, SSpec extraction, source indexing, evidence loading, layout, and rendering. Seal the mandatory checker facets for admission. Optional viewer facets cannot mutate outcomes or silently add permissive policies.

---

# 6. Trace semantics and identity

## 6.1 Entities

| Entity | Identity and role |
|---|---|
| Feature | Reuse existing feature ID; do not renumber all `FR-*` records to impose a new prefix. |
| Requirement | Namespace-qualified stable `REQ-*`/`NFR-*` identity. |
| Acceptance criterion | Stable criterion under a requirement; prose criterion and executable scenario remain separate. |
| Test suite/spec artifact | File/module-level SSpec container. |
| Test case/scenario | One logical executable definition with `kind = acceptance \| unit \| integration \| component \| system \| performance`. |
| Parameterized case | Definition ID plus canonical parameter-set digest; avoids collapsing separate cases. |
| Source artifact | Repository-qualified path at a snapshot; stable artifact ID when available. |
| Symbol/interface | Existing compiler/export identity when available; otherwise a qualified, revision-scoped locator, not a fake globally stable ID. |
| Component/layer/transform | Architecture entities with composition provenance. |
| Document/section | Research, requirement, plan, architecture, design, guide; stable section anchors where explicitly referenced. |
| Run/observation/evidence | Immutable execution identity and revisions, separate from test definitions. |
| Exception/decision/bug | Reviewed reason, scope, owner, expiry/review rule, and related entities. |

A scenario appearing in a generated Markdown manual is **not a second test**. It is a presentation of the same definition. A test can have several roles only when explicitly modeled; do not execute it twice because two folders or views discover it.

## 6.2 Relationships

| Relation | Allowed endpoints | Meaning |
|---|---|---|
| `specifies` | Feature -> Requirement | Feature intent includes this requirement. |
| `decomposes_to` | Requirement -> AcceptanceCriterion | The criterion contributes to the requirement's acceptance contract. |
| `accepted_by` | AcceptanceCriterion -> AcceptanceTest | The scenario declares this criterion as its obligation. |
| `verified_by` | Requirement or Criterion -> Unit/Integration/ComponentTest | Explicit supporting verification, when declared. |
| `targets` | Test -> SourceArtifact/Symbol/Component | Structural or declared test target; provenance determines its strength. |
| `implemented_by` | Requirement/Feature -> Symbol/Component/SourceArtifact | Declared implementation responsibility, not execution proof. |
| `motivated_by` | Requirement/Feature -> Research/Decision | Rationale. |
| `described_by` | Feature/Component -> Design/Architecture section | Documentation relationship. |
| `belongs_to` | Artifact -> Component/Layer/Feature | Structural/ownership membership. |
| `generated_from` | Generated document -> Spec/Graph | Derivation, never an independent verification claim. |
| `observed_in` | Test case -> Observation | Actual execution association. |
| `produced` | Observation -> EvidenceArtifact | Result/artifact provenance. |
| `depends_on` | Component/Symbol/Test -> dependency | Declared or compiler-observed dependency, labeled by source. |
| `supersedes` / `aliases` | Compatible identities | Explicit historical continuity; no automatic equivalence of changed behavior. |

The complete graph is a directed multigraph. Reject cycles in containment, alias resolution, and other relations whose contract is acyclic. Do **not** reject every cycle merely because trace and reverse-navigation relationships can form a cycle. Layout may condense permitted strongly connected groups without changing underlying meaning.

## 6.3 Separate claims from resolved edges

An extracted declaration is a **claim** with origin file, span, snapshot, extractor version, and authority. Resolution yields a canonical edge, a conflict, or an unresolved diagnostic.

For one relationship, several origins may corroborate the same edge. Keep all provenance without duplicating coverage. Two authoritative sources disagreeing on a single-valued relationship produce a conflict; they are not combined into a convenient union.

## 6.4 Identity and moves

Existing semantic IDs remain the primary keys. Do not identify requirements or scenarios solely by line numbers, display titles, or row order.

For ordinary, unreferenced unit cases, derive a definition locator from file/module identity and lexical scenario context. Display that locator as revision-scoped when no stable ID exists. When a scenario becomes a durable cross-artifact reference, assign a stable identity through SSpec metadata or its registered SDN metadata owner. This is a targeted exception to omission, not a demand to annotate every assertion.

Move transactions preserve known artifact IDs and update locators. Ambiguous rename detection produces a proposed alias for review, not an automatic historical identity transfer. Splits and merges require explicit dispositions. Never reuse a deleted ID for a different requirement.

Preserve SCV `ChangeIdentity` and `RevisionIdentity`; any future compact settled integer is an alias requiring namespace/kind context. The graph does not introduce its own distributed sequence allocator. [R14]

---

# 7. Convention-first links and explicit exceptions

## 7.1 What may be omitted

| Link | Omit authored record when | Do not infer |
|---|---|---|
| Source file -> unit spec | A versioned mapping yields exactly one existing, recognized test artifact. | That all functions or requirements are covered. |
| Module -> integration spec | Registered module-root mapping yields one explicit module test convention. | That every sibling integration test targets this module. |
| Component -> component test | Registered component manifest and classifier unambiguously associate them. | A new test-directory numbering convention not yet adopted by the repo. |
| SSpec -> generated manual | Existing docgen mirror rule and generator manifest resolve the output. | That a rendered manual proves a run occurred. |
| Artifact -> layer/component | Existing layout/manifest mapping is unique. | Feature semantics solely from the component name. |
| Requirement -> companion document | A declared, versioned companion convention is exact and unambiguous. | “Same basename” across several directories or unrelated documents. |

Keep discovery and semantics separate. Imported production code is evidence of a possible target, not automatic evidence that every imported symbol was exercised.

## 7.2 Mapping rules

Use scoped rules with explicit input roots and logical-unit mappings. Numeric source layers and legacy test roots must be normalized by registered mappings, not by globally stripping digits from paths. Exclude vendored/generated trees according to trusted policy; do not silently exclude newly added roots.

Illustrative proposed SDN:

```sdn
mapping_rules |id, source_root, target_root, source_suffix, target_suffix, relation, cardinality|
    app-unit-v1, "src/app/", "test/01_unit/app/", ".spl", "_spec.spl", targets, one
    spec-md-v1, "test/", "doc/06_spec/", ".spl", ".md", generated_from, one
```

These are example rule rows, not a claim that every current test follows them. A discovered mismatch is either existing baseline debt or an explicit exception; it is not repaired by selecting another file with a similar name.

For a unit-test rule, the resolver emits `test targets source`, even though the discovery function starts from a source path. Store semantic edge direction, not incidental lookup direction.

## 7.3 Exception operations

Support `add`, `replace`, and `suppress` with distinct meanings:

- **Add:** additional intentional relation, such as one shared unit suite targeting two files.
- **Replace:** replace a specific conventional mapping; identify the rule and the original endpoint scope.
- **Suppress:** suppress one structural expectation, with a reviewed reason and applicable policy. It does not claim verification.

No global “ignore irregular links” switch. A replacement that stops matching its referenced rule becomes stale and fails validation. A suppression needs an owner and review/expiry condition; legitimate no-test obligations need a separately reviewed applicability decision.

```sdn
explicit_links |id, owner, from_id, relation, to_id, operation, replaces_rule, reason|
    LINK-TRC-001, "feature:traceability", "test:tooling-traceability", targets, "source:app-traceability-core", replace, app-unit-v1, "Shared tooling spec intentionally covers the traceability core"
```

Endpoint IDs resolve through the artifact registry/locators. This avoids placing several semicolon-delimited paths in a single field. A link declaration and its locator are not duplicate facts: one states intent, the other locates the artifact.

## 7.4 Resolution order

1. Load trusted conventions and artifact facts from the exact snapshot.
2. Resolve explicit identities and references; reject invalid endpoint kinds.
3. Determine the registered authority for each declaration group.
4. Apply a targeted, authorized replacement/suppression to its exact conventional edge or obligation.
5. Add independent explicit links.
6. Coalesce identical edges while preserving all origins.
7. Validate cardinality, stale overrides, conflicts, missing endpoints, and applicable obligations.

Generated pages have no authority to override their inputs. A more recently edited file does not automatically win a conflict.

## 7.5 Metadata placement

The default semantic owner is the artifact that can express the relationship naturally: requirement declarations in requirements, acceptance associations in SSpec, architecture membership in the existing composition manifest. SDN exception files cover relationships that cannot be represented there cleanly.

The first release must not depend on a new compiler annotation grammar. Existing supported SSpec metadata is reused. Where new stable scenario IDs or associations are needed, provide a versioned SDN metadata block/sidecar accepted by the SSpec extractor; any later annotation syntax is sugar over the same model. Arbitrary `@req` text inside a quoted example remains documentation, not a live declaration.

---

# 8. SDN contracts and serialization

## 8.1 The format boundary

**SDN is mandatory, not merely the default among several machine formats.** Configuration, typed records, graph partitions, diagnostics, receipts, run summaries, query responses, and incremental viewer updates all use SDN. Markdown and HTML are human-readable projections, not alternative structured authorities.

Do not add a JSON backend, compatibility switch, schema, embedded data island, or viewer endpoint. The traceability migration removes legacy structured-output switches from its callers. Third-party service adapters may have to implement a provider's externally imposed wire protocol; that encoding remains inside the adapter and must not leak into the Simple graph, DB, CLI, or viewer contract. Existing GitHub workflow syntax is also an external hosting constraint, not a replacement for the SDN gate registry.

Use the actual shared SDN parser/writer. Renaming custom text to `.sdn` does not qualify. In particular, the current evidence sidecar's `key=value`/`---` format needs a versioned importer and a real SDN replacement. [R12]

**Example status:** All SDN schemas below are proposed contracts using the repository's tabular SDN style. They require parser round-trip fixtures before implementation admission; this report does not claim they were executed through the current Simple parser.

## 8.2 Schema families

| Schema family | Principal records | Authority |
|---|---|---|
| `simple.trace.policy` | mapping rules, required obligations, scopes, limits | Reviewed policy |
| `simple.trace.declarations` | explicit claims, aliases, targeted exceptions | Authored intent |
| `simple.trace.graph` | nodes, resolved edges, locators, provenance, diagnostics | Derived snapshot |
| `simple.trace.run` | run subject, planned cases, observations, artifacts, completion | Test runner |
| `simple.trace.qualification` | obligation evaluations, eligible evidence, refusal reasons | Evaluation engine |
| `simple.trace.receipt` | checker identity, subject, input set, policy, scope, verdict | Admitted producer |
| `simple.slop.message` | query, response, snapshot announcement, delta | Viewer service |
| `simple.slop.preferences` | layout, filters, recent selections | User-local preferences |

A document declares schema family and version. Unknown major versions, duplicate key columns, wrong field types, conflicting IDs, and missing required references fail validation. Optional extension namespaces are registered explicitly; they cannot redefine core verdict or identity fields. Do not silently discard unknown fields that could change interpretation.

## 8.3 Normalized graph representation

Separate node identity, physical location, resolved relationships, and relationship provenance. Avoid one very wide table with a different meaning for every empty column.

```sdn
schema:
    name: "simple.trace.graph"
    version: 1

snapshot:
    id: "snapshot:example-001"
    kind: "illustrative"
    complete: false

nodes |id, kind, title|
    "feature:traceability", feature, "Traceability"
    "req:REQ-TRC-004", requirement, "Conventional links need no duplicate authored rows"
    "test:tooling-traceability", test_case, "Resolve a conventional unit mapping"
    "source:app-traceability-core", source_file, "Traceability core"

edges |id, from_id, relation, to_id|
    "edge:example-1", "test:tooling-traceability", targets, "source:app-traceability-core"

edge_origins |edge_id, origin_kind, origin_id, declaration_path|
    "edge:example-1", explicit, "LINK-TRC-001", "doc/08_tracking/trace/features/traceability.sdn"

locators |entity_id, path, locator_kind, locator|
    "source:app-traceability-core", "src/app/traceability/core.spl", file, ""
```

The example is deliberately not a complete graph or an accepted receipt. Production snapshots must resolve every referenced entity and carry a validated input manifest.

Use integer durations, byte sizes, counters, and explicit units. Ratios are `{numerator, denominator}` records/columns, not strings such as `14/15` requiring another parser. Unknown is not zero; an optional value and its availability state must be distinguishable.

## 8.4 Separate status dimensions

Do not overload one `status` column:

| Dimension | Representative values |
|---|---|
| Structural resolution | `resolved`, `missing`, `ambiguous`, `conflicting`, `excluded_by_policy` |
| Relationship origin | `explicit`, `annotation`, `convention`, `compiler_index`, `runtime_observation` |
| Execution outcome | `pass`, `fail`, `timeout`, `skipped`, `cancelled`, `infrastructure_error`, `not_run` |
| Evidence validity | `eligible`, `stale`, `unverified`, `missing_artifact`, `invalid_provenance` |
| Obligation applicability | `required`, `not_applicable_reviewed`, `undetermined` |
| Qualification | `satisfied`, `unsatisfied`, `incomplete`, `not_applicable_reviewed` |

An observation can be `pass` while its evidence is `stale`; the current qualification is then not satisfied by it. A resolved conventional edge can exist while the associated test remains `not_run`.

## 8.5 Deterministic encoding and validation

Use the shared SDN writer with UTF-8, LF, and one final newline. Emit tables in schema-defined order and unordered rows by canonical key. Preserve meaningful order using an explicit ordinal column, including scenario steps, stack frames, and action traces. Quote/escape through the codec rather than concatenating strings.

Validate duplicate headers, duplicate record IDs, malformed quoted fields, invalid enum values, cardinality, integer overflow, and reference closure. Distinguish absent optional data from an authored empty string. A literal `N/A` does not constitute a reviewed applicability exception.

Identifiers use a restricted validated grammar. Source text and repository paths retain their actual bytes and case; do not normalize code or case-fold distinct Git paths to make a link resolve. Host filesystem aliases and case collisions are diagnosed at the snapshot adapter boundary.

For content identity, canonicalize the schema's semantic records, not a human pretty-print from an arbitrary formatter. Reuse the existing SCV digest/signature boundary when available; the trace format is not a second competing cryptographic protocol. A receipt binds the canonical payload using an explicit algorithm/domain/version and excludes its own digest/signature fields from the signed payload.

Existing SDN seals, including CRC-based corruption checks where used, remain writer-owned and must be updated by the supported writer. A corruption checksum is not producer authentication. Accepted evidence requires actual digest validation against artifact bytes, not a string shaped like a digest.

## 8.6 Avoid self-referential hashes

A generated, committed Markdown file cannot safely contain a digest of the entire candidate tree that includes that same generated file: writing the digest changes the tree again.

Use two identities:

1. **Structural input manifest:** authored requirements, declarations, relevant source/test facts, extractor versions, mapping rules, and publication policy. It excludes the generated outputs it describes.
2. **Admission subject:** the complete Git candidate tree/commit, bound in an external run artifact or receipt after the candidate exists.

Stable Markdown embeds the structural input identity. Run reports outside the tracked source tree can embed the exact candidate revision. CI compares generated output against the candidate and binds that comparison in its receipt. Do not substitute an unversioned `latest` pointer for either identity.

---

# 9. Text database evolution and update transactions

## 9.1 Storage layout

Keep intent small and derived data disposable:

```text
config/traceability.sdn                         reviewed trace policy / mappings
config/check/must_check_gates.sdn               existing canonical gate registry

doc/08_tracking/feature/feature_db.sdn           existing feature identity/lifecycle rows
doc/08_tracking/trace/features/<feature>.sdn     nonredundant semantic claims / exceptions

target/trace/snapshots/<snapshot-id>/
    manifest.sdn                               exact inputs / versions / completion
    nodes-<partition>.sdn
    edges-<partition>.sdn
    diagnostics.sdn

target/test-results/<run-id>/
    run.sdn                                    immutable finalized run manifest
    observations-<shard>.sdn
    traceability.sdn                            qualification and provenance
    traceability.md                             human run report
    artifacts/                                 logs/captures or CAS references

doc/06_spec/trace/
    index.md                                   stable generated structural index
    feature/<feature-id>.md
    component/<component-id>.md
```

These are proposed paths. Use portable filesystem-safe encodings for filenames while preserving original entity IDs inside records. Per-run output paths are immutable; a user-local `latest.sdn` is a convenience pointer, never evidence authority.

Do not commit detailed graph caches, every test execution, or raw captures into the main source repository. Approved evidence can later be published through the planned sibling `simple-data`/CAS arrangement without changing graph semantics. [R14]

## 9.2 Evolve the existing feature DB, do not discard it

The current wide table contains useful IDs, titles, statuses, and external bindings. Its positional readers are a migration hazard. [R04] [R05]

Use a staged migration:

1. Introduce schema-aware readers addressed by column name; reject incompatible schemas instead of guessing positions.
2. Import existing path fields into typed claims, preserving original text and reporting unresolved values.
3. Identify exact duplicates of derivable conventional links. Produce a reviewable migration plan; do not remove them silently.
4. For each feature, register whether its trace declarations are still owned by the legacy row or by the new declaration shard.
5. Compare the old resolved graph and the proposed resolved graph. Require no unexplained lost edges or identities.
6. Transfer ownership in one transaction. Legacy columns become a read-only compatibility projection or are retired after consumers migrate.

The feature's identity must not change because its declarations moved. Preserve existing `FR-*` IDs and aliases. Do not introduce a second mandatory `FEAT-*` numbering scheme just for the viewer.

A shard is optional when the existing artifact metadata and conventions are sufficient. Creating an empty trace file for every feature would recreate the maintenance burden this design is intended to remove.

## 9.3 What gets updated automatically

| Event | Automatic derived update | Authored update |
|---|---|---|
| Source or conventional unit spec added | Recompute mappings, graph facts, affected diagnostics | None when unique and policy-compliant |
| Shared/irregular test added | Report missing or ambiguous association | Add one intentional link through the supported writer |
| Requirement/AC changed | Invalidate affected qualification and generated structural pages | Requirement author edits its authoritative declaration |
| Test run ends | Append observation/run records and generate run SDN/Markdown | No automatic feature `done` or bug closure |
| A convention changes | Recompute impacted mappings; identify stale overrides | Reviewed policy edit |
| An approved migration applies | Replace owned records atomically; refresh projections | Explicit transaction through SJ/DB owner |
| An approved evidence publication occurs | Update publication index and source-pinned views | Controlled publication record, not a normal test-side effect |

The existing test DB view should show newly completed run data immediately through `RunnerTestDb`. The graph consumes the same observation identity rather than writing an independent copy with a separate outcome. [R13]

## 9.4 Single-writer and crash consistency

Use the established SJ/DB mutation owner. Read-only graph construction and test-report generation do not gain permission to modify tracked feature declarations.

For derived graph snapshots, write a new generation into temporary files, validate every partition, then atomically publish its complete manifest/pointer. Readers see either the previous complete generation or the new complete generation. They never read a mixture. Persist/fence writes according to the host's supported filesystem semantics; disclose a weaker durability level rather than pretending an unsupported flush succeeded.

Run shards are append-only until finalized. A run manifest names the exact accepted shard set and planned case set. A crash before finalization leaves an incomplete run; recovery may finalize an explicit interrupted record but must not fabricate missing observations.

Use compare-and-swap generation checks for mutable indexes and explicit leases for authored transactions. Concurrent writer conflict returns a retryable conflict, not last-writer-wins loss. Two execution attempts have distinct attempt identities even when they belong to one case.

## 9.5 History and retention

Preserve immutable run/config/test-definition identities and expectation revisions. Prune large raw evidence by policy with an explicit `expired` or `unavailable` dependency state; keep the manifest and disposition. A record with a pruned required artifact cannot later be promoted as freshly verifiable evidence.

Legacy custom evidence sidecars may be displayed as imported historical material. They become accepted evidence only when original subject, producer, definition, environment, artifact identity, and comparison provenance can actually be validated. Importing them through the new parser does not retroactively establish those facts.

---

# 10. Incremental graph construction and invalidation

## 10.1 Snapshot providers

The kernel receives immutable records. Effectful providers supply bytes from one of:

- Git index: exact staged blobs and the staged path inventory.
- Git revision/tree: exact immutable objects, independent of sparse working checkout.
- SJ-frozen candidate: the mutation owner's immutable candidate manifest.
- Worktree session: explicitly labeled uncommitted snapshot for interactive use, never implicitly substituted for a commit/push subject.

Use batched object reads instead of spawning a subprocess for every file. A sparse checkout missing `doc/` is not proof that the candidate contains no requirements. [W05] [W06]

## 10.2 Cache keys

A file fact cache key includes source blob identity, extractor identity/version, relevant grammar mode, schema version, and extraction configuration. A resolution cache key additionally includes mapping/policy identities and the identities of its lookup results.

A graph manifest records repository identity, snapshot kind, object format, tree or input-manifest identity, extractor/rule versions, exclusion policy, and partition hashes. A cached success without this binding is only a log message.

Keep content fingerprints and semantic fingerprints separate. A prose-only edit may leave some structural edges unchanged, but evidence reuse must still validate its declared input set. Semantic equivalence is not permission to ignore unknown runtime dependencies.

## 10.3 Dependencies include absence

Track both positive and negative dependencies:

| Dependency | Why it must be recorded |
|---|---|
| Existing referenced ID | Deleting or changing its declaration affects incoming links. |
| Missing referenced ID | Creating it must clear the corresponding missing-link diagnostic. |
| Unique ID lookup | Adding a second declaration must invalidate the previous unique answer. |
| Directory/glob membership | Adding a second conventional test can create ambiguity. |
| Module/component membership | Moving a file affects multiple feature views and obligations. |
| Mapping/rule identity | Rule changes can invalidate untouched source and test files. |
| Test-definition/config/expectation identity | A previous passing observation may cease to be eligible. |
| Exclusion/namespace registry | New roots or policy changes must not bypass scanning. |

This is the difference between a correct incremental graph and a changed-files grep wrapper. The incremental-computation references motivate dependency-aware reuse; the exact negative-lookup design here is a proposed Simple contract. [W02] [W03]

## 10.4 Update algorithm

```text
input: admitted base facts/index, exact candidate snapshot, trusted rules

1. Validate base manifest and versions.
2. Obtain added / modified / deleted paths and both sides of rename candidates.
3. Read changed blobs from the candidate, not the worktree.
4. Remove prior facts for deleted/replaced artifacts.
5. Extract current facts; keep parsing failures as explicit unresolved state.
6. Invalidate positive dependencies, negative queries, and membership queries.
7. Resolve affected declarations and mapping obligations to a fixed point.
8. Recompute affected feature/requirement qualification and reverse indexes.
9. Validate scope completeness and structural invariants.
10. Publish a complete new graph generation, diagnostics, and scoped receipt.
```

Renames are an optimization hint, not identity authority. If a move cannot preserve identity unambiguously, resolve it as delete/add and require an explicit alias where stable cross-references matter.

The selected changed set is **not** the entire existence universe. Unchanged referenced files must resolve through the validated base inventory. Likewise, validation of changed source must inspect incoming edges from unchanged requirements/tests where they can become invalid.

## 10.5 Sound scope selection

Local commit checks cover affected structural obligations and their dependencies. Push/remote checks expand to affected feature/component qualification and required generated projections. Shared components can implicate several features; selecting only the directory containing the edited source is insufficient.

If the dependency closure is unknown, broaden the scope or return `incomplete`. Do not claim that the untouched remainder was checked. Global schema changes, extractor upgrades, mapping-root changes, and ID-namespace changes require a full index rebuild or a formally complete partition invalidation.

When no relevant inputs changed, emit a complete scoped verdict explaining that fact and naming the trusted input classifier. An empty changed set caused by a failed Git command is an error, not “no relevant changes.”

## 10.6 Cold caches and equivalence

A missing or incompatible base cache triggers a bounded rebuild attempt. If the mandatory local scope cannot be constructed inside its budget, return an explicit infrastructure/incomplete result with the command to refresh the index outside the hook. Never launch an unbounded rebuild inside a commit hook or declare success because the cache was absent.

Remote admission may restore only provenance-validated cache artifacts or rebuild from repository objects. Untrusted cache content is a performance hint until verified, not admission authority.

The central regression property is:

```text
normalize(incremental(base, delta, candidate, rules))
    == normalize(full_rebuild(candidate, rules))
```

Compare nodes, typed edges, provenance, unresolved references, obligations, and diagnostics—not just counts. Use randomized edit sequences as well as hand-written deletion, duplication, rename, and policy-change fixtures.

---

# 11. Minimum local commit and push gates

## 11.1 Gate profiles

A short structural check and a full execution proof are different obligations. Every relevant commit/push runs traceability validation; neither operation automatically runs the entire test suite.

| Profile | Subject and mandatory work | Explicitly excluded |
|---|---|---|
| `commit` | Exact index/SJ candidate; changed SDN/metadata syntax; identity and reference integrity; affected conventional/explicit mappings; protected-policy changes identified | Network, build, test execution, full documentation regeneration, automatic staging |
| `push` | Every outgoing ref subject; commit checks plus affected feature/component closure; required declaration/projection consistency; eligible receipts only where policy requires them | Unbounded scans, bootstrap, device tests, opportunistic downloads |
| `remote` | Trusted validator against exact candidate; sound incremental completeness; current admission-policy and receipt validation | Trust in arbitrary local success files |
| `audit` | Full graph rebuild, full structural consistency, debt reconciliation, deterministic projection checks | A claim that all runtime tests ran unless separately executed |
| `qualification` | Explicit required test/evidence scope plus trace and documentation admission | Treating a partial developer test run as full qualification |

Draft/in-progress features may have declared, visible unfulfilled obligations. They still cannot contain malformed SDN, duplicate identities, misleading verified claims, or unexplained broken links introduced by the change. A transition to a completed/qualified lifecycle state applies the stricter completeness profile.

This preserves useful work-in-progress commits without relaxing traceability into an optional task.

## 11.2 Local pre-commit

The hook validates staged blobs. A clean worktree copy cannot mask a broken staged copy, and an unstaged edit cannot cause a false failure for a different staged candidate.

The adapter must respect alternate index files and linked worktrees. Capture repository identity and the selected index before clearing environment for unrelated child commands. Do not derive the repo root solely from a symlinked hook script's directory.

The traceability part of pre-commit performs:

1. Resolve the candidate snapshot and relevant changed inputs.
2. Validate changed schemas/declarations and affected inbound/outbound relationships.
3. Check unique convention mapping, irregular-link ownership, and policy changes.
4. Emit one SDN result and return the documented exit status.

It does not run `todo-gen`, `feature-gen`, `task-gen`, `bug-gen`, or a full trace-page generation sweep. The inspected pre-commit currently does those broader operations; migrate them to explicit maintenance/publication and appropriate remote tiers. [R06]

Preserve secret scanning, conflict/tree-safety checks, and legitimate existing hook chaining. This report changes the traceability workload, not permission to delete unrelated security guards. Any existing automatic source normalization must be reviewed separately; the new trace checker itself is read-only.

## 11.3 Local pre-push

Keep the existing dispatcher and canonical must-check driver. Extend their registry/implementation once. Do not install a second launcher that can recurse into the first.

Git passes one row per outgoing ref; consume and store those rows before invoking child tools. Validate every row. A failed read or unexpectedly empty subject list must not be interpreted as a clean push. [W04]

| Ref update | Traceability treatment |
|---|---|
| Existing branch, forward update | Inspect exact old/new objects and affected semantic closure. |
| New branch | Resolve the configured trusted baseline or verified remote ancestry; validate the new tip. Do not use the zero OID as an ordinary base. |
| Branch deletion | Apply protected-ref policy and validate any repository-level references/publication obligations that depend on that ref; do not attempt to parse a nonexistent new tree. |
| Non-fast-forward update | Apply ref policy first; if allowed, compare the actual old/new subjects and discard invalid inherited receipts. |
| Tag update | Apply configured tag/release policy, peel only where appropriate, and bind the result to the actual tag/target subject. |
| Multiple refs | Produce per-ref records plus one aggregate verdict; one passing ref cannot hide another failure. |

Do not assume every push targets `origin/main`. Do not inspect the working directory in place of the pushed commit. Structural endpoint validation is not proof that every intermediate commit is valid; if a protected policy requires every outgoing commit to satisfy an invariant, declare and check that separate range obligation.

The existing pre-push path already has root/wiring checks, captured ref input, and bounded-ledger handling. Reuse them. The current implementation also contains an optimized path selected for a particular known blocking-row set; adding a traceability row requires tests of both optimized and general paths, not just appending a registry line. [R07] [R08]

## 11.4 Jujutsu and SJ/SPipe

Install the same semantic gate at the supported SJ/SPipe freeze/publish boundaries. Git hooks remain adapters for contributors using Git directly; they are not the only enforcement point.

For each supported Jujutsu version/transport, record which commands actually invoke the Git dispatcher. The currently documented Git-subprocess behavior is not sufficient evidence to assume hook coverage. A fixture must exercise the real publication route and prove the exact subject reached the validator. [W07]

Avoid double work when two adapters run: a previously admitted scoped receipt may be reused only when its complete subject, checker, policy, and input set match. Reuse is an optimization, not a bypass for missing or stale validation.

## 11.5 Binary and budget failure

Use a small, source-matched traceability CLI target or an already admitted lightweight module entry. Do not build the compiler or load the Slop/UI dependency closure inside the hook.

A missing executable, unsupported schema, failed object read, exhausted budget, or invalid base index returns an infrastructure/incomplete result. The diagnostic identifies the failed prerequisite and the explicit repair/index command. It must not print `clean` or silently skip traceability.

Ordinary developer pushes need not possess full hardware-test receipts when those tests belong to remote qualification. Structural traceability still runs locally. A protected publish path requiring a qualification receipt refuses absent or ineligible evidence; it cannot promote a local “report-only receipt exists” observation into proof.

---

# 12. Remote admission and full audit

## 12.1 Current integration point

At audit time, the active main ruleset requires two contexts: `Code Idiom & Structural Ratchet Gates` and `SPipe Self Review Admission`. The first is carried by `.github/workflows/required-gates.yml`, not the former hygiene workflow location. [R09] [R10] [R11]

Initially add traceability as a mandatory result within the existing fast admission aggregation. Keep status names stable during that migration. A separate required traceability context is justified only if it improves ownership/observability without creating duplicated execution or queueing; it requires an explicit ruleset migration.

The current sparse checkout does not contain all traceability inputs. Use exact Git-object snapshot reads or an admitted index, rather than concluding that absent working-tree paths are absent from the candidate. The current workflow also returns early for events without PR endpoints; replace that behavior with explicit event-to-subject resolution before enabling additional admission events. [R09]

## 12.2 Trust code, policy, and the control plane

The inspected workflow pins the gate manifest to BASE but acknowledges that its runner and gate scripts remain candidate-controlled. A candidate could change a script to report success while the manifest still appears trusted. [R09]

Required design:

- **Trusted control plane:** the required-check producer/workflow definition must be independently protected from the candidate being judged.
- **Trusted executable:** resolve the checker and its dependencies from an admitted immutable artifact or trusted revision, not candidate source.
- **Trusted policy:** load rule selection, baselines, exclusions, and exception policy from the admitted policy revision. Candidate policy changes are reviewed as data before promotion.
- **Untrusted subject:** candidate source, tests, docs, SDN, and generated pages are inputs to the checker, not executable gate extensions.

Materializing gate scripts from BASE closes the script-content gap only if the invoking workflow, dependency loading, executable search path, and status producer are also trusted. Do not call the boundary closed merely because one script is pinned.

A trusted reusable control workflow or dedicated GitHub App/service can implement this boundary. The chosen producer must match the required check's configured expected source. Changing the producer requires coordinated ruleset configuration and negative tests; this report does not change those settings. GitHub documents expected-source and current-revision requirements for required checks. [W08] [W09]

## 12.3 Isolate actual execution

Static traceability checking parses candidate content without executing repository-provided scripts, SSpec helpers, Markdown directives, or viewer plugins.

Actual tests execute candidate code and need a different security boundary. Use an isolated, disposable execution environment with minimal permissions and no publication credentials. This is particularly important when a required job uses a persistent self-hosted runner, as the inspected workflow does. [R09]

Do not expose privileged tokens through `pull_request_target` while checking out and executing untrusted candidate code. The trusted admission controller may inspect/verify the result of a separate unprivileged test job, but must independently validate its subject, manifest, and producer provenance.

## 12.4 Exact integration subject

A passing feature-branch head is not automatically evidence for its eventual merge with a newer base.

Implement explicit subject resolution:

| Event / operation | Subject to validate |
|---|---|
| PR review | Exact candidate head and base; record both identities. |
| Integration admission | Exact merge candidate or serialized publication candidate whose tree will be integrated. |
| Merge queue, when adopted | The actual merge-group SHA and composition supplied by that event. |
| Direct protected publication | Exact proposed new ref subject through the authorized publish path. |
| Post-main audit | Exact observed main revision, clearly an audit rather than retroactive pre-admission. |

If no merge queue is used, the existing publisher must refresh/revalidate the integration candidate when its base advances. Alternatively, configure an appropriate current-base requirement and prove that its executed subject matches the intended integration. Do not reuse an old head-only receipt after a rebase/merge changes relevant inputs.

GitHub has a distinct `merge_group` event; adding that trigger alone is insufficient if the job still expects PR-only fields and returns success on missing endpoints. [W10]

## 12.5 No skipped mandatory gate

Run the required admission job even for documentation-only changes. It may produce a complete `no_relevant_changes` scoped result only after its trusted classifier checks the candidate's actual changed inputs.

Do not rely on job-level skip semantics for truthfulness. GitHub treats certain skipped/neutral check states differently from a workflow that never runs; the policy aggregator must require complete valid trace results, not simply “no failing child status.” [W09]

Upload SDN diagnostics and the scoped Markdown report on failure as well as success. A producer failure, missing artifact, incomplete result, or mismatched subject is non-green admission.

## 12.6 Full audit policy

The full structural audit runs for schema/extractor/rule changes, missing trustworthy baselines, release qualification, scheduled reconciliation, and explicit maintainers' requests. It also verifies that incremental results match a rebuild over the same inputs.

Normal PR admission remains incremental only where its dependency coverage is demonstrably complete. A high-fan-out change that exceeds the fast lane triggers the explicit full validation lane; it does not receive a guessed green result to preserve a timing target.

Legacy debt remains visible and ratcheted. Full audit success means “all applicable structural obligations satisfied or explicitly admitted under policy,” not “every runtime test passed.” Runtime qualification is a separate named result.

## 12.7 Remote hooks on other hosts

For administrator-controlled bare Git/GHES, a pre-receive adapter can validate incoming old/new/ref rows using quarantined incoming objects, an admitted checker, and a bounded policy. It should not run compilers, device tests, or document-generation sweeps. On GitHub.com use the required-check/publisher model; do not describe a custom pre-receive installation as an available repository feature. GHES documents the administrator-managed option. [W04] [W11]

Post-receive processing can publish reports and queue deep audits, but it cannot prevent the update that already occurred. Keep prevention and observation distinct in UI labels and receipts.

---

# 13. Test execution, evidence, and feature completion

## 13.1 Integrate at the runner boundary

Extend `RunnerTestDb`/its unified database boundary with immutable run-subject and per-case provenance records. Existing run IDs, updates, and resource reporting are useful seams; do not create another independently mutable test-outcome store in the graph layer. [R13]

The runner emits events/finalized records. The trace evaluator joins them with the frozen graph and obligations. The Markdown generator and Slop read that joined result.

```text
Freeze source + test definitions + config + expectations + trace graph
                         |
                  Plan selected cases
                         |
                    Execute cases
                         |
              Record actual observations
                         |
                Finalize run manifest
                         |
           Evaluate scoped trace obligations
                         |
         traceability.sdn + traceability.md
```

## 13.2 Required run identity

An eligible run records at least:

| Category | Required identity/data |
|---|---|
| Subject | Repository and immutable source tree/input manifest; dirty/candidate distinction |
| Definitions | Selected test/suite/case IDs, parameter instances, definition digests |
| Execution lane | Interpreter/native/seed/self-hosted/backend identity, actual binary digest and provenance |
| Environment | OS/architecture, required device/provider identity, effective configuration revision |
| Inputs | Dependency/input-set manifest, fixtures, seeds, toolchain identities |
| Expectations | Reviewed expectation/applicability policy revision |
| Scope | Planned cases, selected features/requirements, required obligations |
| Observations | Per-case actual outcome, attempt ID, duration/resource data, artifacts |
| Completion | Terminal state, missing shards/cases, cancellation/infrastructure reasons |

Do not call a seed/interpreter result proof for a native or self-hosted lane. Record the actual admitted executable instead of assuming its identity from the command name.

For source compiled into a test binary, prove the binary's build-input relation to the source subject. A passing stale executable next to current source is not current-source evidence.

## 13.3 Definition coverage versus execution coverage

Report two separate measures:

```text
structural coverage = resolved applicable verification obligations
                      / all declared applicable verification obligations

verified coverage   = applicable obligations satisfied by eligible observations
                      / all declared applicable verification obligations
```

Count obligations, not file names or incidental edges. Each obligation identifies requirement/criterion, test kind, configuration scope, and its satisfaction rule. Multiple tests may be alternatives for one obligation or all mandatory; that distinction must be declared, never inferred from the presence of a passing case.

A denominator of zero is `not_applicable` only when applicability is established. Otherwise it is `undetermined`, not 100%. Shared tests count once per actual execution, even when they contribute to several distinct feature obligations.

## 13.4 Outcome and aggregation rules

A qualifying observation must match the required definition, source/input scope, configuration, expectation revision, execution lane, and provenance. The rules are intentionally conservative:

- `pass` without eligible provenance does not satisfy an obligation.
- `skipped`, `not_run`, `cancelled`, missing observations, and unfinished shards remain incomplete.
- A known expected failure is reported as such, not silently converted into a pass; whether a release tolerates it is an explicit policy decision.
- A retry retains all attempts. Choosing a later passing attempt cannot erase evidence of flakiness or a mandatory failure.
- A changed requirement or expectation invalidates its previous qualification unless an explicit reviewed equivalence/requalification rule permits reuse.
- A successful screenshot capture is not a correctness oracle. The comparison contract and its actual result must be recorded.

Use the existing typed-evidence model where its semantics fit, but make manifest admission mandatory before a renderer or viewer presents a verified badge. The current loader's unconditional rendering of parsed blocks is specifically insufficient for that badge. [R12]

## 13.5 Feature-level run behavior

When a feature/acceptance suite runs, the runner always emits a run-scoped SDN trace result and a Markdown report. Report generation occurs on failing as well as passing normal completion. A finalizer records interruption/incomplete state where possible; recovery after a hard crash must explicitly mark missing completion rather than invent success.

Executing acceptance tests alone does not execute their linked unit/integration/component tests. Default reporting therefore distinguishes **current-run**, **eligible previous evidence**, and **not executed / stale evidence**.

Illustrative result—not a measured Simple run:

| Verification layer | Linked definitions | Executed in this run | Eligible previous evidence | Current qualification |
|---|---:|---:|---:|---|
| Acceptance | 3 | 3 passed | 0 | Satisfied for selected acceptance scope |
| Unit | 8 | 0 | 0 | Not run |
| Integration | 2 | 0 | 0 | Not run |
| Component | 1 | 0 | 0; one stale historical record | Incomplete |

**Feature qualification: incomplete. Acceptance execution: passed.** Both statements are simultaneously true and must appear together.

An explicit “run required verification for this feature” mode plans and executes all applicable layers, subject to the host's capabilities. Missing GPU/FPGA/OS capabilities produce a visible unsatisfied/incomplete obligation or route an explicitly requested remote execution; they do not mark the feature complete locally.

## 13.6 Evidence reuse and freshness

Freshness is primarily input/provenance equivalence, not a wall-clock age threshold. Reuse a prior observation only when the complete declared input closure, definition, configuration, expectation, binary/build relation, and lane remain eligible.

The receipt may identify a different whole-repository commit only when a trusted equivalence calculation proves the required input subset unchanged and records that derivation. Unknown dependencies require conservative invalidation. Critical/release policies can require the exact candidate tree regardless.

An observation from an unstaged worktree cannot qualify a different staged candidate merely because the test file's name matches. Exact input comparison is required.

## 13.7 Feature lifecycle transitions

Do not automatically write `status=done` just because a run passed. Expose a computed `qualification` projection and a separately authored lifecycle state.

A controlled completion transaction requires:

```text
valid feature/requirement/criterion relationships
+ resolved implementation and verification obligations
+ eligible required execution evidence
+ current generated structural projections
+ reviewed applicability/exception policy
+ explicit authorized lifecycle transition
```

A subsequent relevant change can make qualification stale while preserving the historical fact that the feature was previously completed. Show “previously qualified; current changes require requalification,” not a rewritten historical run.

---

# 14. Generated traceability Markdown

## 14.1 Three document products

| Product | Generated when | Contents and update policy |
|---|---|---|
| Stable feature/component trace pages | Explicit generation or controlled publication; checked in remote admission when owned inputs change | Structural relationships, definition coverage, gaps, provenance. No unqualified latest PASS. |
| Run trace report | Automatically after every feature-level run, including failure/partial completion | Exact run subject, current execution results, eligible prior evidence, incomplete obligations, artifacts. |
| Repository trace index | Explicit generation/publication from the same graph | Feature/component navigation, structural summaries, unresolved/debt counts; links to immutable approved run reports where configured. |

Unit-only runs always emit structured run data; their Markdown can be optional unless policy requires it. Feature-level runs always emit both SDN and Markdown. Generating those artifacts must not rewrite all tracked documentation or require the user to stage a large report diff before committing unrelated code.

When a feature run finishes, its report contains the affected features' structural trace projection alongside run results. A separate maintenance command can promote deterministic structural pages into `doc/06_spec/trace/`; the test process itself does not silently change authored/committed files.

## 14.2 Feature page structure

Each generated feature page contains these sections in order:

| Section | Required content |
|---|---|
| Identity and provenance | Feature ID/title, structural input manifest, generator/rule versions, snapshot label |
| At a glance | Requirements, criteria, applicable test obligations, resolution gaps, qualification scope |
| Primary trace | Feature -> requirements -> AC/acceptance scenarios -> lower-level tests -> implementation |
| Requirement detail | Requirement text/anchor, each criterion, intended implementation, linked verification |
| Verification detail | Test kind, suite/case identity, parameters/config scope, inferred/explicit origin |
| Implementation detail | Component/layer, file/symbol locators, reverse requirement/test relationships |
| Supporting work | Research, plan, architecture, design, relevant decisions/bugs |
| Gaps and exceptions | Missing, ambiguous, stale, explicitly suppressed, or not-applicable obligations |
| Evidence | Only explicitly pinned run records and their eligibility; absent execution is visible |
| Regeneration | Generator command and input identity, without treating the command as executable document content |

An irregular link shows its reason and authoring location. A conventional link shows its mapping-rule identity without requiring a duplicate DB field.

## 14.3 Illustrative run-report excerpt

The following is a proposed rendered shape, not evidence of an executed run:

````markdown
# Traceability — Feature: Incremental Parser

Run: RUN-EXAMPLE-01
Source: exact source-manifest identity recorded in run.sdn
Scope: acceptance tests only
Run completion: complete for selected scope
Feature qualification: INCOMPLETE

## Requirement: REQ-PARSER-021

Unchanged syntax regions shall be reusable.

| Acceptance criterion | Acceptance SSpec scenario | Current run | Qualification |
|---|---|---|---|
| AC-PARSER-021-01 | unchanged blocks are reused | PASS | Selected acceptance obligation satisfied |
| AC-PARSER-021-02 | edited blocks are reparsed | PASS | Selected acceptance obligation satisfied |

## Trace to verification and implementation

| Kind | Definition | Relationship origin | Evidence in this run | Implementation target |
|---|---|---|---|---|
| Unit | incremental_spec / reuse unchanged block | convention: parser-unit-v1 | NOT RUN | incremental.spl |
| Unit | shared_cache_spec / preserve cache key | explicit: LINK-PARSER-09 | NOT RUN | cache.spl; incremental.spl |
| Integration | parser_module_spec / reparse module | explicit module mapping | NOT RUN | parser component |
| Component | frontend_spec / compile edited module | component manifest | NOT RUN | frontend component |

## Implementation

- incremental.spl — IncrementalParser.reuse_block
- cache.spl — ParseCache.lookup

## Supporting documents

Research: incremental parsing comparison
Design: cache invalidation and block reuse
Architecture: frontend component responsibilities

## Remaining obligations

Acceptance passed in this run. Unit, integration, and component obligations
have no eligible observations selected for this source/configuration.
This report does not claim those tests executed or the feature is complete.
````

Production output uses actual resolved links and source anchors rather than the example labels. A file-level target does not silently expand into claimed coverage of every symbol in that file.

## 14.4 Matrices and diagrams

Generate a compact matrix with explicit column meanings:

```text
Feature | requirement obligations | acceptance definitions | unit / IT / component
        | implementation links | unresolved links | qualified scope
```

Avoid a single “coverage score” that combines different denominators. A feature with ten test files and no eligible execution is not better-qualified merely because its inventory is larger.

Use the repository's existing SDN-diagram/manual infrastructure where compatible. For the initial trace pages, a deterministic ASCII flow plus a collapsible SDN source block is sufficient. Do not require a separate Mermaid-authored truth model. Both diagram geometry and prose tables come from the same graph projection.

Shared implementation nodes can appear as references in several feature pages, but aggregate execution totals deduplicate observation IDs. Reverse indexes link a component to every affected feature instead of assigning it to one arbitrary owner.

## 14.5 Determinism and safe publication

Stable pages omit wall-clock generation timestamps that would change on every run. Include only stable input identities and meaningful content changes. Run-specific reports may include their recorded run times.

Generate into a temporary output root, compare against the expected manifest, then publish only owned files. `--check` compares without rewriting. Remove obsolete generated pages only when the prior generator manifest proves ownership; never delete neighboring human documents by a directory wildcard.

Run reports link to immutable source snapshots and artifact IDs. Structural pages can use revision-resolved relative navigation through their publication manifest. Do not emit absolute local machine paths as portable source links.

A failed renderer must not erase the original test result. Record `report_generation_failed` as an additional infrastructure error and retain the run SDN/evidence that was successfully persisted. Feature-run completion requires the required artifacts to be available or the failure to be explicit.

---

# 15. Static HTML publication

## 15.1 Scope

Provide a static site projection for users who need browsable traceability without a running Slop service. It is a snapshot, not a live monitor.

```text
target/trace-site/<publication-id>/
    index.html
    feature/<feature-id>.html
    component/<component-id>.html
    source/<artifact-id>.html
    data/manifest.sdn
    data/nodes-<partition>.sdn
    data/edges-<partition>.sdn
    assets/...
```

Generate HTML directly from the shared projection model. Do not parse generated Markdown back into another trace database. Optional search/filter code consumes SDN data using the same versioned semantic contract.

## 15.2 Offline and server-hosted modes

A server-hosted static export can retrieve SDN shards as text. For `file://` use, package the needed data in escaped inert HTML text/template content or pre-render all essential navigation so browser fetch restrictions do not make the export unusable. Do not use JSON data islands or encode the graph as executable JavaScript object literals.

The artifact visibly declares its publication/input identity, source scope, and evidence selection. It never substitutes a moving branch's source code under a historical passing test.

## 15.3 Publication security and privacy

Escape code and metadata as text. Sanitize rendered Markdown; disable active document directives and arbitrary embedded scripts. Repository content must not become executable viewer code merely because it appears in a generated manual.

Publication policy selects which source/evidence is included. A local private-source view does not authorize exporting that source into a public site. Default exports omit credentials, machine-local paths, and raw environment values; display redacted environment identity and availability indicators instead.

Static publication is optional for initial admission. The underlying SDN and Markdown report remain useful without any server or graphics dependency.

---

# 16. Slop viewer interaction design

## 16.1 Name and entry point

Use **slop viewer** as the product/UI name. The proposed integrated CLI entry is:

```text
simple slop viewer
```

This report does not assume an existing Slop executable. A standalone launcher can be added later as an alias; the first implementation should not duplicate CLI/configuration ownership.

## 16.2 Three-pane workspace

```text
+-------------------------+-------------------------------------------------------+
| TREE / SEARCH           | TRACE / LAYER VIEW                                    |
|                         |                                                       |
| Project                 | Feature -> Requirement -> AC / SSpec -> Tests -> Impl |
|   Compiler              |                                      + Unit           |
|     Parser              |                                      + Integration    |
|       Incremental       |                                      + Component      |
|       Error recovery    |                                                       |
|   UI                    | Supporting research / design / architecture: folded   |
|   SimpleOS              +-------------------------------------------------------+
|                         | DETAIL                                                |
| View by:                | Identity | Attributes | Relations | Evidence          |
| Feature                 | Source | Documentation | History                      |
| Component / Layer       |                                                       |
| Requirement / Test      | Selected symbol / scenario / requirement content      |
| Source                  | Exact revision, location, provenance, unresolved gaps |
+-------------------------+-------------------------------------------------------+
| Snapshot: candidate / committed / historical | Graph state | Scope | Diagnostics |
+---------------------------------------------------------------------------------+
```

Initial proportions: approximately 22% width for the left tree, with the remaining area split roughly 60/40 between graph and detail. These are resizable defaults, not fixed pixel requirements. Persist layout in user-local SDN preferences.

## 16.3 Left tree: MDSOC-aware navigation

Default grouping is project -> component/group -> feature. Alternative roots provide feature, architectural layer, component/entity, transform, requirement, test, and source views over the same canonical nodes.

A feature spanning compiler, runtime, and UI appears as one feature with relationships to those dimensions. A shared component may appear under multiple tree branches as an alias/reference; selecting it always resolves to the same canonical identity.

Tree rows expose status text and counts for unresolved links or incomplete obligations. Do not hide orphaned tests or implementation files simply because they have no feature parent. Provide explicit “Unassigned / unresolved” roots.

Search supports IDs, titles, symbol names, paths, and exact relationship queries. Search results include kind, component/layer, revision context, and the reason they matched. No LLM or network access is required.

## 16.4 Upper-right: layered graph

The default Trace mode uses stable phases:

```text
Feature | Requirement | AC + acceptance scenario | Unit / IT / component | Implementation
```

Research, plan, architecture, and design are folded branches or an optional supporting-document column. The visual phase order is a navigation aid; actual edges retain their typed semantics. Do not draw an invented `acceptance -> unit` edge when both tests are independently linked to the same criterion.

Group source symbols under files/components and tests under suites, with expandable counts. Use edge labels such as `accepted_by`, `verified_by`, `targets`, and `implemented_by`. Display inferred associations distinctly from execution-backed facts. Status must be available as text/icon and not color alone.

For large graphs, open a bounded neighborhood of the selected feature, summarize hidden groups, and expand on demand. Never silently truncate and present the remainder as complete. Display “200 of 4,300 nodes in selected scope shown” when a display limit applies.

Use stable tie-breaking and preserve node positions across small updates. Directional layering and compound groups are supported ideas in ELK's published layout model; the initial implementation can use a simpler native deterministic layout without adopting ELK's runtime. [W12]

## 16.5 Lower-right: inspector and source

| Tab | Content |
|---|---|
| Identity | Canonical ID, kind, owning declaration, snapshot/semantic revision |
| Attributes | Feature status, component/layer, configuration/applicability, artifact properties |
| Relations | Typed incoming/outgoing edges; explicit/inferred origin; replacement/suppression reason |
| Evidence | Current-run observations, eligible previous observations, stale/rejected evidence and reasons |
| Source | Revision-pinned source/SSpec, symbol or scenario span, line numbers and syntax presentation |
| Documentation | Requirement/research/design/architecture section text and links |
| History | Identity/alias transitions and approved run/publication history |

Source content is read lazily for the selected artifact. A node from snapshot A must not show source from snapshot B under the same title. The inspector header always shows the source identity and whether the view is committed, candidate, worktree, or historical.

Source display is initially read-only. “Open in editor” is an explicit action with validated location. Editing trace declarations or code later must route through the existing SJ/refactoring transaction owner, not a private Slop writer.

## 16.6 Essential navigation actions

Support forward trace, reverse impact, go to implementation, go to test, go to requirement, inspect mapping origin, compare snapshots, and open a pinned run.

The reverse-impact view answers: **“Which features, requirements, verification obligations, and published pages may be affected by this source/policy change?”** It reports dependency-derived impact, not an unsupported assertion that all affected behavior is broken.

Selecting an acceptance scenario highlights its requirement/criterion, related verification obligations, eligible evidence, and implementation targets. Selecting a shared implementation node highlights every related feature, not just its first tree parent.

## 16.7 Architecture/design expansion

Later modes reuse the same identities and inspectors:

| Mode | Main projection |
|---|---|
| Trace | Feature -> requirement/AC -> tests -> implementation |
| Architecture | System -> component/layer -> interface/transform seam |
| Design | Feature -> design section -> types/functions and constraints |
| Dependencies | Actual import/call/data dependency edges with scope/provenance |
| Evidence | Scenario -> execution lane/provider -> observation/artifact |

Architecture layer order and permitted dependency direction are different from trace lifecycle order. Slop must not suggest that a trace relationship authorizes a cross-layer import. Transform boundaries and reexports remain governed by the existing MDSOC rules.

Do not introduce full editing, arbitrary workflow execution, or runtime tracing into the first viewer milestone. Deliver navigation and truthful source/evidence inspection first.

## 16.8 Keyboard and accessibility

Use standard tree navigation: arrows for movement/expansion, Home/End for bounds, type-ahead, and a documented activation key. Keep focus distinct from selection and preserve focus across graph refreshes. Provide a relationship-table alternative to the graph and keyboard-accessible pane switching. W3C's tree-view pattern is the reference. [W13]

Long source files and trees are virtualized without losing logical focus/location. Respect reduced-motion preferences; animations must not move the selected target away during inspection.

---

# 17. Slop implementation and SDN protocol

## 17.1 Kernel and adapters

Slop uses a pure presentation transform over `TraceGraph` plus effectful source/query adapters. Rendering backends do not parse repository files or resolve competing declarations themselves.

```text
TraceGraph + selected scope + view preferences
                       |
                View-model transform
                       |
       TreeModel + LayeredGraphModel + DetailModel
                       |
           Existing Simple UI adapters
```

Reuse existing Simple UI/renderer facilities after an API inventory; do not assume that every necessary tree/source widget already exists. Keep UI providers optional so the trace CLI and hooks never load graphics, browser, or device-runtime dependencies.

The native viewer is the first interactive surface. A later browser-hosted surface uses the same projection and SDN contract. No separate browser-owned graph authority is introduced.

## 17.2 Layout algorithm

Start with phase/layer assignment from typed node kinds, then compound component/suite groups. Order nodes deterministically using stable IDs and local crossing reduction; preserve prior positions where a small delta permits it. Route visible edges through labeled ports and summarize edges to folded groups.

Cycles in a dependency projection are presented as strongly connected groups or explicit back-edges. Do not force the underlying trace graph to become acyclic just to satisfy a diagram renderer.

Layout runs outside the input/UI thread. Cancel superseded work and publish one consistent view generation. Large fan-out nodes initially expand to grouped summaries, not thousands of individual source symbols.

## 17.3 SDN request/response model

Native in-process clients call typed APIs; remote/local-service clients serialize the same requests as SDN. Suggested operations are `open_snapshot`, `query_nodes`, `query_relations`, `read_source`, `explain`, `impact`, and `subscribe`.

```sdn
schema:
    name: "simple.slop.message"
    version: 1

request:
    id: "request-17"
    operation: "query_relations"
    snapshot: "snapshot-42"
    entity: "req:REQ-TRC-004"
    direction: "both"
    limit: 200
```

A response carries request ID, snapshot identity, completeness, result tables, and an opaque continuation token when more results exist. `read_source` accepts an admitted artifact ID and range, not an arbitrary operating-system path. Validate all bounds and maximum response sizes.

For HTTP, use UTF-8 text bodies with an explicit SDN schema marker; do not claim an unregistered MIME type is a standard. For a WebSocket transport, one text message contains one complete SDN message. Native IPC may use length-delimited SDN frames. Binary source artifacts remain separate hashed artifacts, not a second structured graph format.

## 17.4 Live updates and recovery

A delta names its base snapshot/generation and sequence. Apply it only to the matching complete base. Publish node/edge changes and removals atomically; preserve referential integrity within the completed generation.

If messages are lost, duplicated inconsistently, or arrive against another base, request a fresh snapshot. Never patch by best effort and display a partially mixed graph as current.

The index service may debounce file events, but notifications are hints. Confirm the exact content snapshot before rebuilding. On parse failure, Slop can retain the last-good view with a conspicuous **“last valid snapshot; current inputs invalid”** banner and current diagnostics. Old green badges must not appear to describe the invalid worktree.

Local live indexing runs only while the user has started the viewer/service. No daemon, network listener, or background scan is required for hooks or static reports.

## 17.5 Service security

Default to read-only local access. A loopback service still requires origin checks and a session authorization mechanism for browser clients; binding to localhost alone is not a complete access policy. Disable remote binding unless explicitly configured.

No arbitrary shell commands, file writes, URL fetching, plugin loading, or path traversal are accepted through a node attribute. Treat repository metadata and Markdown as untrusted display content. Export/publish actions require explicit authorization and the applicable visibility policy.

Optional extensions declare capabilities and consume the public graph API. They cannot replace the admission evaluator, inject verified outcomes, or bypass the single-writer boundary.

---

# 18. Proposed command contracts

**All commands/options in this section describe the target interface. They are not a claim of current CLI availability.** Extend existing commands rather than installing a parallel checker with different rules.

| Operation | Proposed invocation | Result |
|---|---|---|
| Minimum staged check | `simple traceability-check --snapshot=index --profile=commit` | SDN scoped verdict |
| Exact revision/push check | `simple traceability-check --snapshot=git:<head> --base=<base> --profile=push` | SDN affected-closure verdict |
| Trusted remote check | `simple traceability-check --snapshot=git:<candidate> --base=<base> --profile=remote` | SDN admission result |
| Full audit | `simple traceability-check --snapshot=git:<revision> --profile=audit --rebuild` | SDN complete structural audit |
| Explicit cache refresh | `simple trace index --snapshot=git:<revision>` | Complete derived SDN snapshot |
| Explain a link or gap | `simple trace explain <entity-id> --snapshot=<snapshot-id>` | SDN origins, rules, unresolved obligations |
| Reverse impact | `simple trace impact <entity-id> --snapshot=<snapshot-id>` | SDN affected entities and dependency reasons |
| Generate stable pages | `simple trace docs --snapshot=<snapshot-id> --output=doc/06_spec/trace` | Markdown files plus SDN output manifest |
| Check generated pages | `simple trace docs --snapshot=<snapshot-id> --output=doc/06_spec/trace --check` | Read-only comparison; SDN diagnostics |
| Regenerate run report | `simple trace report --run=<run-id>` | Pinned SDN/Markdown run projection |
| Acceptance run | `simple test <feature-spec>` | Tests plus automatic feature-run SDN and Markdown |
| Full requested feature verification | `simple test --feature=<feature-id> --verification=required` | Planned/actual required cases; truthful capability failures |
| View | `simple slop viewer --snapshot=<snapshot-id>` | Three-pane interactive viewer |
| Export HTML | `simple trace site --snapshot=<snapshot-id> --output=<directory>` | Read-only static publication plus SDN manifest |

The hook adapter supplies all ref-update rows through a typed SDN request to the checker or typed API to the shared driver. A single `--base/--head` example is not the multi-ref protocol.

Default structured stdout is SDN. Human progress belongs on stderr; a quiet mode suppresses progress, not the verdict. `--help` is ordinary help text. Markdown/HTML generation writes files and returns an SDN manifest; it does not interleave prose with structured output.

There is no JSON-format option. Legacy callers receive an actionable unsupported-format error until migrated. Do not silently honor an obsolete flag or fall back to another encoding when SDN serialization fails.

## Exit semantics

| Exit | Meaning |
|---|---|
| `0` | Selected mandatory scope completed and satisfied; may explicitly report no relevant changes |
| `1` | Completed evaluation found policy/trace/test violations |
| `2` | Required evaluation/reporting could not complete: invalid input, missing prerequisite, infrastructure failure, or budget exhaustion |
| `130` | Interrupted/cancelled operation, with incomplete result where recoverable |

The SDN result preserves underlying test outcomes and infrastructure/reporting errors even when one aggregate exit code is returned. A feature can pass selected tests while the command's required qualification/reporting contract fails; that distinction must remain inspectable.

Before installing new hook invocations, verify the deployed source-matched binary supports the new schema and commands. CLI-help presence alone is not a successful execution test.

---

# 19. Performance and resource contracts

These are **proposed benchmark acceptance targets, not measurements obtained during this audit**.

| Workload | Initial target | Conditions |
|---|---|---|
| Commit trace check | p95 <= 500 ms; p99 <= 1 s | Warm admitted index, <=25 changed relevant files / <=2 MiB input, bounded component closure |
| Push trace increment | p95 <= 2 s | Warm index, ordinary affected-feature closure |
| Entire local push gate | Preserve the adopted short-gate budget; target <=10 s for normal workloads | Includes existing safety checks; trace is not allowed a separate unbounded allowance |
| Required remote trace step | <=5 s warm processing contribution | Excludes runner queue/checkout; broader changes explicitly escalate |
| Required remote lane | Target <=60 s normal processing | End-to-end timings measured separately; current configured 240 s budget is not a benchmark |
| Feature trace report | <=2 s for 1,000 case observations | Excludes test execution and large artifact transfer |
| Slop interaction | Visible response within 150 ms for already-loaded selections | Source/layout work asynchronous, cancellable; bounded visible graph |
| Slop initial graph | Display a useful grouped neighborhood, initially <=200 visible nodes | Expanding a large graph is explicit; completeness counts remain visible |

Index/CLI startup memory and source-import closure are first-class measurements. Reuse immutable parsed facts across worker tasks, partition mutable work, and avoid per-file processes. The default trace CLI must not import UI, compiler-codegen, GPU, or test-execution dependencies merely to check metadata.

Measure Linux, macOS, and Windows separately with identified hardware, storage, binary/lane, dataset, and sample count. Record cold/warm runs, at least 30 repeated ordinary samples, p50/p95/p99, source files/bytes touched, peak memory, cache hit rate, and actual closure size. Include shared/high-fan-out changes and deliberately cold cache fixtures.

Do not run the checker's complete self-test suite on every hook invocation. The existing gate registry documents cases where per-invocation self-tests consumed much of a short hook budget; self-tests belong in checker admission and CI. [R08]

A deadline is a correctness boundary: timeouts produce incomplete/non-green results. Large work is performed explicitly outside the hook or in the authoritative expanded remote lane, never silently abandoned.

---

# 20. Diagnostics, baseline debt, and exceptions

## 20.1 Diagnostic contract

Retain existing useful `TRC*` meanings during migration. Allocate new names/codes through one registry; do not reuse an old code with a new meaning.

Proposed diagnostic names include:

| Name | Condition |
|---|---|
| `TRACE-SDN-SCHEMA` | Invalid/incompatible SDN schema or fields |
| `TRACE-DUPLICATE-ID` | Identity resolves to competing declarations |
| `TRACE-MISSING-ENDPOINT` | Referenced entity/path/symbol unavailable |
| `TRACE-AMBIGUOUS-MAPPING` | Conventional mapping has several candidates |
| `TRACE-STALE-OVERRIDE` | Explicit replacement no longer matches its named rule/scope |
| `TRACE-AUTHORITY-CONFLICT` | Two authored owners disagree on a semantic declaration |
| `TRACE-UNSATISFIED-OBLIGATION` | Required criterion/test-kind/config obligation unresolved |
| `TRACE-EVIDENCE-INELIGIBLE` | Observation does not match subject/config/lane/provenance |
| `TRACE-SNAPSHOT-INCOMPLETE` | Required facts could not be constructed |
| `TRACE-PROJECTION-DRIFT` | Owned generated document differs from current inputs |
| `TRACE-UNTRUSTED-CHECKER` | Executable/policy/status provenance not admitted |

Each diagnostic includes severity, entity, source path/span where known, input snapshot, rule version, reason, and a concrete repair direction. Sort deterministically. Do not hardcode all diagnostics to line 1 when an exact parsed declaration span is available.

## 20.2 Progressive enforcement

Existing debt cannot be solved by commenting out every source root indefinitely. Roll out by supported mapping roots and affected features:

- Always reject newly introduced malformed data, identity conflicts, false verified claims, and unsafe policy changes.
- Ratchet existing unresolved structural debt using stable diagnostic/entity/input fingerprints.
- Enforce complete semantics for newly onboarded features and explicit lifecycle-completion transitions.
- Promote additional roots after their mapping conventions and irregular links are normalized.

A baseline entry identifies exactly what debt was accepted and under which policy. It expires when the underlying declaration changes or the issue disappears. Do not permit a stale baseline to suppress a new problem at the same path.

Exceptions record owner, rationale, applicable obligation/configuration, review/expiry condition, and approval provenance. They can establish reviewed non-applicability or tolerated debt; they cannot change an actual failed observation into a passed one.

---

# 21. Implementation work packages

## 21.1 Dependency sequence

```text
WP0 baseline / trust / measurements
             |
WP1 shared model + SDN + identity contracts
             |
      +------+------+
      |             |
WP2 extraction   WP4 runner/evidence adapter
      |
WP3 incremental snapshots / local+remote gate integration
      |             |
      +------+------+
             |
WP5 Markdown / static HTML projections
             |
WP6 Slop viewer MVP
             |
WP7 architecture/design views + distributed evidence adapters
```

This sequence permits parallel work after interfaces are fixed, but shared codec, graph semantics, and DB-writer ownership remain single responsibilities.

## 21.2 Concrete delivery packages

| Package | Principal changes | Exit criterion |
|---|---|---|
| **WP0: verified baseline** | Pin checkout and relevant settings; inventory current trace/DB/docgen call sites; record actual hook execution on hosts; measure current costs; identify trusted-checker deployment route | Reproducible baseline with no claims based solely on old reports |
| **WP1: model/SDN** | Proposed `common/traceability` model, schema-aware codec, typed IDs/edges/obligations, deterministic diagnostics; remove native legacy-format callers in this path | Codec round trips and reject fixtures; all structured outputs are SDN |
| **WP2: extract/resolve** | Adapt current trace parser, feature DB, SSpec metadata, source/module index, explicit mapping shards; reference/authority checks; negative lookup registry | End-to-end feature graph with conventional and irregular links, no semantic substring false greens |
| **WP3: incremental/admission** | Snapshot providers, dependency invalidation, cache manifests, existing hook/registry integration, trusted remote executable and policy, candidate/event resolution | Incremental/full equivalence; exact staged/multi-ref tests; candidate cannot weaken admission |
| **WP4: runner/evidence** | Extend `test_db_compat` and unified DB owner; immutable subject/config/case records; formal SDN evidence sidecars; provenance admission | Feature acceptance-only run honestly shows lower layers not run; crash/failure records persist |
| **WP5: projections** | Shared structural/run projection; feature/component indexes; deterministic owned-page publication; optional offline HTML | Same relationships and eligibility in SDN, Markdown, and HTML; no accidental tracked run churn |
| **WP6: Slop MVP** | Three-pane workspace; MDSOC tree; layered graph; source/details/evidence inspector; read-only snapshot service | All basic navigation works without duplicate graph logic; exact-revision source and stale-state behavior |
| **WP7: extensions** | Architecture/design/dependency projections, approved publication into future `simple-data`, optional remote/browser adapters | New views reuse existing identities/edges and cannot alter admission authority |

## 21.3 Existing edit points versus proposed modules

| Existing path | Intended change |
|---|---|
| `src/app/traceability/main.spl` | SDN-only frontend, snapshot/profile selection, shared evaluator |
| `src/app/traceability/_TraceabilityCore/` | Extract reusable rules; replace filesystem-only collection with snapshot adapter; preserve tests while migrating |
| `config/traceability.sdn` | Versioned mapping, ownership, profile, applicability, and enforcement configuration |
| `src/app/tracking/main.spl` | Schema-aware readers and shared graph validation; no independent nonblank-only qualification |
| `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl` | Single-writer run/evidence extension and migration boundary |
| `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl` | Real SDN loader, versioned legacy import, provenance-aware rendering eligibility |
| `scripts/hooks/pre-commit` | Minimum exact-snapshot trace step; remove broad generation from this step |
| Existing pre-push dispatcher/driver | One shared trace gate; preserve ref capture/chaining/recursion safety |
| `config/check/must_check_gates.sdn` | Register bounded trace work and appropriate full-audit tier |
| `.github/workflows/required-gates.yml` | Trusted admission integration and explicit event/subject resolution |
| Existing traceability guide | Explain omitted conventional links, irregular declarations, run reports, scope and commands |

New `src/lib/common/traceability/` and `src/app/slop/` package layouts are proposals, not an assertion those modules currently exist. Select their final placement after import-boundary checks. Avoid a one-step wholesale rewrite of the current checker.

## 21.4 First vertical slice

Use the traceability feature itself as the first onboarded feature: its requirement declarations, focused tooling SSpec, CLI-facing test, implementation module, and generated page. Its tooling-test placement is a useful irregular-link fixture rather than forcing a mass repository move.

Complete the slice from a changed requirement through graph diagnostics, a real selected test run, emitted SDN/Markdown, and Slop source navigation before expanding to compiler/UI/OS roots. This proves integration more effectively than creating hundreds of empty feature records.

## 21.5 Deliverable documentation

Publish concise maintained documents extracted from this report, without duplicating authority:

```text
doc/04_architecture/infra/traceability.md        model, ownership, trust boundaries
doc/05_design/infra/traceability_graph.md        schemas, resolution, invalidation
doc/05_design/app/slop_viewer.md                interaction and projection contracts
doc/07_guide/infra/traceability.md               authoring and everyday commands
```

The final report remains the decision/audit record. The guide is the operational entry point; generated feature trace pages are the navigable evidence of adoption.

---

# 22. Verification and acceptance matrix

**The following are planned verification cases, not tests executed during this report.** Use unit tests for pure rules, integration tests for adapters/transactions, component tests for complete subsystems, and feature SSpec for user-observable behavior. Actual test-kind placement follows the admitted repository classifier rather than introducing an arbitrary new numbered root.

| AC ID | Required scenario | Level | Requirements |
|---|---|---|---|
| AC-TRC-001 | SDN round-trip preserves quoted commas, Unicode, ordered rows, empty/absent values, and integer boundaries | Unit | 001, 018 |
| AC-TRC-002 | Unknown schema/duplicate columns/invalid enum fails; legacy structured-format flags are rejected | Unit + CLI | 001, 007 |
| AC-TRC-003 | Adding source and its conventional unit spec creates an edge with no authored DB diff | Integration | 004 |
| AC-TRC-004 | Shared test adds two explicit targets without duplicate test identity | Integration | 005, 016 |
| AC-TRC-005 | Adding a second conventional candidate invalidates a previously unique cached mapping | Unit + Integration | 006, 017 |
| AC-TRC-006 | Replacing a mapping applies only to the named rule/scope; stale replacement fails | Unit | 005, 006, 019 |
| AC-TRC-007 | Requirement ID inside a quoted example does not become an accepted-by relationship | Unit | 002, 013 |
| AC-TRC-008 | Adding a previously missing declaration invalidates a negative lookup and clears the correct diagnostic | Unit | 007, 017 |
| AC-TRC-009 | Duplicate ID, deletion, and cross-directory rename invalidate unchanged incoming references | Integration | 006, 017 |
| AC-TRC-010 | Staged broken/unstaged fixed content fails; staged fixed/unstaged broken content is judged correctly | Integration | 008 |
| AC-TRC-011 | Alternate index, linked worktree, spaces/non-ASCII paths, and case collisions use the right subject | Integration | 008, 009 |
| AC-TRC-012 | Multi-ref push with one bad ref fails the aggregate; child tools cannot consume ref rows | Integration | 009 |
| AC-TRC-013 | New/deleted/non-fast-forward branches and protected tags are handled explicitly | Integration | 009, 011 |
| AC-TRC-014 | Git, supported jj routes, and SJ publication each reach the same validator with the correct candidate | Component | 008, 009 |
| AC-TRC-015 | Missing binary/cache, timeout, failed object read, and unsupported schema cannot return clean | Integration | 010 |
| AC-TRC-016 | Existing pre-push optimized and generic dispatch paths both run the new mandatory trace gate | Component | 010, 011 |
| AC-TRC-017 | Candidate replaces runner/gate script with a no-op; trusted remote admission still detects violation | Security integration | 011 |
| AC-TRC-018 | Candidate edits exclusions/baseline/manifest; unapproved policy cannot admit itself | Security integration | 011, 019 |
| AC-TRC-019 | No-relevant-change case runs the required job and emits a complete scoped result | Component | 010, 011 |
| AC-TRC-020 | PR/merge candidate/merge-group/post-main events cannot reuse the wrong SHA or exit early as verified | Component | 011 |
| AC-TRC-021 | Acceptance-only passing run emits SDN/Markdown with linked unit/IT/component tests still not run | Feature SSpec | 012, 013 |
| AC-TRC-022 | Zero discovered cases with planned cases, missing shards, cancellation, and crash remain incomplete | Component | 012, 013 |
| AC-TRC-023 | Changed source/test/config/expectation/binary lane rejects a stale receipt; same eligible input set can reuse one transparently | Integration | 013, 018 |
| AC-TRC-024 | Forged status or well-shaped digest without matching artifact/provenance cannot produce verified evidence | Security integration | 011, 013 |
| AC-TRC-025 | Retry keeps failed attempts; expected failures and unexpected passes remain distinguishable | Unit + runner | 013 |
| AC-TRC-026 | Legacy evidence imports preserve history without granting missing provenance | Integration | 001, 018 |
| AC-TRC-027 | Interrupted DB migration or concurrent update preserves one valid owner and no lost links | Integration | 018 |
| AC-TRC-028 | Incremental graph equals full rebuild through randomized edits, rule changes, aliases, and deletions | Property + Integration | 017 |
| AC-TRC-029 | Repeated structural generation is byte-identical; run timestamps do not churn stable pages | Integration | 014 |
| AC-TRC-030 | Committed generated-output identity avoids self-referential tree-hash regeneration loops | Integration | 014 |
| AC-TRC-031 | Feature Markdown exposes each requirement/AC, verification kind, implementation target, and irregular origin | Feature SSpec | 002–007, 014 |
| AC-TRC-032 | Offline HTML works without a server; malicious source/Markdown cannot execute in the viewer | Component + Security | 020 |
| AC-TRC-033 | Selecting a shared component in any tree branch selects the same graph node and detail identity | Feature SSpec | 015, 016 |
| AC-TRC-034 | Selecting historical evidence opens historical source, not the moving worktree file | Feature SSpec | 015, 020 |
| AC-TRC-035 | Lost/mismatched SDN delta forces resync; parse errors show last-valid status rather than current green | Component | 015, 020 |
| AC-TRC-036 | Tree/pane/source navigation works keyboard-only and preserves focus during refresh | Feature SSpec | 015 |
| AC-TRC-037 | UI and graph limits expose hidden counts; no display truncation changes qualification | Component | 013, 015 |
| AC-TRC-038 | Warm/cold/high-fan-out workloads produce measured latency/resource receipts and obey budgets | Performance | 010, 017 |
| AC-TRC-039 | Completed feature transition requires all applicable obligations and authorization; later edits invalidate current qualification | Feature SSpec | 002, 013, 019 |
| AC-TRC-040 | Source/evidence export respects visibility policy and never exposes arbitrary filesystem paths | Security integration | 020 |

The requirement column uses numeric suffixes of `REQ-TRC-*`; the range in AC-TRC-031 means requirements 002 through 007. The test implementation should store explicit associations, not parse this human table as the authoritative association source.

At least one complete feature SSpec must intentionally exercise the real production extractor/resolver/runner/reporting path. Pure in-memory fixtures remain useful unit tests but cannot alone prove CLI/hook integration or a deployed binary's behavior.

---

# 23. Rollout, risks, and completion criteria

## 23.1 Rollout gates

**Stage A — observe and compare:** keep existing enforcement; build the shared graph in shadow mode and compare known legacy relationships. Establish current baseline measurements and trusted remote execution.

**Stage B — enforce new declarations:** require valid SDN, identities, explicit exceptions, and correct snapshots for the first onboarded features. Move broad generation out of the minimum commit path only when replacement checks demonstrably preserve required protection.

**Stage C — make reporting automatic:** enable run-scoped SDN/Markdown for feature tests; migrate evidence encoding and test DB ownership. Historical records remain labeled by their actual validity.

**Stage D — widen structural enforcement:** admit more source/test mapping roots, shrink baseline debt, and enable deterministic stable-page checks for owned outputs. Keep full audits for uncertain scope.

**Stage E — viewer/publication:** deliver Slop's read-only tree/graph/source slice, then optional HTML publication and architecture/design modes. No extra graph parser or writer may be introduced during UI work.

## 23.2 Principal risks

| Risk | Mitigation |
|---|---|
| Hook latency recreates existing frustration | Batch reads, reusable facts, negative-dependency indexing, small CLI closure, measured budgets |
| Inferred links overstate verification | Distinct structural origin, actual outcome, evidence validity, and obligation evaluation |
| Metadata migration loses relationships | Single authority per declaration group, old/new graph comparison, transactional transfer |
| Candidate weakens its own gate | Trusted control plane, checker, dependencies, policy, and expected status producer |
| A stale binary appears to verify current source | Execution/build-input provenance and lane-specific eligibility |
| Full-graph cache becomes a second source of truth | Disposable derived generations, validated input manifests, rebuild equivalence |
| Generated documentation causes large commits | Stable structural pages separate from local immutable run reports |
| Slop shows a misleading clean snapshot | Explicit current/last-valid state, revision-pinned source, complete-generation publication |
| Distributed DB work delays useful delivery | Local SDN MVP with preserved SCV/SJ identity/mutation seams |

## 23.3 Definition of complete

The first release is complete only when an onboarded feature can be followed from requirement/research to acceptance, lower-level verification, and implementation; a conventional unit mapping needs no duplicate declaration; an irregular mapping is explained; a real feature run emits truthful SDN/Markdown; local and remote gates inspect exact candidates; and Slop displays the same relations, gaps, evidence, and source revision.

Completion additionally requires the negative fixtures in Section 22, measured hook budgets on supported hosts, an admitted source-matched CLI, and a verified remote required-check configuration. A generated page, an implemented data type, or a passing isolated comparator is not sufficient by itself.

**Final recommendation:** unify the existing checker, tracking DB, test-run/evidence owner, and generators around the shared graph. Deliver the fast exact-snapshot gate and truthful feature-run report before broad UI expansion. Keep SDN exclusive, inferred links nonredundant, and every verification claim tied to actual eligible evidence.

---

# 24. Source register

## Repository evidence

Repository file references below are pinned to the audited revision. The ruleset reference is a settings snapshot read on 2026-10-03 and may change independently of source history. Some reads covered focused ranges rather than whole files; the findings in Section 2 are limited accordingly.

| Reference | Source and use |
|---|---|
| [R01] | Audited commit and revision boundary |
| [R02] | Traceability configuration; source roots are opt-in |
| [R03] | Collector/extractor, inspected lines 170–295; accepted file types and text-based IDs |
| [R04] | Feature DB, inspected header and first sampled rows; lifecycle columns and incomplete sample data |
| [R05] | Tracking CLI, inspected lines 92–146; nonblank/positional done checks |
| [R06] | Pre-commit, inspected lines 68–146; generation and full-scope checks |
| [R07] | Pre-push canonical guard, inspected lines 1–180; exact refs, bounded dispatcher, receipt boundary |
| [R08] | Mandatory gate registry, inspected opening section; existing tiers, budgets, and admission integration |
| [R09] | Current required workflow; sparse checkout, event handling, BASE manifest and candidate-code trust gap |
| [R10] | Hygiene workflow, inspected opening section; required-job relocation and advisory scope |
| [R11] | Active main/integration ruleset, API read; required contexts and policy |
| [R12] | Evidence loader, inspected complete short file; custom sidecar format and render admission gap |
| [R13] | Test DB compatibility layer, inspected lines 1–120; shared writer and run integration seam |
| [R14] | Distributed textual DB design, inspected opening section; design-only status, SCV/SJ/test-DB direction |

## Primary external research

| Reference | Source | Applied design lesson |
|---|---|---|
| [W01] | StrictDoc user guide | Textual intent, explicit relationships, generated trace/source navigation |
| [W02] | Build Systems à la Carte, original research publication page | Separate dependency discovery, scheduling, and reuse |
| [W03] | Rust compiler incremental compilation guide | Dependency-aware fingerprints rather than last-good booleans |
| [W04] | Git hook reference | Exact hook subjects, ref rows, bypass and server-hook distinctions |
| [W05] | Git diff-index reference | Index/cached snapshot semantics |
| [W06] | Git cat-file reference | Batch immutable object access |
| [W07] | Jujutsu configuration reference | Verify actual Git-subprocess/publication behavior rather than assume hook coverage |
| [W08] | GitHub protected branch documentation | Required checks and expected-source policy |
| [W09] | GitHub required-status troubleshooting | Current revision, skipped-state pitfalls, mandatory-job aggregation |
| [W10] | GitHub Actions event reference | PR and merge-group subject/event distinction |
| [W11] | GHES pre-receive-hook documentation | Administrator-controlled server-side admission option |
| [W12] | Eclipse ELK Layered reference | Directional layers, compound groups, explicit routing |
| [W13] | W3C WAI-ARIA tree-view pattern | Keyboard operation and focus/selection semantics |

[R01]: https://github.com/ormastes/simple/commit/02f6687d846ba55faea4a08c44e4a3c0982a488d
[R02]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/config/traceability.sdn
[R03]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/src/app/traceability/_TraceabilityCore/config_and_analysis.spl#L170-L295
[R04]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/doc/08_tracking/feature/feature_db.sdn#L1-L8
[R05]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/src/app/tracking/main.spl#L92-L146
[R06]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/scripts/hooks/pre-commit#L68-L146
[R07]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/scripts/check/pre-push-conflict-tree-guard.shs#L1-L180
[R08]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/config/check/must_check_gates.sdn
[R09]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/.github/workflows/required-gates.yml
[R10]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/.github/workflows/repo-hygiene.yml#L1-L180
[R11]: https://github.com/ormastes/simple/rules/21573643
[R12]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/src/app/spipe_docgen/spipe_docgen/evidence_loader.spl
[R13]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/src/lib/nogc_sync_mut/test_runner/test_db_compat.spl#L1-L120
[R14]: https://github.com/ormastes/simple/blob/02f6687d846ba55faea4a08c44e4a3c0982a488d/doc/05_design/simple_distributed_textual_databases.md#L1-L72
[W01]: https://strictdoc.readthedocs.io/en/stable/stable/docs/strictdoc_01_user_guide.html
[W02]: https://www.microsoft.com/en-us/research/publication/build-systems-la-carte/
[W03]: https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html
[W04]: https://git-scm.com/docs/githooks
[W05]: https://git-scm.com/docs/git-diff-index
[W06]: https://git-scm.com/docs/git-cat-file
[W07]: https://docs.jj-vcs.dev/latest/config/#git-subprocessing-behavior
[W08]: https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches
[W09]: https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks
[W10]: https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows
[W11]: https://docs.github.com/en/enterprise-server@3.18/admin/enforcing-policies/enforcing-policy-with-pre-receive-hooks/about-pre-receive-hooks
[W12]: https://eclipse.dev/elk/reference/algorithms/org-eclipse-elk-layered.html
[W13]: https://www.w3.org/WAI/ARIA/apg/patterns/treeview/
