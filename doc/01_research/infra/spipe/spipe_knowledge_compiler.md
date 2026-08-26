<!-- codex-research -->
# SPipe Knowledge Compiler

## Virtual Documentation Views, Hybrid Search, Traceability, Tree Rebalancing, and Common-Knowledge Promotion

**Research layout note:** This requested infrastructure research artifact
combines repository-local findings and domain research; no duplicate same-slug
`local/` or `domain/` companion files currently exist.

**Date:** 2026-08-25  
**Status:** Final research, architecture, design, and implementation plan  
**Selected direction:** Canonical lifecycle tree + virtual two-dimensional views; hybrid rebalancing; full knowledge compiler  
**Repositories:** `ormastes/Spipe`, `ormastes/simple`  
**Repository snapshots reviewed:** SPipe `4527ac41dee1774820605dde10d0f209fa5eb608`; Simple `3b676a17736bcd9d7be2289e41ef1fab9e8b7251`

---

## 1. Executive Decision

### 1.1 Selected solution

Build a **SPipe Knowledge Compiler** with these properties:

1. Keep one canonical physical document tree, primarily organized by lifecycle/artifact kind:
   `research`, `requirements`, `plan`, `architecture`, `design`, `spec`, `guide`, `tracking`, and `report`.
2. Classify every artifact independently by:
   - feature,
   - component,
   - layer,
   - project,
   - lifecycle kind,
   - trace relations.
3. Expose generated, read-only **virtual files and directories** to LLMs in feature-first, component-first, layer-first, trace-first, and project-family views.
4. Use a typed artifact graph as the source of truth for identity and traceability; paths are locations, not identities.
5. Use hybrid retrieval:
   - exact identifier and metadata lookup,
   - BM25 lexical search,
   - graph traversal/reranking,
   - optional embeddings,
   - optional LLM validation.
6. Use a hybrid tree-rebalancing algorithm:
   - deterministic thresholds,
   - Leiden community detection,
   - balanced multilevel partitioning,
   - constrained local refinement,
   - migration/churn penalties,
   - human-approved physical moves.
7. Discover reusable knowledge across projects with exact duplication, MinHash/SimHash, BM25, semantic similarity, structural comparison, and LLM classification; promote only after evidence-backed review.
8. Keep SPipe independent. Simple provides an optional high-performance implementation of search, source analysis, duplication analysis, embedded storage, and server storage through stable provider interfaces.

### 1.2 Can virtual files and directories be presented to an LLM?

**Yes.** The robust design uses three compatible exposure mechanisms rather than assuming every LLM host behaves the same way.

| Exposure | What the LLM sees | Primary use | Write policy |
|---|---|---|---|
| MCP resources | URI-addressed virtual files and directories | Native context browsing | Read-only |
| MCP tools | `list`, `read`, `search`, `trace`, `resolve`, and refactor operations | Model-controlled discovery and action | Reads automatic; writes gated |
| Materialized view | Real generated files under `.spipe/view/` | File/shell-only agents | Generated and read-only |
| Editor virtual FS | `spipe-view:` hierarchy through a filesystem provider | Human + LLM IDE use | Read-only; refactor command for writes |
| FUSE/ProjFS | OS-mounted virtual hierarchy | Optional late compatibility | Not part of the initial design |

MCP resources can represent data that behaves like a filesystem without mapping to a physical filesystem, and directory resources can use a directory MIME type. MCP tools are model-controlled, while resources are usually host/application-controlled. Therefore, **resources alone are insufficient** for reliable LLM discovery; SPipe must expose both resources and equivalent model-callable tools. The current MCP release also makes list/read responses cacheable, which matches SPipe's immutable snapshot and incremental-index design.

### 1.3 Why the full knowledge compiler is preferable

| Alternative | Strength | Main limitation | Decision |
|---|---|---|---|
| Physical 2-D directory tree | Easy to understand initially | One artifact belongs to many features/components; paths become deep and unstable | Reject |
| Duplicated feature and component trees | Both views are visible | Duplicate content drifts and breaks traceability | Reject |
| Canonical tree + generated indexes only | Low implementation cost | Weak rename safety and limited graph reasoning | Useful migration stage |
| **Knowledge compiler + virtual views** | Stable identity, multi-view navigation, safe refactors, search, traceability, promotion | More initial infrastructure | **Selected** |

---

## 2. Repository Findings

### 2.1 SPipe is already an independent mounted module

SPipe is structured as a reusable package containing process documents, skills, agents, CLI, MCP server, plugin metadata, and setup scripts. Simple mounts it under `.spipe` and links common process/expert surfaces into the host document tree. This is the correct dependency direction:

```text
SPipe
  independent process, schema, tools, rules, and common knowledge
       ▲
       │ mounted/linked and optionally extended
       │
Simple
  project-specific documents, source symbols, tests, DB/search providers
```

The current host-link checker and `doctor` command are a suitable foundation for workspace and linked-project validation.

### 2.2 Current SPipe implementation gaps

The current SPipe implementation is intentionally small, but the following changes are required:

- `cli/spipe.js` is a large, dependency-free Node entry point that mixes routing, filesystem operations, fine-tune workflow logic, and validation. New knowledge-compiler behavior should not be added to this monolith.
- `mcp/server.js` exposes only a few tools and one fixed resource, and identifies itself as protocol `2024-11-05`. The current MCP protocol is `2026-07-28`, with a stateless core and cache hints for list/read results.
- Project state is primarily exchanged through `.spipe/<feature>/state.md`; artifact IDs and typed graph edges do not yet carry state between agents.
- Similar skill/rule payloads are stored separately for Claude, Codex, Gemini, and other harnesses. This creates manual duplication and semantic drift.

### 2.3 Simple already contains most required search primitives

Simple does not need a new BM25 implementation from zero. It currently contains:

- `src/lib/common/search/types.spl`
  - fixed-point `Score`, posting lists, and embedding types;
- `src/lib/common/search/inverted_index.spl`
  - positional postings and Boolean/phrase queries;
- `src/lib/common/search/ranking.spl`
  - deterministic fixed-point BM25 using a non-negative logarithmic IDF form;
- `src/lib/common/search/ann.spl`
  - approximate-nearest-neighbor foundations;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/`
  - DBFS tokenizer, inverted index, search, and a second weaker BM25 approximation;
- `src/compiler/90.tools/duplicate_check/`
  - semantic, embedding, token, cosine, caching, and incremental duplicate analysis;
- `examples/10_tooling/obsidian-search/`
  - Markdown parsing, link graph, MCP handlers, and a ranking pipeline, although its current lexical scorer is only term-frequency matching.

The design must **consolidate**, not duplicate, these implementations.

### 2.4 Simple has three distinct database kinds

The current canonical database map identifies:

1. **Textual DB** — SDN text-file store with atomic writes/WAL.
2. **Embedded DB** — in-process SQL engine and DBFS storage kernel.
3. **DB server** — networked multi-user tier with sessions, capabilities, transactions, durability, protocol, and transport.

BM25/search integration must explicitly support all three instead of treating them as one DB.

### 2.5 Existing traceability work must be preserved

Simple already reorganized executable SSpec tests and generated `doc/06_spec` documents around mirrored paths and added `TRC231`/`TRC232` diagnostics. The knowledge compiler must retain this rule as a generated compatibility view:

```text
test/<kind>/<domain>/<feature>_spec.spl
  -> doc/06_spec/<kind>/<domain>/<feature>_spec.md
```

However, this mirrored path must no longer be the fundamental identity mechanism. Stable artifact/test IDs become authoritative; mirrored paths remain a human-facing projection and validation rule.

---

## 3. Goals and Non-Goals

### 3.1 Goals

- Present project knowledge to LLMs as shallow, searchable virtual directories.
- Support feature-first and component/layer-first navigation simultaneously.
- Preserve one canonical content copy.
- Make artifact, section, tag, and source-symbol renames compiler-like and transactional.
- Detect and prevent broken links across worktrees, submodules, linked projects, documentation, source, SSpec, unit tests, integration tests, and reports.
- Provide explicit traceability from research evidence to verified implementation.
- Rebalance large/deep documentation trees without oscillation or excessive churn.
- Promote genuinely reusable project knowledge into common SPipe knowledge.
- Reuse Simple's BM25, inverted-index, ANN, duplicate-check, compiler, DB, and test infrastructure.
- Keep a dependency-free SPipe fallback for repositories that do not use Simple.

### 3.2 Non-goals

- Do not physically duplicate canonical documents into every view.
- Do not let embeddings or an external LLM become mandatory for basic operation.
- Do not auto-accept inferred requirement/test/source trace links.
- Do not automatically rewrite the physical tree merely because a clustering algorithm changes its result.
- Do not require FUSE, ProjFS, an IDE extension, or a server process for initial operation.
- Do not merge SPipe into Simple or make SPipe impossible to use independently.
- Do not replace Git history or Git rename detection; supplement it with stable artifact identity and transaction journals.

---

## 4. Terminology and Relationship Model

### 4.1 Separate dependency from physical linkage

The word “dependent” must not implicitly mean “symlink” or “submodule.” Model these separately:

| Dimension | Values | Meaning |
|---|---|---|
| Semantic dependency | `independent`, `dependent`, `extends` | Knowledge/build/process relationship |
| Physical linkage | `none`, `path`, `symlink`, `junction`, `gitlink`, `worktree`, `package` | How the project is mounted |
| Version relation | commit, tag, range, floating | Which revision is consumed |
| Trust relation | trusted, reviewed, untrusted | Whether content may affect rules or prompts |

Example:

```sdn
project_relation:
  from: simple
  to: spipe
  semantic: extends
  linkage: gitlink
  mount: .spipe/spipe_project
  revision: pinned
  trust: trusted
```

### 4.2 Artifact versus location

- **Artifact**: Stable conceptual object, such as a research report or requirement.
- **Canonical path**: Current physical location of the artifact.
- **Virtual path**: Generated location in a selected view.
- **Artifact UID**: Immutable opaque identity.
- **Artifact key**: Human-readable semantic key that can be aliased or renamed.
- **Section UID**: Stable identity for a section/anchor.
- **Trace edge**: Typed relationship between graph nodes.

A path change must not create a new artifact.

---

## 5. Target Architecture

```text
                           ┌──────────────────────────┐
                           │ Canonical project files  │
                           │ docs / source / tests    │
                           └────────────┬─────────────┘
                                        │ parse + normalize
                   ┌────────────────────▼────────────────────┐
                   │          Knowledge Compiler Core        │
                   │                                         │
                   │  Identity ─ Artifact IR ─ Typed Graph   │
                   │      │           │            │          │
                   │      ├──── Diagnostics ────────┤          │
                   │      ├──── Search indexes ─────┤          │
                   │      └──── Transaction log ────┘          │
                   └───────┬─────────┬──────────┬─────────────┘
                           │         │          │
               ┌───────────▼──┐  ┌───▼─────┐  ┌─▼──────────────┐
               │ Projection   │  │ Refactor│  │ Analysis       │
               │ engine       │  │ engine  │  │ rebalancer /   │
               │              │  │         │  │ promotion      │
               └──────┬───────┘  └────┬────┘  └──────┬─────────┘
                      │               │              │
          ┌───────────┼───────────────┼──────────────┼───────────┐
          │           │               │              │           │
       MCP 2026     CLI/SDN       Editor/LSP     Simple      JS fallback
       resources    commands      adapter        provider    provider
       + tools                                      │
                                        ┌───────────┼────────────┐
                                        │           │            │
                                     Search      Compiler       DBs
                                     BM25/ANN    symbols/HIR    kinds 1-3
```

### 5.1 MDSOC+ component boundaries

Use parent-owned orchestration and explicit child ports:

- `KnowledgeCompiler` owns workspace lifecycle and immutable snapshots.
- `ParserService` emits parsed artifact deltas.
- `IdentityService` assigns/resolves UIDs and aliases.
- `GraphService` applies typed edge deltas.
- `IndexService` applies lexical/semantic index deltas.
- `ProjectionService` reads snapshots and emits virtual views.
- `DiagnosticService` reads snapshots and emits diagnostics only.
- `RefactorService` is the sole service authorized to mutate canonical files.
- `RebalanceService` emits proposals; it does not directly move physical files.
- `PromotionService` emits common-knowledge candidates; it does not publish without approval.

No analyzer should write arbitrary repository files. This greatly reduces race conditions in parallel-agent and worktree use.

---

## 6. Canonical Physical Tree and Virtual Views

### 6.1 Canonical lifecycle roots remain fixed

```text
doc/
  00_llm_process/
  01_research/
  02_requirements/
  03_plan/
  04_architecture/
  05_design/
  06_spec/
  07_guide/
  08_tracking/
  09_report/
  10_metrics/
```

The top-level taxonomy should change only through an explicit architecture decision. It provides stable human orientation and avoids moving thousands of files when feature/component taxonomy evolves.

### 6.2 Orthogonal classifications live in metadata

```sdn
artifact:
  uid: A-01K3R8G3N70ZMT43W6QJ7YHX4P
  key: design.search.bm25-core
  project: simple
  kind: design
  title: Shared BM25 Search Core
  canonical_path: doc/05_design/lib/search/bm25_core.md
  features:
    - search
    - project_knowledge
  components:
    - std.common.search
    - database.textual
    - database.embedded
    - database.server
    - spipe.knowledge
  layers:
    - parser
    - index
    - ranking
    - adapter
  status: approved
  visibility: project
  aliases:
    - design.db.bm25
```

A document can appear in any number of virtual views without being copied canonically.

### 6.3 Required virtual views

```text
spipe://workspace/simple/view/
  lifecycle/
  feature/
    search/
    traceability/
  component/
    std.common.search/
    database.embedded/
    spipe.knowledge/
  layer/
    index/
    ranking/
  matrix/
    feature/search/component/database.embedded/
  trace/
    requirement/REQ-SEARCH-001/
  project/
    simple/
    spipe/
  status/
    proposed/
    approved/
    stale/
  diagnostics/
```

### 6.4 Virtual naming and collision policy

A generated path is for navigation, not identity.

```text
<slug>--<short-uid>.md
```

The UID suffix is omitted when the slug is unique in the virtual directory. If two artifacts have the same title/slug, the suffix is added deterministically. A generated `.spipe-view.sdn` manifest maps every path to its canonical UID.

### 6.5 Generated directory index

Reading a virtual directory returns a generated Markdown index:

```markdown
# Feature: Search

Project: simple
Artifacts: 38

## Most Relevant
- Shared BM25 Search Core — design — `spipe://artifact/A-...`
- Search Requirements — requirement — `spipe://artifact/A-...`

## By Lifecycle
- Research: 6
- Requirements: 4
- Design: 8
- SSpec: 10
- Reports: 3

## Trace Gaps
- REQ-SEARCH-004: missing integration test
```

Keep generated index pages bounded. Default limits:

- at most 100 direct entries per page;
- at most 200 Markdown lines;
- at most roughly 6,000 model tokens;
- cursor/page resources for larger directories.

---

## 7. LLM Exposure Design

### 7.1 Canonical MCP URI space

Use a custom RFC 3986-compliant scheme:

```text
spipe://workspace/{workspace_id}/
spipe://project/{project_id}/artifact/{artifact_uid}
spipe://project/{project_id}/section/{section_uid}
spipe://workspace/{workspace_id}/view/{view}/{path...}
spipe://workspace/{workspace_id}/trace/{artifact_uid}
spipe://workspace/{workspace_id}/diagnostics
```

The custom scheme is preferable to pretending every object is a local physical file. It makes project and artifact identity explicit and prevents path-root ambiguity. A compatibility alias may expose `file://`-style virtual resources for clients that require them, but the `spipe://` URI remains authoritative.

### 7.2 MCP resources

Implement:

- `resources/list`
- `resources/templates/list`
- `resources/read`
- list-change/update notification where supported by the negotiated protocol
- `ttlMs` and `cacheScope` for MCP 2026 clients

Resource templates:

```text
spipe://project/{project}/artifact/{uid}
spipe://workspace/{workspace}/view/{view}/{path}
spipe://workspace/{workspace}/search/{query_hash}
spipe://workspace/{workspace}/trace/{uid}
```

Directory resources use `inode/directory`; documents use `text/markdown`; graph/structured records use an SDN MIME convention such as `application/vnd.spipe.sdn`.

### 7.3 MCP tools

Resources may not be automatically surfaced to the model by every host. Provide equivalent tools:

| Tool | Purpose |
|---|---|
| `spipe_list` | List children of a virtual URI with pagination |
| `spipe_read` | Read artifact, section, directory index, or report |
| `spipe_search` | Hybrid search with filters and explanations |
| `spipe_resolve` | Resolve key/path/alias/UID to canonical artifact |
| `spipe_trace` | Return typed trace subgraph or matrix |
| `spipe_diagnostics` | Return broken links, gaps, stale edges, imbalance |
| `spipe_refactor_plan` | Produce a mutation plan without writing |
| `spipe_refactor_apply` | Apply an approved transaction token |
| `spipe_tree_suggest` | Return rebalance proposals |
| `spipe_knowledge_candidates` | Return common-knowledge promotion candidates |

Read operations are safe and model-callable. Mutating operations require explicit policy/approval and support dry-run by default.

### 7.4 MCP protocol migration

The existing server identifies as MCP `2024-11-05`. Refactor it into:

```text
mcp/
  server.js                 # protocol-neutral entry
  transport/
    stdio_legacy.js         # 2024/2025 initialize/session compatibility
    http_2026.js            # 2026-07-28 stateless HTTP
  protocol/
    resources.js
    tools.js
    cache.js
    auth.js
```

Requirements:

- maintain current stdio behavior for installed clients;
- add a stateless `2026-07-28` path;
- return deterministic tool/resource ordering;
- expose cache hints;
- never store authorization-sensitive results in a public cache scope;
- keep the core knowledge services transport-independent.

### 7.5 Materialized view for file-only agents

Generate:

```text
.spipecache/                 # ignored immutable/cache data
.spipe/view/                 # ignored materialized virtual hierarchy
  feature/
  component/
  layer/
  trace/
  diagnostics/
```

The materializer copies generated read-only representations, not canonical ownership. Each file starts with a generated header:

```markdown
<!-- generated by SPipe; do not edit -->
<!-- canonical-uid: A-... -->
<!-- canonical-path: doc/05_design/lib/search/bm25_core.md -->
```

Use a content hash to avoid rewriting unchanged generated files. On Unix, permissions may be changed to read-only as a user hint; correctness must not depend on permissions because users and tools can override them.

### 7.6 Editor virtual filesystem

A VS Code-style filesystem provider can register `spipe-view:` and show the virtual hierarchy without materializing it. The provider should reject direct writes and route rename/edit commands through SPipe refactor operations.

FUSE/ProjFS remains an optional final adapter. It creates more platform, security, invalidation, and write-through complexity than is justified before MCP, tools, materialization, and editor providers have been evaluated.

---

## 8. Artifact Identity and Schema

### 8.1 Dual identity

Every node has:

- immutable UID: never reused or changed;
- semantic key: human-readable and renameable;
- aliases: retained after semantic-key, tag, section, or title changes;
- canonical path: mutable location;
- content hash: detects changes, not identity.

A ULID-like sortable UID is suitable, but no semantic information should be embedded in it.

### 8.2 Stable section identity

Markdown heading text is not a safe identity. Store a stable marker immediately after the heading:

```markdown
## Incremental Index Maintenance
<!-- spipe:section uid=S-01K3... key=design.search.incremental-maintenance -->
```

Rendered Markdown remains readable. A heading rename changes only presentation; the section UID remains stable. If a client uses a traditional `#heading-slug` link, SPipe records it as a compatibility alias and can rewrite it.

### 8.3 Graph node types

```text
Workspace
Project
Revision
Artifact
Section
Claim
ResearchEvidence
Requirement
NonFunctionalRequirement
DesignDecision
ArchitectureComponent
PlanTask
SSpecScenario
SourceSymbol
UnitTest
IntegrationTest
SystemTest
TestRun
TestResult
Feature
Component
Layer
Tag
CommonKnowledgeUnit
VirtualView
```

### 8.4 Typed edge set

| Edge | Meaning |
|---|---|
| `contains` | Project/artifact/section containment |
| `classifies` | Feature/component/layer/tag classification |
| `evidence_for` | Research evidence supports a claim/requirement/design decision |
| `derives` | One artifact or claim derives another |
| `satisfies` | Design or implementation satisfies requirement |
| `realizes` | Design realizes architecture/requirement |
| `schedules` | Plan task schedules requirement/design work |
| `specifies` | SSpec scenario specifies required behavior |
| `implements` | Source symbol implements requirement/design/spec |
| `verifies` | Test verifies requirement/spec/source behavior |
| `covers` | Test covers source symbol/module |
| `produces` | Test run produces result/report |
| `links_to` | General explicit cross-reference |
| `aliases` | Compatibility identity/link |
| `supersedes` | New artifact replaces old artifact |
| `extends` | Project knowledge extends common/family knowledge |
| `promoted_from` | Common unit provenance from project units |
| `depends_on` | Semantic/build dependency |
| `mounted_as` | Concrete linked/mounted relation |

### 8.5 Edge provenance and authority

```sdn
edge:
  uid: E-01K3...
  type: verifies
  from: T-UNIT-SEARCH-004
  to: REQ-SEARCH-004
  origin: explicit
  status: accepted
  confidence_milli: 1000
  created_by: author
  evidence:
    - test/01_unit/lib/search/bm25_spec.spl
```

`origin` values:

- `explicit`
- `generated`
- `structural`
- `lexical_inference`
- `semantic_inference`
- `llm_inference`

Only accepted explicit/generated edges satisfy strict traceability gates. Inferred edges remain proposals until reviewed.

---

## 9. Traceability Model

### 9.1 Use a DAG, not one rigid sequence

The desired flow is valid, but plan and research do not always form a single linear chain. Model this as a typed directed acyclic graph:

```text
Research evidence ──evidence_for──► Requirement
        │                               │
        └──evidence_for──► Design ◄─────┘
                               │ realizes
                               ▼
                          Architecture

Plan task ──schedules──► Requirement / Design / Implementation

Requirement ──specified_by──► SSpec scenario
Requirement ──satisfied_by──► Design
Requirement ──implemented_by─► Source symbol
Requirement ──verified_by────► Unit / Integration / System test
SSpec scenario ──verified_by─► Test
Source symbol ──covered_by───► Test
Test run ──produces──────────► Result / Report
```

This allows a requirement to precede research in an obvious case, a design experiment to generate new requirements, or a plan to schedule several graph nodes without becoming the semantic source of truth.

### 9.2 Traceability policy profiles

| Profile | Required authority | Typical use |
|---|---|---|
| `advisory` | Explicit or high-confidence candidate | Early research/prototype |
| `standard` | Explicit requirement-to-design/spec/test; source may be structural | Normal development |
| `strict` | All required links explicit/generated and accepted | Release-critical component |
| `mission_critical` | Strict links, immutable evidence, signed results, formal verification where configured | Safety/security-critical work |

### 9.3 Required trace checks

For each requirement, configurable gates check:

- evidence or rationale exists;
- design/architecture realization exists;
- a plan task exists when implementation is open;
- at least one SSpec scenario exists;
- implementation source exists when status is implemented;
- required unit test exists;
- required integration/system test exists;
- last passing result is not stale relative to source/spec changes.

### 9.4 Inference pipeline

Candidate trace recovery proceeds from cheapest and most reliable to more expensive:

1. Explicit artifact/requirement/test IDs.
2. Stable section IDs and aliases.
3. Exact source symbols and `@cover` markers.
4. Path and mirrored SSpec relationships.
5. Metadata equality/intersection.
6. BM25 lexical retrieval.
7. Graph-neighborhood features.
8. Optional semantic retrieval.
9. Optional LLM validation/explanation.

Information-retrieval trace recovery is useful but requires analyst review; combining lexical, structural, domain, and semantic evidence is more reliable than relying on one similarity score. Therefore, the compiler emits:

```text
candidate edge + confidence + evidence breakdown + affected quality gate
```

It never silently converts a candidate to accepted truth.

### 9.5 Diagnostic codes

Introduce stable diagnostics, while retaining existing `TRC231`/`TRC232` compatibility:

| Code | Meaning |
|---|---|
| `SPK001` | Duplicate artifact UID |
| `SPK002` | Ambiguous artifact key/alias |
| `SPK101` | Broken artifact link |
| `SPK102` | Broken section link |
| `SPK103` | Cross-project target unavailable at configured revision |
| `SPK201` | Requirement lacks design realization |
| `SPK202` | Requirement lacks executable SSpec |
| `SPK203` | Requirement lacks required unit test |
| `SPK204` | Requirement lacks required integration/system test |
| `SPK205` | Test result stale relative to source/spec |
| `SPK301` | Missing feature/component/layer classification |
| `SPK302` | Conflicting classification |
| `SPK401` | Virtual path collision |
| `SPK501` | Common-knowledge candidate |
| `SPK601` | Directory exceeds balance threshold |
| `SPK602` | Excessive canonical path depth |
| `SPK603` | Tiny sibling directories should be merged |

---

## 10. Search Architecture

### 10.1 One common lexical search core

Make `std.common.search` the canonical algorithm owner. The current fixed-point BM25 implementation in `src/lib/common/search/ranking.spl` is stronger than the separate DBFS FTS approximation and should become the common scorer.

Target common modules:

```text
src/lib/common/search/
  __init__.spl
  types.spl
  analyzer.spl
  document.spl
  inverted_index.spl
  corpus_stats.spl
  ranking.spl
  query.spl
  top_k.spl
  wand.spl
  block_max_wand.spl
  segment.spl
  snapshot.spl
  provider.spl
  explain.spl
  fingerprint.spl
  similarity.spl
```

### 10.2 Required common abstractions

```text
SearchDocument
  id
  fields[]
  metadata
  revision

SearchField
  name
  tokens
  length
  weight

Analyzer
  normalize
  tokenize
  stopword/stemming policy

LexicalIndex
  add/update/delete
  snapshot
  postings
  document stats

Ranker
  score
  top-k
  explanation

SearchProvider
  index delta
  query
  capabilities
```

### 10.3 BM25 consolidation tasks

1. Preserve deterministic fixed-point scoring from `std.common.search.ranking`.
2. Add exact document lengths and corpus statistics to the shared index.
3. Replace DBFS's simplified IDF and average-length substitution with the common scorer.
4. Keep old DBFS public functions as compatibility facades until callers migrate.
5. Add score-parity fixtures shared by:
   - common Simple implementation,
   - DBFS adapter,
   - SPipe JavaScript fallback,
   - textual DB adapter,
   - embedded DB adapter,
   - server DB adapter.
6. Use stable tie-breaking by document ID.
7. Add field-aware scoring for title, heading, identifiers, tags, and body.

Initial field weights, subject to evaluation:

| Field | Initial weight |
|---|---:|
| Exact artifact/requirement/source ID | deterministic exact-match boost |
| Title | 4.0 |
| Source symbol / key / alias | 4.0 |
| Heading | 2.5 |
| Tag / feature / component | 2.0 |
| Body | 1.0 |

### 10.4 Database adapters

#### Kind 1: Textual DB

The current textual FTS is trigram overlap. Retain it for fuzzy substring matching, but add a BM25 side index:

```text
SdnDatabase table mutation
       │
       ├─ transactional row/WAL update
       └─ lexical index delta
              ├─ in-memory segment
              └─ durable index snapshot/checkpoint
```

The DB API exposes separate query modes:

- `contains_fuzzy` — trigram index;
- `search_lexical` — BM25;
- `search_hybrid` — lexical plus optional vector provider.

#### Kind 2: Embedded DB

Provide an in-process search index usable by `PureDatabase`, SQLite-style wrappers, and DBFS. Small databases use exhaustive postings/top-k; larger embedded databases enable WAND. Persistence follows the embedded DB transaction/checkpoint boundary.

#### Kind 3: DB server

Add a search capsule behind the existing server's session, capability, transaction, durability, protocol, and transport boundaries:

```text
database/server/
  search_capability.spl
  search_session.spl
  search_service.spl
  search_protocol.spl
  search_segment_store.spl
```

Server requirements:

- deny-wins capability checks for collections and fields;
- snapshot-consistent query view;
- commit-before-ack index durability policy;
- segmented postings;
- Block-Max WAND for top-k pruning;
- optional shard-level top-k merge;
- per-tenant/private cache isolation;
- query budget and cancellation.

### 10.5 SPipe provider independence

SPipe must work without a Simple binary. Define a provider protocol:

```sdn
search_provider:
  name: simple_native
  protocol_version: 1
  capabilities:
    - bm25
    - phrase
    - explain
    - semantic
    - incremental
  transport: process
  command: bin/simple spipe-search-provider
  fallback: js_fixed_point
```

Provider order:

1. Simple native provider, when configured and healthy.
2. Optional server provider, for large multi-project deployments.
3. Dependency-free JavaScript fixed-point BM25 fallback.

The fallback and Simple providers must pass the same golden corpus and score-order tests.

---

## 11. Hybrid Retrieval

### 11.1 Candidate generation

```text
Exact/alias/ID matches
          ∪
BM25 top N lexical candidates
          ∪
Graph-neighborhood candidates
          ∪
Optional embedding top N candidates
          ∪
Recent/active task candidates
```

### 11.2 Fusion

Use **Reciprocal Rank Fusion (RRF)** first because BM25, graph scores, and semantic similarity have incompatible score scales. RRF avoids fragile normalization:

```text
RRF(d) = Σ 1 / (k + rank_source(d))
```

Use a configurable default `k`, initially 60, and record every contributing rank in the explanation.

After fusion, apply bounded reranking:

```text
final = rrf
      + exact-id boost
      + accepted-trace proximity boost
      + same feature/component boost
      + optional recency boost
      - stale/deprecated penalty
```

Graph and recency boosts must be capped so a central but irrelevant document cannot outrank strong lexical evidence.

### 11.3 Semantic retrieval

Semantic search is optional and provider-based:

- local Simple fixed-point/ANN provider;
- local external model through a configured adapter;
- remote embedding service only with explicit data policy.

Do not send private project content to a remote service by default. Cache entries by normalized content hash, model ID, model revision, and preprocessing version.

### 11.4 Explainability

Every result can return:

```sdn
result:
  artifact: A-...
  final_rank: 1
  matched:
    - title: bm25
    - alias: exact
    - component: exact
  ranks:
    lexical: 2
    graph: 1
    semantic: 8
  trace_distance: 1
  stale: false
```

This is essential for trace suggestions, rebalancing, and common-knowledge promotion because users must understand why two artifacts were considered related.

---

## 12. Incremental Indexing and Storage

### 12.1 Snapshot + delta architecture

```text
immutable base snapshot
        +
per-worktree dirty overlay
        +
in-memory current delta
        =
query snapshot
```

### 12.2 Cache keys

```text
project UID
revision/commit
canonical path
content hash
parser version
schema version
analyzer version
search-provider version
embedding model/revision, when used
```

### 12.3 Tracked versus derived data

Tracked:

```text
.spipe/config.sdn
.spipe/projects.sdn
.spipe/artifact_aliases.sdn
.spipe/tag_registry.sdn
knowledge/common/...                 # in SPipe repo
```

Derived and ignored:

```text
.spipecache/objects/
.spipecache/graph/
.spipecache/index/
.spipecache/embeddings/
.spipecache/transactions/
.spipe/view/
```

### 12.4 Worktree behavior

Git linked worktrees share common repository data but have separate per-worktree metadata. Follow the same principle:

- share immutable content-addressed index segments for committed revisions;
- keep dirty overlays, write locks, transaction journals, and generated views per worktree;
- identify the workspace with repository identity + worktree identity + revision;
- never allow one worktree's uncommitted document move to mutate another worktree's index state.

### 12.5 Linked-project behavior

Each graph node is namespaced by project UID and revision. Cross-project references resolve through the project registry, not by assuming a relative path. A missing linked project produces a diagnostic rather than silently resolving to a similarly named local artifact.

---

## 13. Compiler-Like Rename and Link Safety

### 13.1 Transactional refactor pipeline

```text
1. Resolve UID/section/tag/symbol
2. Compute incoming and outgoing references
3. Check project/worktree revision and content hashes
4. Build mutation plan
5. Validate collisions and policy
6. Write transaction journal
7. Apply atomic file edits/moves
8. Update aliases and canonical paths
9. Incrementally reparse/reindex
10. Run link and trace verification
11. Commit transaction or roll back
```

### 13.2 Supported operations

```text
spipe doc rename <artifact> <new-title-or-key>
spipe doc move <artifact> <new-canonical-path>
spipe section rename <section> <new-heading>
spipe tag rename <old> <new>
spipe component rename <old> <new>
spipe feature rename <old> <new>
spipe symbol rename-plan <symbol>
```

### 13.3 Alias policy

- Artifact key rename creates a durable alias unless explicitly disabled.
- Section heading rename retains section UID and old slug alias.
- Tag/component/feature rename writes a registry alias and rewrites canonical metadata.
- Aliases carry deprecation status and optional expiry review, but immutable UIDs never expire.

### 13.4 Detecting raw external moves

Direct filesystem or Git operations cannot always be intercepted. Recovery order:

1. UID found in moved content.
2. Exact content hash match.
3. Git rename detection.
4. Near-duplicate fingerprint.
5. BM25/semantic candidate recovery.
6. User review for ambiguity.

Git rename detection has a configurable similarity threshold and can fall back to an expensive quadratic comparison. SPipe should use UIDs/hashes first and bound any similarity fallback.

### 13.5 Prevention layers

| Layer | Behavior |
|---|---|
| MCP/editor virtual view | Reject direct writes |
| SPipe CLI | Require plan/apply transaction |
| File watcher | Diagnose raw move/edit immediately |
| Pre-commit | Reject newly broken links/trace gates |
| Pre-push/CI | Full linked-project and worktree verification |
| `spipe doctor` | Validate mounts, revisions, indexes, aliases, and transactions |

Do not use Git `assume-unchanged` or `skip-worktree` as a protection mechanism; they are not reliable edit guards.

---

## 14. Hybrid Tree-Rebalancing Algorithm

### 14.1 Separate virtual and physical balancing

- **Virtual trees** can be regenerated automatically because no canonical path changes.
- **Physical trees** receive conservative proposals and require explicit apply.
- Top-level lifecycle roots remain fixed.
- Protected component roots, generated paths, test mirror rules, and external-public paths are constraints.

### 14.2 Why not AVL/B-tree balancing

AVL/B-tree algorithms balance key lookup depth. Documentation organization must preserve semantic cohesion, trace relationships, ownership, public paths, and migration cost. It is a constrained weighted graph/hypergraph partitioning problem, not an ordered-key tree problem.

### 14.3 Graph construction

Each artifact is a node. Create normalized weighted edges from:

| Evidence | Initial relative strength |
|---|---:|
| Explicit accepted trace | 10 |
| Source/test coverage relation | 9 |
| Explicit document link | 8 |
| Same stable component ownership | 6 |
| Same feature + layer | 5 |
| Co-change history | 4 |
| BM25 similarity | 0–4 |
| Semantic similarity | 0–4 |
| Shared tags only | 1–2 |

These values are starting weights and must be calibrated against accepted organization decisions.

Represent multi-node requirements/design/tests as hyperedges or as a trace-hub node so the partitioner does not split a tightly related verification chain merely because pairwise lexical similarity is weak.

### 14.4 Constraints

**Must-link:**

- generated spec and executable SSpec pair;
- artifact and mandatory sidecar;
- explicitly protected document bundle;
- requirement and its only strict verification evidence when policy demands co-location.

**Cannot-link:**

- lifecycle roots;
- separate security/trust domains;
- public versus private knowledge;
- different projects when a view is configured as project-local;
- incompatible artifact kinds when a view forbids mixing.

### 14.5 Algorithm pipeline

1. Audit current tree and calculate metrics.
2. Collapse must-link groups.
3. Build sparse candidate graph using explicit edges and lexical/semantic candidate generation.
4. Run **Leiden** to find connected semantic communities.
5. For oversized communities, use a **multilevel balanced k-way partitioner**:
   - coarsen,
   - initial partition,
   - uncoarsen,
   - local refinement.
6. Merge undersized communities into the neighbor with the lowest objective increase.
7. Assign a stable cluster UID.
8. Generate a deterministic label from taxonomy + representative terms; allow optional LLM naming review.
9. Construct a shallow hierarchy under fixed roots.
10. Run constrained local moves/swaps to improve the objective.
11. Apply hysteresis, cooldown, and minimum-improvement gates.
12. Emit a proposal with moves, links affected, trace impact, score delta, and rollback map.

Leiden is preferred over Louvain because it guarantees connected communities. Multilevel graph partitioning is used after community detection because it explicitly handles balanced k-way subdivision. Dynamic balanced partitioning motivates charging a migration cost when organization changes over time.

### 14.6 Objective function

For candidate tree `T`:

```text
C(T) =
    λcut      × weighted_cross_directory_edges
  + λdepth    × depth_penalty
  + λfanout   × directory_fanout_penalty
  + λcount    × direct_file_count_penalty
  + λentropy  × semantic_entropy
  + λtrace    × trace_chain_split_penalty
  + λambig    × naming_or_classification_ambiguity
  + λmove     × number_and_weight_of_moves
  + λchurn    × recent_move_or_rename_penalty
  + λpublic   × public_path_break_penalty
  - λcohesion × within_directory_cohesion
```

Physical proposals include a high `λmove`, `λchurn`, and `λpublic`. Virtual projections set those near zero because regeneration does not move canonical files.

### 14.7 Initial tree heuristics

These are tunable defaults, not universal laws. Human menu research supports avoiding both extreme depth and extreme breadth, but does not define a repository-wide perfect number.

| Metric | Target | Warning | Split/review candidate |
|---|---:|---:|---:|
| Depth below lifecycle root | 1–3 | 4 | ≥5 |
| Direct documents per directory | 6–24 | >32 | >48 |
| Child directories | 3–12 | >16 | >24 |
| Tiny sibling directory | ≥3 docs | 2 docs | repeated 1-doc siblings |
| Full canonical components | ≤6 | 7 | ≥8 |

Exceptions remain for stable public APIs, generated mirrors, hardware/platform taxonomies, and policy-protected roots.

### 14.8 Stability controls

A physical move proposal is emitted only when all configured gates pass, for example:

- predicted objective improvement ≥15%;
- confidence ≥0.85;
- no unresolved strict trace break;
- no protected/public path violation;
- cluster stable across at least two index snapshots or explicitly requested;
- moved artifact has not been automatically proposed recently;
- proposal size below configured review limit.

Never use exact numbers as immutable standards; store them in `.spipe/config.sdn` and calibrate from repository history.

### 14.9 Proposal format

```sdn
rebalance_proposal:
  uid: RP-01K3...
  scope: doc/05_design/compiler
  old_cost_milli: 18320
  new_cost_milli: 14210
  improvement_milli: 224
  confidence_milli: 910
  moves: 37
  aliases_added: 37
  references_rewritten: 126
  strict_trace_breaks: 0
  clusters:
    - uid: C-...
      label: lowering
      members: 14
  status: proposed
```

---

## 15. Common-Knowledge Discovery and Promotion

### 15.1 Knowledge scopes

```text
local session
  ↓
project
  ↓
project family
  ↓
SPipe common
```

Examples:

- Simple HIR lowering details remain `project:simple`.
- A rule for preserving stable section IDs during document refactoring can become `common:spipe`.
- A firmware verification workflow shared by several embedded projects may become `family:embedded`.

### 15.2 Candidate discovery cascade

1. Exact normalized hash.
2. Token/shingle overlap.
3. MinHash for scalable near-duplicate candidate generation.
4. SimHash for near-duplicate fingerprints.
5. BM25 cross-project retrieval.
6. Existing Simple token/cosine duplicate analysis.
7. Structural comparison:
   - artifact kind,
   - heading roles,
   - trace position,
   - component/layer classifications.
8. Optional embedding similarity.
9. Optional LLM classification and rewrite proposal.

Use cheap methods to create a small candidate set; do not perform all-pairs embedding or LLM comparison.

### 15.3 Reuse and refactor Simple duplicate-check

The existing duplicate tool already provides semantic, semantic-LLM, token, cosine, embedding cache, and incremental modules. Extract its reusable analysis primitives from compiler-tool ownership:

```text
src/lib/common/search/
  fingerprint.spl
  similarity.spl
  candidate_bucket.spl
  semantic_provider.spl

src/compiler/90.tools/duplicate_check/
  # remains CLI/report orchestration using the common library
```

SPipe calls this through the same provider mechanism as BM25. The JavaScript fallback implements exact hash, shingles, and lexical similarity; semantic support remains optional.

### 15.4 Promotion score

```text
promotion_score =
    project_diversity
  + lexical_similarity
  + semantic_similarity
  + structural_similarity
  + trace_role_similarity
  + stability
  + reuse_value
  - project_specificity
  - conflicting_policy
  - sensitive_content_risk
```

A candidate report must show each component, source projects, conflicting clauses, and proposed scope.

### 15.5 Promotion policy

- No automatic publication to SPipe common.
- Require at least two independently configured projects for normal common promotion; allow explicit expert promotion for foundational rules.
- Preserve source provenance and revision.
- Replace local copies with `extends` only after project verification.
- Support local overrides without copying the entire common artifact.
- Re-run project-specific tests/skill validation after promotion.

Example:

```sdn
knowledge:
  uid: K-...
  key: common.doc.safe_refactor
  scope: common
  promoted_from:
    - simple:A-...
    - project_b:A-...
  status: approved
  version: 1

project_extension:
  extends: spipe://common/K-...
  additions:
    simple_symbol_index: required
```

### 15.6 LLM role

The LLM may:

- explain whether content is project-specific, family-level, or common;
- identify semantic differences hidden by high lexical similarity;
- propose a neutral generalized wording;
- identify unsafe loss of constraints during generalization.

The LLM must receive the source evidence and conflicts. It does not decide promotion alone.

---

## 16. Skill and Rule Compiler

### 16.1 One canonical source

Replace hand-maintained parallel skill payloads with:

```text
skill_src/
  common/
  phases/
  domains/
  tools/
  harness/
    claude.sdn
    codex.sdn
    gemini.sdn
```

The compiler emits:

```text
.claude/skills/...
.claude/agents/...
.codex/skills/...
.codex/commands/...
.gemini/...
```

Generated files include source UID, generator version, and content hash. CI verifies that generated surfaces are current.

### 16.2 Phase updates

The existing eight-phase pipeline should exchange graph identities, not only prose in `state.md`.

| Phase | Required graph input | Required graph output |
|---|---|---|
| Dev/intake | user request | task UID, acceptance criteria/requirement candidates |
| Research | task/requirements | evidence, claims, risks, reusable components |
| Architecture | accepted evidence/requirements | components, interfaces, decisions |
| Spec | requirements/design | SSpec scenario nodes and `specifies` edges |
| Implement | design/spec | source-symbol nodes and `implements` edges |
| Refactor | source/graph | preserved identity, duplicate findings, refactor transaction |
| Verify | requirements/spec/source/tests | accepted `verifies` edges and test results |
| Ship | complete trace subgraph | revision/release/report nodes |

`state.md` remains a readable session log, but it references stable UIDs and is no longer the sole machine-readable communication channel.

### 16.3 Rule additions

Every harness receives these common rules:

- search/resolve by artifact UID before guessing a path;
- never edit a generated virtual view;
- use SPipe refactor operations for rename/move/tag/section changes;
- preserve accepted trace edges;
- distinguish explicit versus inferred relations;
- never promote project knowledge without provenance and review;
- run incremental diagnostics before phase exit;
- update generated skill surfaces only through the skill compiler.

---

## 17. CLI Design

```text
spipe index build [scope]
spipe index update [scope]
spipe index watch
spipe index status

spipe view list <uri>
spipe view read <uri>
spipe view materialize [view]
spipe view clean

spipe search <query> [--project ...] [--feature ...]
spipe resolve <key|uid|path|alias>

spipe trace show <artifact>
spipe trace matrix [scope]
spipe trace check [--profile standard|strict|mission_critical]
spipe trace suggest [scope]

spipe doc rename <artifact> <new-key-or-title>
spipe doc move <artifact> <path>
spipe section rename <section> <heading>
spipe tag rename <old> <new>
spipe refactor plan <operation...>
spipe refactor apply <transaction>
spipe refactor rollback <transaction>

spipe tree audit [scope]
spipe tree suggest [scope]
spipe tree apply <proposal>

spipe knowledge scan [projects...]
spipe knowledge candidates
spipe knowledge promote <candidate> --scope family|common

spipe skill generate
spipe skill check
spipe doctor [host]
```

All commands support stable machine output:

```text
--format text|sdn|json
```

SDN is the canonical repository data format; JSON is retained for MCP and external interoperability.

---

## 18. SPipe Repository Refactor

### 18.1 Target layout

```text
Spipe/
  cli/
    spipe.js                       # thin compatibility dispatcher
  mcp/
    server.js                      # thin transport entry
    transport/
    protocol/
  src/
    core/
      knowledge_compiler.js
      snapshot.js
      delta.js
    format/
      sdn.js
    model/
      project.js
      artifact.js
      section.js
      edge.js
      diagnostic.js
    parser/
      markdown.js
      sdn.js
      sspec.js
      source_metadata.js
    workspace/
      registry.js
      git.js
      worktree.js
      linked_project.js
    storage/
      object_store.js
      snapshot_store.js
      alias_store.js
      transaction_store.js
    graph/
      graph.js
      trace.js
      query.js
    search/
      provider.js
      js_bm25.js
      fusion.js
      explain.js
    view/
      projection.js
      virtual_path.js
      materialize.js
    diagnostics/
      links.js
      trace.js
      tree.js
    refactor/
      planner.js
      apply.js
      rollback.js
    rebalance/
      graph_builder.js
      community.js
      partition.js
      objective.js
      proposal.js
    promote/
      candidates.js
      score.js
      generalize.js
    skill/
      compiler.js
      adapters.js
  schema/
    project.schema.sdn
    artifact.schema.sdn
    edge.schema.sdn
    view.schema.sdn
    provider.schema.sdn
  skill_src/
  knowledge/
    common/
    family/
  test/
    unit/
    integration/
    fixture/
    perf/
```

### 18.2 Compatibility rule

Existing `spipe` CLI commands, setup scripts, link surfaces, and `doctor` behavior remain available. Refactoring first extracts modules without changing output, then adds new commands.

### 18.3 Dependency policy

Keep the baseline Node package dependency-free. Optional capabilities are external providers accessed through an explicit process/server protocol. This maintains SPipe portability while allowing Simple-native performance.

---

## 19. Simple Repository Changes

### 19.1 Search core

Create/extend:

```text
src/lib/common/search/analyzer.spl
src/lib/common/search/document.spl
src/lib/common/search/corpus_stats.spl
src/lib/common/search/query.spl
src/lib/common/search/top_k.spl
src/lib/common/search/wand.spl
src/lib/common/search/block_max_wand.spl
src/lib/common/search/segment.spl
src/lib/common/search/provider.spl
src/lib/common/search/explain.spl
src/lib/common/search/fingerprint.spl
src/lib/common/search/similarity.spl
```

Modify:

```text
src/lib/common/search/ranking.spl
src/lib/common/search/inverted_index.spl
src/lib/common/search/__init__.spl
```

### 19.2 DB integrations

Modify/add:

```text
# Textual DB
src/lib/nogc_sync_mut/database/fts.spl
src/lib/nogc_sync_mut/database/search_index.spl

# Embedded DB / DBFS
src/lib/nogc_sync_mut/db/dbfs_engine/fts/bm25.spl
src/lib/nogc_sync_mut/db/dbfs_engine/fts/inverted_index.spl
src/lib/nogc_sync_mut/db/dbfs_engine/fts/search.spl
src/lib/nogc_sync_mut/database/pure_sql/search.spl

# DB server
src/lib/nogc_sync_mut/database/server/search_capability.spl
src/lib/nogc_sync_mut/database/server/search_service.spl
src/lib/nogc_sync_mut/database/server/search_protocol.spl
src/lib/nogc_sync_mut/database/server/search_segment_store.spl
```

Mirror required public APIs into supported async/GC variants according to the existing tier policy.

### 19.3 Provider executable

```text
src/app/spipe_knowledge_provider/
  main.spl
  protocol.spl
  search_handler.spl
  duplicate_handler.spl
  symbol_handler.spl
```

Capabilities:

- fixed-point BM25 search;
- indexing/delta application;
- duplicate/similarity candidates;
- optional ANN/embedding search;
- compiler symbol/reference export;
- deterministic structured responses.

### 19.4 Compiler/source symbol export

Add a stable source-symbol snapshot API using compiler/HIR data:

```text
symbol UID
project/module
kind
name
signature hash
definition span
reference spans
implements/cover annotations
content/revision hash
```

Use compiler data for Simple source. Other languages use pluggable analyzers or text fallback; do not make an imprecise generic parser authoritative.

---

## 20. Implementation Plan by Dependency Wave

### Wave 0 — Baseline and locked decisions

Deliverables:

- Record the architecture decisions listed in Section 27.
- Inventory current SPipe command outputs, links, skills, and MCP behavior.
- Inventory Simple search, DB, duplicate-check, source-symbol, SSpec, and trace diagnostics.
- Create benchmark corpora and representative project-tree fixtures.
- Establish `.spipe/config.sdn` schema extension.
- Measure current CLI startup, doctor, full scan, duplicate scan, and representative search latency.

Exit gates:

- behavior snapshots for all existing SPipe commands;
- no unresolved ownership conflict between SPipe and Simple;
- baseline metrics recorded;
- migration fixture includes linked project and multiple worktrees.

### Wave 1 — Modularize SPipe without behavior change

Deliverables:

- Extract CLI routing, link handling, config parsing, fine-tune operations, and doctor checks from `cli/spipe.js`.
- Extract MCP protocol/transport from `mcp/server.js`.
- Introduce core error/result types and deterministic SDN/JSON serialization.
- Keep existing command output byte-compatible where practical.

Exit gates:

- all current SPipe tests/build checks pass;
- existing host setup and `doctor` output preserved;
- `cli/spipe.js` and `mcp/server.js` are thin dispatchers;
- no new external runtime dependency.

### Wave 2 — Schemas, identity, parsers, and workspace registry

Deliverables:

- Project, artifact, section, edge, alias, and view schemas.
- Markdown/SDN/SSpec parsers.
- UID injection command with dry-run.
- Project/link/worktree registry.
- Content-addressed cache and per-worktree overlay.
- Initial artifact inventory report.

Exit gates:

- deterministic parse and round-trip fixtures;
- duplicate UID and ambiguous alias diagnostics;
- no canonical path move required for adoption;
- worktrees do not share dirty overlay state.

### Wave 3 — Read-only artifact graph and diagnostics

Deliverables:

- Typed graph store and query API.
- Explicit link, heading, requirement, SSpec, test, and source-reference extraction.
- Broken-link and initial trace-gap diagnostics.
- Compatibility mapping for `TRC231`/`TRC232`.
- Trace matrix report.

Exit gates:

- every parsed explicit relation has provenance;
- no inferred edge satisfies strict gates;
- incremental one-file update produces the same graph as a clean rebuild;
- graph snapshots are deterministic.

### Wave 4 — Consolidated BM25 and provider protocol

Deliverables:

- Shared Simple search documents, corpus statistics, scorer, top-k, explanations, and provider protocol.
- DBFS BM25 adapter migrated to common ranking.
- JavaScript fixed-point fallback.
- Golden corpus parity tests.
- Initial SPipe `search`, `resolve`, and `read` commands.

Exit gates:

- identical ordering across provider implementations for golden fixtures;
- exact document length used by DBFS path;
- old DBFS API compatibility maintained;
- no embedding required;
- incremental index parity with clean rebuild.

### Wave 5 — Virtual resources, tools, and materialized views

Deliverables:

- `spipe://` URI resolver.
- Feature/component/layer/matrix/trace projections.
- MCP resource list/templates/read.
- MCP model-callable list/read/search/trace tools.
- 2026 stateless HTTP path and legacy stdio compatibility.
- `.spipe/view/` materializer.
- Optional editor filesystem adapter skeleton.

Exit gates:

- an LLM can navigate a virtual directory without knowing canonical paths;
- virtual files resolve to exactly one artifact UID;
- views are deterministic and read-only;
- cache hints and private/public scope are correct;
- large views paginate and stay within output limits.

### Wave 6 — Transactional refactoring and link repair

Deliverables:

- Rename/move/section/tag operations.
- Reverse-reference index.
- transaction journal, hash preconditions, atomic writes, rollback;
- file-watch diagnostics for raw moves;
- pre-commit/pre-push/CI integrations;
- cross-project link checking.

Exit gates:

- fault injection at every transaction phase leaves either old or new valid state;
- rename preserves UID and accepted trace edges;
- broken links cannot be introduced through approved refactor operations;
- raw rename recovery handles UID/hash/Git cases and reports ambiguity.

### Wave 7 — Full traceability and phase integration

Deliverables:

- compiler source-symbol provider;
- SSpec scenario and test-result nodes;
- requirement/design/plan/source/test/result policy profiles;
- agent phase input/output UID contracts;
- stale-result detection;
- trace suggestion pipeline with evidence breakdown.

Exit gates:

- selected features demonstrate research-to-result trace matrices;
- strict profile rejects inferred-only required links;
- accepted trace survives canonical path reorganization;
- phase agents read/write graph references without losing readable `state.md` logs.

### Wave 8 — Hybrid tree audit and rebalancer

Deliverables:

- tree metrics and threshold diagnostics;
- weighted graph builder;
- Leiden-compatible community implementation/provider;
- multilevel balanced partitioner;
- constrained local optimizer;
- virtual auto-rebalancing;
- physical proposal and apply path.

Exit gates:

- no disconnected generated community;
- hard constraints always preserved;
- objective and every move are explainable;
- repeated unchanged runs produce no churn;
- physical changes require explicit approved proposal.

### Wave 9 — Common-knowledge promotion and skill compiler

Deliverables:

- cross-project candidate scan;
- exact/MinHash/SimHash/BM25/semantic/structural fusion;
- candidate review report;
- common/family knowledge catalog;
- `extends` and override model;
- canonical skill source and harness generators.

Exit gates:

- no common promotion without provenance;
- promoted knowledge passes every consuming project's validation;
- generated harness skills are current and semantically equivalent;
- project-specific constraints are not erased by generalization.

### Wave 10 — Database server optimization and optional semantic layer

Deliverables:

- textual DB BM25 side index;
- embedded DB WAND path;
- DB server segmented index and Block-Max WAND;
- shard merge and capability controls;
- optional ANN/embedding provider;
- hybrid RRF search in SPipe and DB APIs.

Exit gates:

- transaction/snapshot consistency demonstrated for each DB kind;
- authorization tests prevent unauthorized field/document leakage;
- Block-Max WAND results exactly match exhaustive top-k;
- semantic provider failure degrades to lexical/graph search.

### Wave 11 — Optional OS-level virtual filesystem

Proceed only if MCP tools/resources, materialization, and editor adapters do not cover required clients.

Potential deliverables:

- FUSE adapter for Linux/macOS environments;
- ProjFS adapter for Windows;
- explicit read-only mount;
- invalidation and mount-health diagnostics.

This wave is intentionally non-critical.

---

## 21. Parallel Workstreams and Ownership

| Workstream | Primary ownership | Must not modify concurrently |
|---|---|---|
| A — SPipe core/model/storage | `Spipe/src/core`, `model`, `storage`, `schema` | Search/rebalancer internals |
| B — MCP/virtual views | `Spipe/mcp`, `src/view`, MCP adapters | Canonical parsers/model schema |
| C — Simple search core | `simple/src/lib/common/search` | DB/server adapters |
| D — DB adapters | textual, embedded, server DB paths | Common scorer internals except reviewed interfaces |
| E — Trace/source/SSpec | SPipe graph/diagnostics + Simple symbol provider | Rebalancer objective |
| F — Rebalancer | `Spipe/src/rebalance` | Canonical graph model |
| G — Promotion/skill compiler | `Spipe/src/promote`, `skill`, `skill_src`, `knowledge` | Harness generated outputs by hand |
| H — Verification/performance/security | tests, fixtures, benchmarks, fault injection | Product code except test hooks |

Integration order:

```text
A
├─► B
├─► E
├─► F
└─► G

C ─► D ─► B/E/F/G provider integration

H begins in Wave 0 and gates every merge.
```

Each workstream publishes interfaces before implementation fan-out. Shared files are owned by an integration agent; parallel agents avoid overlapping edits.

---

## 22. Testing Strategy

### 22.1 Unit tests

- UID and alias resolution.
- Markdown section-marker preservation.
- SDN schema validation.
- edge authority/status transitions.
- BM25 fixed-point scoring and ties.
- RRF fusion.
- virtual path collision handling.
- objective-function terms.
- transaction journal state machine.
- MinHash/SimHash/fingerprint fixtures.

### 22.2 Property and metamorphic tests

- Moving a file without changing UID does not change artifact identity.
- Renaming a heading with stable section UID preserves all UID-based links.
- Clean rebuild equals any sequence of incremental updates.
- Repeating view generation produces byte-identical output.
- Exhaustive search and WAND/Block-Max WAND return identical top-k.
- Refactor rollback restores hashes and graph exactly.
- Rebalancing never violates must-link/cannot-link constraints.
- Adding unrelated artifacts does not reorder exact-ID search results.

### 22.3 Integration tests

- SPipe standalone repository without Simple.
- Simple host with SPipe links.
- multiple linked projects;
- Git submodule missing/uninitialized;
- two simultaneous worktrees with different dirty changes;
- Unix symlink and Windows junction/path behavior;
- legacy MCP stdio client;
- MCP 2026 stateless client;
- file-only agent using `.spipe/view/`;
- editor virtual filesystem read-only enforcement.

### 22.4 Traceability fixtures

Create small complete and intentionally incomplete chains:

```text
research -> requirement -> design -> plan -> SSpec -> source -> unit -> integration -> result
```

Test every missing or stale edge and every policy profile.

### 22.5 Rebalancer fixtures

- one oversized directory with clear semantic clusters;
- deep single-child chains;
- many tiny one-file directories;
- cross-cutting feature artifacts;
- protected public paths;
- unstable changing similarity edges;
- conflicting must-link/cannot-link constraints;
- linked-project boundary.

Metrics:

- weighted edge cut;
- maximum and average depth;
- direct file-count distribution;
- trace-chain splits;
- move count;
- cluster stability across revisions;
- human acceptance/rejection rate.

### 22.6 Retrieval evaluation

Build judged query sets for:

- exact identifiers;
- acronym/symbol queries;
- natural-language feature queries;
- requirement-to-test recovery;
- design-to-source recovery;
- common-knowledge candidates.

Measure:

- Recall@K;
- Precision@K;
- MRR;
- nDCG@10;
- candidate-link precision/recall;
- index build/update latency;
- warm/cold query latency;
- memory/index size;
- provider parity.

### 22.7 Performance gates

Set final absolute budgets after Wave 0 measurement. Initial release gates should be relative:

- no-op `spipe doctor` and existing commands do not regress by more than 10%;
- warm one-file incremental update is at least 20× cheaper than full rebuild on the benchmark repository;
- virtual view regeneration rewrites only changed generated files;
- BM25/WAND optimizations preserve exact result parity;
- search remains usable with embeddings disabled or unavailable;
- duplicate/common-knowledge candidate generation is sparse, not global all-pairs.

Provisional scale targets for evaluation, not unconditional promises:

- 50,000 document artifacts;
- 1,000,000 sections/symbol/test nodes;
- 10 linked projects;
- 5 concurrent worktrees;
- warm lexical query P95 below 100 ms on a development workstation;
- single-document incremental graph/index update P95 below 100 ms.

---

## 23. Migration Plan

### Stage 1 — Observe only

- Add parsers, inventory, diagnostics, and search.
- Do not move canonical files.
- Generate report of missing UIDs, ambiguous paths, broken links, and directory metrics.

### Stage 2 — Add stable identity

- Inject artifact UIDs into high-value docs first.
- Add stable section IDs only where referenced or trace-critical.
- Build alias registry from current paths/headings.

### Stage 3 — Build virtual views

- Generate feature/component/layer views.
- Let agents use views while humans retain current physical tree.
- Measure navigation/search effectiveness and view size.

### Stage 4 — Convert rules and trace links

- Update SPipe agents/skills to resolve UIDs and write typed edges.
- Import existing requirement IDs, `@cover` markers, SSpec mirrored paths, and reports.
- Preserve `TRC231`/`TRC232` behavior.

### Stage 5 — Enable safe refactors

- Require SPipe refactor commands for managed document moves/renames.
- Add pre-commit/CI checks.
- Migrate old path links to UID-backed links while preserving readable relative Markdown.

### Stage 6 — Rebalance virtual views

- Run hybrid rebalancer automatically only on virtual projections.
- Calibrate weights and thresholds from user acceptance.

### Stage 7 — Propose physical cleanup

- Start with obvious deep chains and oversized directories.
- Apply small batches with aliases and rollback maps.
- Do not combine physical reorganization with unrelated content changes.

### Stage 8 — Promote common knowledge

- Scan Simple plus other SPipe projects.
- Review high-confidence candidates.
- Introduce `extends` references and remove duplicate local copies only after validation.

---

## 24. Security and Trust

### 24.1 URI and path security

- Validate every resource URI.
- Reject `..`, encoded traversal, absolute-path injection, and cross-root escape.
- Resolve symlinks/junctions before authorization decisions.
- Namespace project/revision explicitly.
- Never let a virtual path choose an arbitrary host path.

### 24.2 Knowledge and prompt security

Project documents may contain untrusted instructions. The knowledge compiler treats content as data, not as executable agent policy, unless it is in an approved skill/rule scope. Search results include trust/visibility metadata.

### 24.3 Write authorization

- Read-only by default.
- Refactor apply requires approved transaction capability.
- Common promotion requires separate publish capability.
- DB server search honors existing deny-wins capability policy.
- Private artifacts never enter public MCP cache scope.

### 24.4 Embedding privacy

- Local provider is default.
- Remote embedding requires explicit project policy.
- Secret/private paths can be excluded or locally embedded only.
- Cache keys include model revision; cache scope follows artifact visibility.

### 24.5 Transaction integrity

- hash preconditions;
- journal before writes;
- atomic rename/write where supported;
- fsync policy for critical mode;
- rollback and startup recovery;
- signed or immutable result evidence in mission-critical mode.

---

## 25. Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Too much schema/metadata burden | Adoption slows | Auto-infer candidates; require metadata progressively by policy |
| Virtual views confuse canonical ownership | Accidental edits | Generated header, read-only adapters, UID/canonical-path display |
| MCP clients expose resources differently | LLM cannot navigate | Resources + tools + materialized tree |
| SPipe becomes dependent on Simple | Portability loss | Provider ports and JS fallback |
| Duplicate BM25 implementations drift | Search inconsistency | One golden corpus and common scorer ownership |
| Embeddings leak code/docs | Security issue | Local default, explicit remote policy, visibility-aware cache |
| Rebalancer oscillates | Path churn | Stable cluster UIDs, hysteresis, cooldown, migration cost |
| Semantic clustering splits trace chains | Lost cohesion | Hyperedges, trace penalty, must-link constraints |
| Inferred trace is mistaken for truth | False compliance | Explicit authority/status, strict gate excludes inferred edges |
| Parallel worktrees corrupt cache | Incorrect results | Shared immutable snapshots + per-worktree overlays/locks |
| Common promotion erases project constraints | Unsafe generic rule | Provenance, conflict analysis, local overrides, project validation |
| MCP 2026 ecosystem migration is uneven | Compatibility break | Legacy stdio adapter and protocol-neutral core |
| Huge graph/index startup cost | Poor UX | content-addressed snapshots, lazy loads, incremental deltas |

---

## 26. Acceptance Criteria

### Virtual knowledge view

- An LLM can list and read feature/component/layer/trace virtual directories through MCP tools without knowing physical paths.
- A file-only agent can browse the same logical view under `.spipe/view/`.
- Every virtual file maps to exactly one canonical artifact UID.
- No virtual representation is treated as canonical writable ownership.

### Search

- One BM25 scoring contract is used by SPipe, textual DB, embedded DB, DBFS, and DB server adapters.
- JavaScript fallback and Simple provider return equivalent deterministic ordering on golden fixtures.
- Semantic search is optional and failure-safe.
- Every hybrid result includes an explanation.

### Traceability

- Research, requirements, design, plan, SSpec, source, tests, runs, and results can be represented as typed graph nodes/edges.
- Strict/mission-critical gates ignore unaccepted inferred links.
- Broken or stale links are detected across linked projects and worktrees.
- Existing SSpec mirrored-path diagnostics continue to work.

### Refactoring

- Artifact, section, tag, feature, and component renames preserve stable identity and update references transactionally.
- A failed transaction can be recovered or rolled back.
- Raw external moves are recovered when identity/hash/Git evidence is sufficient and otherwise reported as ambiguous.

### Rebalancing

- Fixed lifecycle roots and all hard constraints are preserved.
- Virtual views can rebalance automatically.
- Physical moves are proposal-only until explicitly approved.
- Repeated runs on unchanged input are deterministic and produce no churn.

### Common knowledge

- Candidates are discovered through the hybrid pipeline.
- Every promoted common unit records source provenance and conflicts.
- No project-specific constraint is deleted without validated replacement/override.
- Harness-specific skills are generated from one canonical source.

---

## 27. Architecture Decisions to Record

| ADR | Decision |
|---|---|
| ADR-001 | Canonical physical organization remains lifecycle-first |
| ADR-002 | Artifact/section UIDs are identity; paths and headings are aliases/locations |
| ADR-003 | Virtual knowledge is exposed through MCP resources, MCP tools, and materialized views |
| ADR-004 | Virtual views are read-only; canonical writes use transactional refactor operations |
| ADR-005 | `std.common.search` owns the canonical BM25 scoring contract |
| ADR-006 | SPipe remains independent through a dependency-free fallback and provider ports |
| ADR-007 | Traceability is a typed DAG with explicit edge provenance and authority |
| ADR-008 | Inferred trace links are candidates, never strict compliance evidence |
| ADR-009 | Hybrid retrieval uses exact lookup + BM25 + graph + optional semantics, initially fused with RRF |
| ADR-010 | Tree balancing uses constrained graph clustering/partitioning, not ordered-tree balancing |
| ADR-011 | Physical reorganization is conservative and proposal-driven; virtual reorganization is automatic |
| ADR-012 | Common knowledge promotion requires provenance, conflict review, and validation |
| ADR-013 | Agent/harness skills are compiled from one canonical source |
| ADR-014 | MCP 2026 is the target protocol with legacy compatibility adapters |
| ADR-015 | FUSE/ProjFS is optional and deferred |

---

## 28. Recommended First Implementation Slice

The first useful end-to-end slice should be deliberately smaller than the final system but aligned with it:

1. Modularize SPipe CLI/MCP.
2. Add project/artifact/section/edge schemas.
3. Index Markdown and current SSpec/test metadata.
4. Use the JavaScript fixed-point BM25 fallback first.
5. Expose:
   - `spipe_list`,
   - `spipe_read`,
   - `spipe_search`,
   - `spipe_trace`,
   - feature/component virtual resources,
   - `.spipe/view/` materialization.
6. Add read-only broken-link and trace-gap diagnostics.
7. Integrate the Simple native search provider after the public provider contract and golden corpus are stable.
8. Add transactional refactoring before any automatic physical tree migration.

This slice immediately answers the LLM navigation problem and validates the core identity/view model without waiting for semantic embeddings, server DB search, or physical filesystem mounts.

---

## 29. Research Basis

### Protocols and virtual filesystems

1. Model Context Protocol, **2026-07-28 specification release**: stateless core, self-describing requests, cacheable/deterministic list results, and protocol migration guidance.
2. Model Context Protocol, **Resources**: URI-addressed resources, list/read/templates, custom URI schemes, virtual `file://` behavior, directory MIME type, and path-sanitization requirements.
3. Model Context Protocol, **Tools**: model-controlled invocations and human-in-the-loop guidance for actions.
4. Visual Studio Code Extension API, **FileSystemProvider / virtual workspaces**: URI-scheme-based hierarchical virtual filesystems.
5. Linux FUSE and Windows Projected File System documentation: optional user-space/projected filesystem adapters.

### Search and similarity

6. Robertson and Zaragoza, *The Probabilistic Relevance Framework: BM25 and Beyond*, Foundations and Trends in Information Retrieval, DOI `10.1561/1500000019`.
7. Broder et al., *Efficient Query Evaluation using a Two-Level Retrieval Process* / WAND, DOI `10.1145/956863.956944`.
8. Ding and Suel, *Faster Top-k Document Retrieval Using Block-Max Indexes*, DOI `10.1145/2009916.2010048`.
9. Cormack, Clarke, and Buettcher, *Reciprocal Rank Fusion Outperforms Condorcet and Individual Rank Learning Methods*, DOI `10.1145/1571941.1572114`.
10. Malkov and Yashunin, *Efficient and Robust Approximate Nearest Neighbor Search Using Hierarchical Navigable Small World Graphs*, arXiv `1603.09320`.
11. Broder, *On the Resemblance and Containment of Documents*, DOI `10.1109/SEQUEN.1997.666900`.
12. Manku, Jain, and Das Sarma, *Detecting Near-Duplicates for Web Crawling*, DOI `10.1145/1242572.1242592`.

### Tree organization and graph partitioning

13. Miller, *The Depth/Breadth Tradeoff in Hierarchical Computer Menus*, DOI `10.1177/107118138102500179`.
14. Traag, Waltman, and van Eck, *From Louvain to Leiden: Guaranteeing Well-Connected Communities*, DOI `10.1038/s41598-019-41695-z`.
15. Karypis and Kumar, *A Fast and High Quality Multilevel Scheme for Partitioning Irregular Graphs* and *Multilevel k-way Partitioning Scheme for Irregular Graphs*.
16. Avin et al., *Dynamic Balanced Graph Partitioning*, DOI `10.1137/17M1158513`.

### Requirements traceability

17. Hayes, Dekhtyar, and Osborne, information-retrieval approaches for requirements tracing, with analyst review.
18. Research on requirements-to-code recovery combining lexical, structural, domain, and semantic features rather than relying on one IR signal.
19. T-BERT and related neural trace-recovery work, used here only as an optional semantic candidate provider, not an authority mechanism.

### Repository evidence reviewed

SPipe:

- `README.md`
- `cli/spipe.js`
- `mcp/server.js`
- `plugin/manifest.sdn`
- `package.json`
- `.claude/skills/lib/doc.md`
- `.claude/skills/lib/spipe_phases.md`
- `.claude/agents/spipe/research.md`
- `doc/00_llm_process/spipe/skill.md`

Simple:

- `.spipe/README.md`
- `doc/03_plan/app/spipe/sspec_traceability_reorg_plan.md`
- `doc/07_guide/lib/database/db_implementations_map.md`
- `src/lib/common/search/{types,inverted_index,ranking,__init__}.spl`
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/{bm25,inverted_index,search,__init__}.spl`
- `src/lib/nogc_sync_mut/database/fts.spl`
- `src/lib/nogc_sync_mut/database/server/`
- `src/compiler/90.tools/duplicate_check/`
- `doc/07_guide/app/duplicate_check.md`
- `examples/10_tooling/obsidian-search/`

---

## 30. Final Recommendation

Proceed with the selected **full knowledge compiler**, but implement it in dependency waves:

1. stabilize identity and read-only graph/search;
2. expose virtual directories to LLMs through resources, tools, and materialized views;
3. consolidate BM25 and integrate Simple providers/DB tiers;
4. add transactional refactoring and full trace gates;
5. add hybrid virtual-tree rebalancing;
6. add conservative physical proposals;
7. add common-knowledge promotion and generated skill surfaces;
8. defer OS-level virtual mounts until actual client evidence requires them.

The central rule is:

> **Canonical content remains single-copy and stable by UID; every directory hierarchy is a projection that may be regenerated, searched, validated, and safely refactored.**

---

## 31. Post-Research Design Resolution

<!-- codex-design-review: 2026-08-25 -->

The selected direction remains unchanged. Independent highest-capability review
identified ambiguities that are resolved normatively by the final requirements,
architecture, ADR record, and detail designs linked below. Where this research
uses earlier or conflicting wording, those follow-on artifacts govern:

- the graph is a directed typed multigraph; only the lifecycle/derivation
  subgraph is required to be acyclic, and reverse relation names are queries,
  not separately stored edge types;
- artifact virtual files carry one artifact UID, while aggregate directory,
  search, trace, and diagnostic representations carry a synthetic projection
  UID bound to an immutable snapshot;
- provisional identities permit observe-only migration of unmarked documents,
  but strict identity gates require persisted artifact/section UIDs;
- URIs, cursors, transaction approvals, and cache entries bind snapshot,
  principal, policy, analyzer, and provider-contract identity as applicable;
- the threat model and authorization/resource-limit contracts precede enabling
  HTTP transport or canonical mutation;
- transaction journals are durable per-worktree state with before-images,
  ordered locks, replay protection, crash recovery, cross-device rejection,
  and schema-version coexistence rules—not disposable cache data;
- deterministic RRF belongs to the search foundation, while optional semantic
  retrieval and database-server optimization remain later providers;
- rebalancing is bounded by a fixed seed, deterministic numeric policy, memory
  budget, and a deterministic non-Leiden fallback; and
- performance thresholds become release gates only with a recorded corpus,
  machine profile, command, and retained result.

Normative follow-on artifacts:

- `doc/02_requirements/feature/spipe_knowledge_compiler.md`
- `doc/02_requirements/nfr/spipe_knowledge_compiler.md`
- `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md`
- `doc/04_architecture/infra/adr/spipe_knowledge_compiler_decisions.md`
- `doc/05_design/infra/spipe/spipe_knowledge_compiler.md`
- `doc/05_design/infra/spipe/spipe_knowledge_compiler_mcp_views.md`
- `doc/05_design/infra/spipe/spipe_knowledge_compiler_search_providers.md`

## 32. 2026-08-26 Native Identity-Model Follow-up

Wave 2's dependency-free JavaScript identity and schema implementation is
already present on `main` (rewritten upstream commit `deccbce964e`). A review
therefore rejected duplicating that implementation and instead froze the
provider-facing native Simple boundary.

The first proposed native slice was deliberately narrowed to typed ASCII
workspace/project/worktree/artifact/section/edge IDs, content hashes, and
provisional artifact identity derivation. Semantic keys, revisions, and paths
remain deferred because current `main` has UTF-8 validation but no importable
Unicode NFC normalization primitive; accepting an ASCII-only substitute would
falsify the contract.

A highest-capability review gave the narrowed three-file candidate a static
PASS. It was not admitted or committed: both available `bin/release` executables
identify themselves as Rust bootstrap seeds, and repository policy forbids seed
fallback for normal checks/tests. The candidate is preserved outside the
worktree at `/tmp/spipe-id-wave2-clean` pending a genuine self-hosted runtime.
Before admission it still needs focused self-hosted check/test evidence, success
coverage for every `KnowledgeUid` variant, and an early non-ASCII provisional-ID
rejection case. No runtime PASS or implementation-complete claim is made.

## 33. 2026-08-26 Raw JavaScript RRF Admission

The dependency-free raw-RRF boundary is separate from exact-identity dominance,
graph traversal, semantic retrieval, and post-fusion adjustments. An initial
two-file candidate stopped at syntax `PASS`, focused `10/11`, and high-review
`FAIL`; it remains historical `NOT-EVIDENCE`.

A fresh session repaired the validation TOCTOU by snapshotting caller-owned
data descriptors exactly once, rejected accessor/hidden/symbol/unknown shapes,
preserved phase-specific errors, completed numeric/default/source-identity and
hostile-object coverage, and corrected the reordered-source oracle. Evidence:
pre-runtime highest-capability static `PASS`; cycle 1 syntax `PASS` and focused
`15/16` with one malformed test fixture; cycle 2 syntax `PASS` and focused
`16/16`; independent final highest-capability `PASS`. The exact two-file kernel
was pushed as `595ba6e449`.

This admits raw deterministic RRF only. Exact identity dominance, accepted graph
candidate construction/proximity, bounded post-fusion adjustments, integrated
stale/deprecated explanations, and full AC-4 remain open.

## 34. 2026-08-26 Authority-Bound RRF Reranking Admission

The next dependency-free slice admits a page-local, fixed-policy reranker over
the raw RRF result. Only a captured verification capability may attest the
combined raw-fusion digest, evidence digest, authorization receipt, graph
snapshot/policy, query, analyzer, and scope. The reranker validates and freezes
all locally provable structure, calls the verifier exactly once, and applies
integer trace, feature, component, recency, stale, and deprecated adjustments
without mutating raw hits or explanations.

Evidence: syntax `PASS`; focused `13/13`; full SPipe suite `PASS` (`117/117`
unit, Wave 2 `9/9`, Wave 3 `25/25`, Wave 4 `9/9`, legacy and performance gates);
pre-runtime and final highest-capability reviews `PASS`. The exact three-file
slice was pushed as `44e65a6713`.

This remains page-local and authority-bound. Exact identity dominance, graph
candidate production, provider/search integration, and global candidate-pool
completeness remain open, so AC-4 is not complete.
