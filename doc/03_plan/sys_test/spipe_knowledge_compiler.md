# SPipe Knowledge Compiler System-Test Plan

**Date:** 2026-08-25  
**Status:** Design baseline with five compile-valid, deliberately RED scaffolds  
**Feature slug:** `spipe_knowledge_compiler`  
**Research:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`

## 1. Purpose

This plan defines the executable and operator-manual evidence required to accept
the SPipe Knowledge Compiler. It covers the dependency-free SPipe core, optional
Simple providers, virtual knowledge views, traceability, safe refactoring,
rebalancing, promotion, protocol compatibility, storage isolation, and failure
recovery. It does not treat source inspection, generated inventories, or an
optional-provider skip as runtime evidence.

Five executable design scaffolds now exist under `test/`. They compile and run
to explicit `DESIGN-SCAFFOLD` failures because production oracles do not yet
exist. Their five exact-path Markdown mirrors under `doc/06_spec/` are authored,
non-generated design manuals. Neither the RED executions nor the authored
mirrors are implementation PASS evidence. When implementation surfaces
stabilize, replace each fail-fast helper with a production-observing oracle,
run the exact commands in Section 10, regenerate each mirror, and independently
review the resulting operator manual.

## 2. Authoritative contracts

- Feature requirements: `doc/02_requirements/feature/spipe_knowledge_compiler.md`
- NFRs: `doc/02_requirements/nfr/spipe_knowledge_compiler.md`
- Architecture: `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md`
- Detail design: `doc/05_design/infra/spipe/spipe_knowledge_compiler.md`
- Operator guide: `doc/07_guide/app/spipe/spipe_knowledge_compiler.md`
- SSpec authoring: `doc/07_guide/infra/sspec_scenario_manual.md`
- Manual quality: `doc/07_guide/infra/sspec_documentization_maintenance.md`

The allocation below uses the frozen `REQ-SPKC-001` through `REQ-SPKC-030` and
`NFR-SPKC-001` through `NFR-SPKC-025` identifiers. Executable coverage must
never invent a second identifier vocabulary.

## 3. Planned executable and manual artifacts

| Responsibility | Executable SSpec | Generated operator manual |
|---|---|---|
| Primary end-to-end workflow | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl` | `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md` |
| MCP resources, tools, transport, and policy | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl` | `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.md` |
| Journals, rollback, linked projects, and worktrees | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl` | `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.md` |
| Search provider and incremental parity | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl` | `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md` |
| Tree balancing and common promotion | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl` | `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md` |

Focused unit and integration specs may be added under the owning SPipe or Simple
module. They support, but do not replace, these system scenarios.

## 4. Frozen manual vocabulary

The primary manual must use these exact literal `step("...")` calls:

1. `Index canonical knowledge artifacts`
2. `Browse virtual knowledge views`
3. `Search and trace artifacts`
4. `Apply a transactional refactor`
5. `Audit tree balance and promotion candidates`

The shared setup/checker helper names are also frozen:

- `setup_spipe_knowledge_fixture`
- `check_spipe_knowledge_compiler`
- `check_spipe_provider_parity`
- `check_spipe_refactor_recovery`
- `check_spipe_virtual_view_safety`

Reusable setup scenarios should use `# @inline`; primary scenarios may expand
them through `# @prev("...")` or `# @include("...")`. Do not introduce
`Given_*`, `When_*`, or `Then_*` alternatives. An unimplemented helper must
call `assert(false)` or `fail(...)`; an empty body or placeholder pass is a
release-blocking defect.

## 5. Scenario allocation

### 5.1 Canonical identity, parsing, graph, and snapshots

Allocate identity, canonical-tree, parser, graph, diagnostics, and snapshot
requirements `REQ-SPKC-001` through `REQ-SPKC-005` to the primary
spec. Required scenarios include:

- index Markdown, SDN, SSpec, and supported source metadata and resolve every
  artifact by immutable UID independently of its path;
- preserve section identity through heading and path changes;
- reject duplicate UIDs and ambiguous keys/aliases with stable diagnostics;
- produce byte-equivalent clean-rebuild and incremental snapshots;
- keep committed immutable segments shareable while isolating dirty overlays
  between two worktrees;
- diagnose an unavailable or revision-mismatched linked project rather than
  resolving a similarly named local artifact.
- preserve two same-endpoint/type multigraph edges with distinct provenance;
- reject duplicate canonical `RQ-`, `NFR-`, `SS-`, and `SY-` identities and
  keep human `REQ-*`/`NFR-*` labels as aliases rather than graph UIDs;
- prove inferred origins never satisfy strict or mission-critical trace even
  when maliciously marked accepted with confidence 1000;
- produce byte-identical graph roots, reverse queries, trace matrices, and
  diagnostics for clean versus equivalent incremental add/update/delete/move;
- reject overlapping node/edge delta operations, stale bases, and before-hash
  mismatches;
- prove a reader pin observes wholly old or wholly new graph state across a
  writer-lock-protected `current.sdn` compare-and-swap publication;
- emit `SPK101`/`SPK102`/`SPK103`, requirement gaps `SPK201`–`SPK204`, and the
  exact four-state `TRC231`/`TRC232` compatibility projection without local
  name fallback.

The visible primary step is `Index canonical knowledge artifacts`. Parser
matrices, unsupported syntax, and individual diagnostic-code cases are folded.

### 5.2 Virtual views and MCP

Allocate view and protocol requirements `REQ-SPKC-006` through `REQ-SPKC-010`,
plus CLI and compatibility requirements `REQ-SPKC-026`, `REQ-SPKC-027`, and
deferred-mount contract `REQ-SPKC-030`, to the primary and MCP specs. Required
scenarios include:

- list/read lifecycle, feature, component, layer, matrix, trace, project,
  status, and diagnostics projections;
- prove every virtual file resolves to exactly one canonical UID;
- enforce bounded deterministic pagination and stable collision suffixes;
- bind resource URIs, cursors, query hashes, cache entries, and mutation tokens
  to immutable snapshot identity, principal/policy version, filters, and
  analyzer version so pagination cannot drift across authorization or updates;
- materialize only changed read-only files under `.spipe/view/`;
- complete legacy stdio initialization and a stateless MCP 2026 request;
- start/connect, send `initialize`, send `notifications/initialized`, request
  `tools/list`, call one representative read tool, and observe a tool-level
  error response;
- reject virtual writes, traversal, encoded traversal, absolute injection,
  symlink/junction escape, and unauthorized project/revision access before any
  filesystem or cache effect;
- prove HTTP bind policy, authentication, origin policy, request/rate bounds,
  and parser/query budgets fail closed before dispatch;
- prove private/auth-sensitive results never use public cache scope.

The visible primary step is `Browse virtual knowledge views`. Schema
inventories, protocol matrices, large JSON payloads, and stress cases are
folded. Capture MCP frames with `# @capture(protocol)`, wrapper lifecycle with
`exec`, and diagnostics with `log`.

### 5.3 Search and traceability

Allocate retrieval/provider requirements `REQ-SPKC-011` through
`REQ-SPKC-016` and trace requirements `REQ-SPKC-017` through `REQ-SPKC-018` to
the primary and provider-parity specs. Required
scenarios include:

- exact UID/key/alias lookup has deterministic priority;
- fixed-point BM25 ordering and document-ID tie-breaking match the golden
  corpus for the dependency-free JavaScript and Simple providers;
- RRF combines lexical, graph, and optional semantic ranks with an explanation
  of every contributing signal;
- semantic-provider absence, denial, timeout, or malformed response degrades to
  lexical/graph retrieval without being reported as semantic PASS;
- clean-build versus incremental-index ordering and explanations are equal;
- receipt-bound explicit/generated accepted trace edges satisfy strict profiles while
  lexical, structural, semantic, and LLM-inferred candidates do not;
- research-to-requirement-to-design-to-SSpec-to-source-to-test-to-result paths
  are queryable and stale results are diagnosed after source/spec mutation;
- existing `TRC231`/`TRC232` behavior remains compatible.

The visible primary step is `Search and trace artifacts`. Golden-corpus rows,
ranking matrices, and candidate-confidence cases are folded. Capture compact
rank explanations and trace matrices as `text`; retain large provider payloads
as linked `protocol` or `artifact` evidence.

### 5.4 Transactional refactoring and recovery

Allocate rename/move and safety requirements `REQ-SPKC-019` through
`REQ-SPKC-020`, with registry/migration coverage from `REQ-SPKC-005` and
`REQ-SPKC-029`, to the primary and refactor specs. Required scenarios include:

- plan and apply artifact, section, tag, feature, and component renames/moves;
- preserve immutable UIDs, accepted trace edges, aliases, and readable links;
- reject stale content-hash preconditions before mutation;
- inject failure before journal, after journal, after partial staging, before
  verification, and before commit, proving that restart yields one valid old or
  new state;
- reject expired/replayed approval tokens and apply a documented lock order,
  durable before-images, file and parent-directory sync, and fail-closed
  cross-device policy;
- roll back content, paths, graph, aliases, and hashes exactly;
- recover raw moves by UID, then hash, then Git evidence, and report ambiguous
  similarity candidates for human review;
- prove a transaction in one dirty worktree cannot alter another worktree or an
  unavailable linked-project revision.

The visible primary step is `Apply a transactional refactor`. Use
`check_spipe_refactor_recovery`; capture the plan/journal/rollback map as
`artifact` and recovery diagnostics as `log`.

### 5.5 Rebalancing, promotion, and skill generation

Allocate organization, reuse, and generated-surface requirements
`REQ-SPKC-021` through `REQ-SPKC-025`, with phase/migration contracts
`REQ-SPKC-028` through `REQ-SPKC-029`, to the primary and
rebalance/promotion specs. Required scenarios include:

- preserve lifecycle roots, must-link/cannot-link constraints, trust domains,
  generated mirrors, and public paths;
- emit connected, deterministic virtual communities and byte-identical views
  on unchanged input;
- subdivide oversized communities, merge safe tiny siblings, and explain every
  objective term without oscillation;
- require an approved proposal token for physical moves and retain a rollback
  map;
- generate common-knowledge candidates from exact, fingerprint, BM25,
  structural, graph, and optional semantic evidence without global all-pairs
  work;
- reject promotion without provenance, conflict review, trust/visibility
  compatibility, license/secret scanning, and consuming-project validation;
- preserve project constraints with `extends` and local overrides;
- generate Claude, Codex, Gemini, and agent surfaces deterministically from one
  source and fail verification for stale generated hashes.

The visible primary step is `Audit tree balance and promotion candidates`.
Fold cluster matrices, stress data, and detailed scoring. Capture proposals,
rollback maps, and promotion provenance as `artifact`.

## 6. NFR evidence allocation

| NFR family | Required evidence | Planned owner |
|---|---|---|
| `NFR-SPKC-001`, `002`, `012`, `013` | byte-equivalent output/incremental parity, stable provider ordering, exhaustive-versus-optimized exact top-k | primary and provider specs |
| `NFR-SPKC-003`, `019`, `022` | dependency-free degradation, cross-platform/client compatibility, dependency and boundary discipline | primary, MCP, and provider specs |
| `NFR-SPKC-004`–`007` | fail-closed views/mutations, URI/path containment, authorization/cache isolation, embedding privacy | MCP and provider specs |
| `NFR-SPKC-008`–`010` | transaction integrity, worktree isolation, linked-project resolution safety | refactor spec |
| `NFR-SPKC-011` | bounded directory/manual/model-context pages and pagination | MCP spec |
| `NFR-SPKC-014`–`016` | incremental efficiency, qualified latency/capacity, compatibility-path performance | provider spec and retained benchmark receipts |
| `NFR-SPKC-017`, `018` | rebalancer stability/explanation and promotion fidelity | rebalance/promotion spec |
| `NFR-SPKC-020`, `021`, `024` | executable/manual evidence quality, reproducible receipts, generated-surface freshness | all specs; primary manual review |
| `NFR-SPKC-023` | canonical lifecycle/path stability | primary and refactor specs |
| `NFR-SPKC-025` | convergent once-only verification and bounded delivery cycles | verification report |

Absolute latency and capacity budgets must use the final authoritative NFR
identifiers and a Wave 0 hardware-qualified benchmark fixture. Provisional
research targets (50,000
artifacts, 1,000,000 graph nodes, ten projects, five worktrees, warm P95 under
100 ms) are evaluation targets until the NFR document freezes hardware,
dataset, repetitions, percentile method, and acceptable variance.

## 7. Test environment and fixtures

The fixture set must include:

- a standalone SPipe repository without Simple;
- a Simple host mounting SPipe;
- two linked projects, one absent and one pinned to a different revision;
- two simultaneous worktrees with conflicting dirty changes;
- duplicate UID/key, renamed heading, raw file move, stale source result, and
  virtual-path collision cases;
- a judged lexical corpus with exact IDs, phrases, ties, trace neighborhoods,
  private artifacts, and semantic-provider failures;
- oversized, deep, tiny-sibling, protected-path, and conflicting-constraint
  tree shapes;
- two project-specific knowledge units with a shared core and conflicting
  constraints;
- legacy MCP stdio and MCP 2026 stateless clients.
- adversarial parser/query depth, size, fanout, regex/token, and graph-traversal
  budgets plus an untrusted provider-command fixture.

Fixtures must use temporary, explicit roots. Tests may not target the repository
root, `$HOME`, `~`, or unresolved environment variables for destructive work.

## 8. Pass/fail and honesty rules

- Every accepted requirement has happy, edge, and error-path assertions.
- Use built-in matchers only. No `pass_todo`, empty body, or
  `expect(true).to_equal(true)` is evidence.
- A candidate or inferred trace edge never satisfies strict compliance.
- Catalog/schema/source presence never proves runtime dispatch or endpoint
  behavior.
- An unavailable optional provider is an explicit degraded result, not PASS for
  that provider.
- A zero-stub docgen result proves structural generation only; the mirrored
  Markdown must also pass independent operator-readability review.
- Any missing/stale mirror, fail-fast scaffold, unauthorized cache exposure,
  broken accepted trace, recovery mismatch, non-determinism, or unexplained
  rebalancer move is FAIL.

### 8.1 Frozen hostile-input boundaries

Production defaults may be configured downward, never disabled. MCP cases test
limit and limit-plus-one for: frame 1 MiB, headers 32 KiB, JSON depth 64,
method 128 bytes, URI 8 KiB, query 4 KiB, decoded string 256 KiB, aggregate
arguments 512 KiB, list 100, candidates 1,000, trace depth 8/nodes 2,000,
response 1 MiB, generated manual 200 lines/about 6,000 tokens, and 16 in-flight
requests. Expected typed failures are `frame_too_large`, `limit_exceeded`,
`invalid_request`, `unauthorized`, or `stale_cursor`, before protected effects.

Provider cases additionally test: 128 query tokens, 64 Boolean clauses, depth
8, 32 terms/phrase and 64 total phrase terms, 256 expansions, 32 filters, 64
values/filter, 1,000 hits, 128 explanation terms/hit, 32 fields/hit, 64 KiB
explanation/hit and 512 KiB/page, 1,000 delta documents, 64 fields/document,
1 MiB field value, 1,000 duplicate candidates total/100 per document, 1,000
symbols, and 50 ms..30 s client deadlines. Regex and leading unbounded wildcard
queries return `invalid_request`; budget/deadline exhaustion returns
`limit_exceeded`/`deadline_exceeded` without semantic truncation.

Transaction, rebalancer, and promotion cases assert typed
`precondition_failed`, `transaction_conflict`, `recovery_required`,
`unsupported_version`, `constraint_conflict`, `budget_exceeded`,
`unauthorized`, `provider_unavailable`, and `incompatible_contract` outcomes.
Prompt injection remains data; provider output, promotion content, licenses,
secrets, approval-token replay, symlink races, concurrent edits, and every
durability fault must fail closed without publication or mixed healthy state.

## 9. Manual and evidence policy

Each executable file begins with `# codex-system-test`, requirement comments,
an evidence-display policy, and a triple-quoted authored manual containing:

- purpose and audience;
- scope, exclusions, and preconditions;
- operator workflow using the applicable frozen step names;
- syntax and bounded examples;
- evidence and provenance;
- verification outcomes;
- recovery and troubleshooting;
- compatibility, privacy, and limitations.

Use `# @manual: show` only for the five primary workflows. Use
`# @manual: folded` or `detail` for matrices, failure injection, stress,
schemas, and internal checker cases. Complete executable source remains folded
for reproduction. Default evidence display is `links`; embed only compact text
that materially helps an operator.

Evidence paths are rooted under:

```text
build/test-artifacts/03_system/app/spipe/feature/<spec-name>/
```

Use capture kinds deliberately: `text` for search/trace summaries, `protocol`
for MCP exchanges, `exec` for process receipts, `log` for diagnostics/recovery,
and `artifact` for snapshots, journals, proposals, manifests, and hashes.
Credentials, private content, and authorization tokens must never be captured.

## 10. Execution order and exact commands

Run each acceptance command at most once after the relevant implementation is
ready. Do not rerun unchanged green gates.

```bash
bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl --mode=interpreter
bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl --mode=interpreter
bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl --mode=interpreter
bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl --mode=interpreter
bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --mode=interpreter
```

If the provider spec contains an admitted native-only Simple lane, run it with
stub fallback disabled:

```bash
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl --mode=native
```

Generate and assess each changed mirror separately:

```bash
bin/simple spipe-docgen test/03_system/app/spipe/feature/<name>_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/spipe/feature/<name>_spec.spl
```

If Simple MCP/LSP source or wrapper paths change, include the existing owner
gates exactly once:

```bash
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/check/check-mcp-native-smoke.shs
```

Before completion:

```bash
find doc/06_spec -name '*_spec.spl' | wc -l
```

The required result is `0`. Verification must also run the repository-required
runtime-facade audits and any additional Simple compiler/lib, MCP/LSP, database,
or package smoke gates activated by the actual changed paths.

### Scenario: Legacy identity migration is deterministic

- **Given** two schema-v1 snapshots with the same workspace/worktree `W-` identities but changed project membership and revision fields
- **When** both independently migrate to schema v2
- **Then** record type and legacy UID select identical `WS-`/`WT-` mappings, each migration records its own first v2 snapshot UID, and both v1 snapshots remain unchanged.

### Scenario: Edge authority fails closed

- **Given** forged, revoked, expired, wrong-policy, and wrong-edge receipts
- **When** strict trace is evaluated
- **Then** none satisfies an obligation and each produces a stable diagnostic.

### Scenario: Wave 2 edges migrate without gaining authority

- **Given** an immutable schema-v1 snapshot containing accepted edges without provenance or authority
- **When** Wave 3 loads it through the containing manifest
- **Then** deterministic v2 wrappers and migration records are produced, original bytes remain unchanged, and the edges satisfy advisory gates only.

### Scenario: Trace records must agree with their source owner

- **Given** scenario, symbol, and test records whose artifact, path, project, revision, or source-location owner disagrees
- **When** graph extraction validates them
- **Then** each produces `SPK004`, creates no node or edge, and clean and incremental roots remain equal.

### Scenario: Marker constructors are byte-deterministic

- **Given** CRLF/LF-equivalent normalized parser bytes, non-BMP Unicode titles/symbols, aliases, nested SSpec suites, and provider-backed symbol fixtures with exact artifact and section records
- **When** clean and incremental constructors parse requirement, NFR, scenario, symbol, and test markers
- **Then** every closed record field, source hash, half-open span, signature hash, and graph root is byte-identical, while malformed or mismatched markers emit `SPK003`/`SPK004` and no node.

### Scenario: One marker block creates scenario and test identities

- **Given** scenario-only, test-only, and ordered scenario-plus-test blocks before `it` declarations
- **When** the SSpec parser constructs records
- **Then** the dual block creates both nodes with matching scenario binding, while reversed, duplicated, separated, or mismatched blocks emit `SPK003` and no canonical records.

### Scenario: Source locations use required artifact content hashes

- **Given** artifacts with nullable provenance `source_hash` and required newline-normalized parser-byte `content_hash`
- **When** scenario, symbol, and test locations are constructed
- **Then** every location and span uses normalized UTF-8 parser bytes and `content_hash`, CRLF/LF forms produce equal identities, and raw-byte, UTF-16, code-point, line/column, version-mismatched, or hash-mismatched provider coordinates fail with `SPK406` rather than being translated.

### Scenario: Deferred Wave 2 edges remain historical

- **Given** schema-v1 generated edges plus `produces`, `promoted_from`, missing-endpoint, and unsupported-kind edges
- **When** migration maps generator fields and domain-separated hashes
- **Then** supported edges receive deterministic v2 wrappers, deferred/unsupported edges receive deterministic historical records, and none gains compliance authority.

### Scenario: Legacy W endpoints translate before edge hashing

- **Given** v1 edges and manifests containing workspace/worktree `W-` values
- **When** typed identity migration precedes edge migration
- **Then** unique mappings produce `WS-`/`WT-` v2 provenance/endpoints, while missing or ambiguous mappings remain historical with stable reasons.

### Scenario: Delta replay distinguishes identity and conflict

- **Given** one published graph delta
- **When** the identical delta and a different same-base delta are replayed
- **Then** the identical replay returns its original byte-identical successful
  response, while the different delta is stale.

### Scenario: Snapshot pins cannot cross lifetime or store

- **Given** released, expired, wrong-store, and wrong-scope pins
- **When** each performs a graph lookup
- **Then** lookup fails before reading graph data.

### Scenario: Graph budgets paginate deterministically

- **Given** fixtures exceeding edge, node, work-unit, and trace-row limits
- **When** reads continue through authenticated cursors
- **Then** exhaustion reports reason/counters and continuation yields each authorized result exactly once.

## 11. Manual-quality review gate

For every generated mirror, an independent reviewer must confirm:

1. the purpose, audience, preconditions, trust boundary, and exclusions survive
   generation;
2. applicable frozen steps appear in operator order;
3. setup/checker helpers are either visible steps or present in complete folded
   executable source;
4. expected results say what the operator observes, not merely that a function
   was called;
5. recovery explains stale cache, unavailable provider, rejected transaction,
   interrupted apply, and rollback;
6. compatibility distinguishes legacy stdio, MCP 2026, materialized views,
   editor adapters, and deferred FUSE/ProjFS;
7. evidence carries revision, fixture, provider/version, command, exit status,
   elapsed time, and hashes where applicable;
8. no optional, inferred, source-only, or readiness evidence is promoted into a
   stronger PASS claim.

`sspec-maintain scan` must show a current mirror, no blocker cap, no fail-fast
scaffold, and acceptable independent scores. Docgen must report the affected
spec complete with `0 stubs`.

## 12. Exit gate

This test-design increment includes all five planned executable RED scaffolds
and five authored non-generated mirrors. It is complete when the architecture
and detail design publish the interfaces used by the fixtures/checkers and a
highest-capability reviewer accepts the planned evidence boundaries.
Implementation completion remains unproven until fail-fast helpers are replaced
with production oracles, mirrors are regenerated and independently reviewed,
receipts are retained, Wave 0 qualifies absolute latency budgets, and every
applicable command records one verified PASS.

## 13. Wave 4 search-provider acceptance freeze

<!-- codex-design -->

This section refines Sections 5.3, 6, 7, and 8 with the completed Wave 4
audits. It freezes executable vocabulary rather than adding a second
requirements namespace. Coverage remains on `REQ-SPKC-011` through
`REQ-SPKC-016` and the applicable NFR IDs already allocated
above. Tests and receipts must name these exact contracts:
`spipe-search-provider/1.0`, `spipe-unicode-lex-v1`, `bm25-fixed-v1`,
`bm25-explain-v1`, `spipe-lexical-snapshot-v1`, and `rrf-fixed-v1`.

### 13.1 Frozen helpers and fixtures

Provider-conformance code uses only these shared helper names:

- `loadSearchGoldenCorpus`
- `runProviderConformance`
- `assertCanonicalSearchPage`
- `buildIndexFromCorpus`
- `applyGoldenDeltaSequence`
- `assertCleanIncrementalParity`
- `assertExplanationBoundedAndCanonical`
- `measureQualifiedSearch`
- `createJsProviderFixture`
- `createSimpleProviderFixture`

Their signatures are frozen as
`loadSearchGoldenCorpus()`,
`runProviderConformance(suiteContext)` with the closed context in Section 13.7,
`assertCanonicalSearchPage(actual, expected)`,
`buildIndexFromCorpus(port, corpus)`,
`applyGoldenDeltaSequence(port, deltas)`,
`assertCleanIncrementalParity(factory, corpus, deltas)`,
`assertExplanationBoundedAndCanonical(hit)`,
`measureQualifiedSearch(provider, fixture, repetitions)`,
`createJsProviderFixture()`, and `createSimpleProviderFixture()`.

The checked-in golden corpus must carry a canonical fixture hash and cover all
five ordered fields—`identifier`, `title`, `heading`, `classification`, and
`body`—with weights `4000/4000/2500/2000/1000` milli. It includes empty and
missing fields, zero/one/many-document corpora, repeated terms, ties, unsigned
UTF-8 document-ID ordering, stop-word position gaps, valid non-BMP Unicode,
combining sequences, NFC equivalents, invalid UTF-8 rejection, overflow
boundaries, facets, private documents, deletes, and stale replace preconditions.

The exact fixture locations are:

- `examples/05_stdlib/spipe/test/fixture/wave4_search/golden_corpus.json`
- `examples/05_stdlib/spipe/test/fixture/wave4_search/golden_results.json`
- `examples/05_stdlib/spipe/test/fixture/wave4_search/fusion_results.json`

JavaScript unit ownership is
`examples/05_stdlib/spipe/test/unit/{search_analyzer_test.js,search_bm25_test.js,search_index_test.js,search_fusion_test.js,search_provider_protocol_test.js}`;
integration ownership is
`examples/05_stdlib/spipe/test/integration/knowledge_wave4_search_test.js`.
Simple unit ownership is
`test/01_unit/lib/common/search/{ranking_spec.spl,analyzer_spec.spl,document_spec.spl,query_spec.spl,top_k_spec.spl,provider_spec.spl,explain_spec.spl,snapshot_spec.spl`.
DBFS parity extends
`test/02_integration/storage/dbfs/fts_engine_spec.spl`; the system owner remains
`test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl`.

### 13.2 Exact Wave 4 matrix

| Matrix ID | Required oracle | Required implementations |
|---|---|---|
| `W4-SRCH-01` Analyzer parity | exact normalized tokens, positions, exact identifier token, and rejection agree for the pinned Unicode table | JavaScript and Simple |
| `W4-SRCH-02` Checked BM25 | exact integer scores, per-field statistics/contributions, one public-milli conversion, and score/unsigned-UTF-8-ID ordering agree | exhaustive JS, common Simple, DBFS facade |
| `W4-SRCH-03` Explanation | `bm25-explain-v1` is bounded, canonical, recomputes the hit score, and contains no unauthorized field/value | every lexical adapter |
| `W4-SRCH-04` Logical root | clean builds across providers produce the same `spipe-lexical-snapshot-v1` root | JavaScript, Simple process, DBFS facade |
| `W4-SRCH-05` Delta parity | sorted UID-disjoint add/replace/delete; exact-present and paired-null expected-absence delete preconditions; mixed-null rejection; unchanged-root no-op; byte-identical original result/envelope/receipt replay; conflict, CAS, and mixed-history result equal clean rebuild | JavaScript and Simple; DBFS compatibility path |
| `W4-SRCH-06` Protocol bounds | eight lowercase-hex framing, canonical UTF-8 JSON, 1 MiB limit, correlation, deadlines, cancellation, and response validation fail closed | process adapter and adversarial provider fixture |
| `W4-SRCH-07` Health/fallback | closed health transitions, poisoned-generation quarantine, crash fallback with same-root rebuild, at-most-one retry, and no mixed page/cursor | process adapter plus JavaScript fallback |
| `W4-SRCH-08` Query v1 | distinct bag terms and equality facets are deterministic; phrase handshake is `false` and phrase syntax returns `unsupported_capability` | every v1 provider/adapter |
| `W4-SRCH-09` Qualified performance | persistent provider, no hot full-tree reads/spawns, raw latency/RSS receipt, and functional parity under benchmark load | each implementation claimed production-ready |

`runProviderConformance` executes `W4-SRCH-01` through `W4-SRCH-08` against
the same corpus and returns structured per-matrix evidence. It must not convert
an unavailable implementation into PASS. `assertCanonicalSearchPage` checks
score order, unsigned UTF-8 ID ties, snapshot/query bindings, visibility, and
canonical explanation. `assertCleanIncrementalParity` compares logical root,
ordered pages, exact scores, corpus statistics, and explanations—not merely hit
sets.

### 13.3 System scenarios and manual allocation

The provider-parity SSpec contains these exact scenario titles:

1. `should return identical golden ordering and scores across fallback and Simple providers`
2. `should keep exact identity dominant and break lexical ties by public document ID`
3. `should reject phrase queries and apply metadata equality filters identically in version 1`
4. `should return bounded canonical explanations for every ranked hit`
5. `should make mixed incremental deltas equal a clean rebuilt snapshot`
6. `should degrade process and semantic provider failures without a false semantic pass`
7. `should reject every query and response resource boundary at limit plus one`
8. `should meet qualified warm-query and incremental-update latency gates`

The third title deliberately replaces the pre-freeze draft wording “apply
phrase queries”: `phrase=false` is normative in v1, so executing phrases as if
supported would be a contract failure.

Detailed scalar, arithmetic, corruption, and limit rows remain folded in the
manual. The visible workflow remains `Search and trace artifacts`, invokes
`check_spipe_provider_parity`, and captures compact score/explanation evidence
as `text`, protocol transitions as `protocol`, degradation/quarantine as `log`,
and the logical-root/delta/performance receipts as `artifact`.

### 13.4 Performance qualification rule

`measureQualifiedSearch` must record machine/CPU and memory, OS, toolchain,
build identity/mode, provider and contract versions, fixture hash and document/
token/byte sizes, warm-up count, measured sample count, percentile algorithm,
raw samples, P95, maximum RSS, command, exit status, and timestamp. The receipt
must separately prove zero per-query process spawns and zero warm-query
full-tree scans/repeated source reads. Functional parity and enforced limits
remain prerequisite gates.

The qualified fixture contains exactly 50,000 artifacts and freezes its
content hash, analyzer identity, and score identity. It also records CPU model
and core policy, RAM, OS/kernel, runtime and provider binary hashes, cold/warm
state, repetitions, percentile method, peak RSS, index bytes, and cache bytes.
After a checked-in Wave 0 profile qualifies those inputs, its release gates are
warm lexical P95 below 100 ms, one-document publication P95 below 100 ms, and
full-rebuild median divided by incremental median at least `20.0`. The provider
must start exactly once with no per-query spawn, warm full-tree scan, or
repeated source read. Degradation runs are measured separately and excluded
from steady-state samples. Missing qualification metadata is `NOT EVIDENCE`,
never PASS.

Until a checked-in profile freezes hardware class, fixture, warmups, samples,
variance rule, and absolute budget, the research values such as 50,000
documents and warm P95 below 100 ms are qualification targets only. A timing
run may report observations but must not claim an absolute performance PASS.

### 13.5 High-review closure matrix

The following cases are additions to the exact Wave 4 matrix and must be red
before their implementation exists:

| Matrix ID | Exact evidence |
|---|---|
| `W4-SRCH-10` UCD provenance | UCD 17.0.0 generator manifest has real source/generated hashes; clean regeneration is byte-identical; complete normalization and default-lowercase vectors match JS/Simple; host locale/engine variation changes nothing |
| `W4-SRCH-11` Scope isolation | two principals and policy versions receive distinct scope-bound roots/cursors/caches; private/redacted documents cannot affect public `N`, `df`, lengths, averages, scores, counts, explanations, or error shape |
| `W4-SRCH-12` Canonical JSON | exact golden bytes/hashes match across JS/Simple for NFC/key ordering/integer/escape boundaries; duplicate normalized keys, `-0`, exponent/fraction, invalid UTF-8, NaN/infinity, trailing bytes/newline, and frame length including header are rejected |
| `W4-SRCH-13` Arithmetic order | every normative BM25 and fixed-ln intermediate matches golden integers, averages floor once, public milli converts once, and all invalid-stat/overflow/range-reduction boundaries return the exact typed error |
| `W4-SRCH-14` Negotiation schema | protocol object is required; all five provider-side contract IDs and negative capabilities negotiate; closed init/request/success/error records reject missing/extra/wrong fields and mismatched bindings; provider-supplied fusion authority is rejected |

Additional checked-in fixtures are
`unicode_17_0_0_manifest.json`, `canonical_json_vectors.json`,
`authorization_scope_vectors.json`, `bm25_intermediates.json`, and
`provider_protocol_vectors.json` under
`examples/05_stdlib/spipe/test/fixture/wave4_search/`. The UCD generated-table
artifacts and non-placeholder manifest hashes are a Wave 4 pre-implementation
gate, not documentation-only intent.

`runProviderConformance` must execute `W4-SRCH-01` through `W4-SRCH-14`.
`assertCanonicalSearchPage` additionally verifies `scope_digest` and proves the
explanation can mechanically reconstruct the public score. Protocol tests feed
fragmented and coalesced frames and assert that the eight lowercase hex bytes
count only canonical JSON payload bytes. Fallback tests verify a new generation
and identical authorized logical root; they reject mixed pages, cursors,
statistics, caches, or scope partitions. Performance tests cannot begin until
all correctness matrices pass.

### 13.6 Wire-operation closure cases

Extend `W4-SRCH-14` with a table-driven case for every operation:
`index_open`, `index_apply`, `index_publish`, `search`, `explain`,
`duplicate_candidates`, `symbols_snapshot`, `stats`, `cancel`, and `shutdown`.
For each, assert its exact request and result schema, null policy, type and
limit boundaries, missing/extra/duplicate-normalized fields, and bound error.
Wave 4 must prove `duplicate_candidates`, `symbols_snapshot`, phrase, regex,
wildcard, and semantic capabilities are false and return a fully bound
`unsupported_capability`, never a success or unbound generic error.

Error fixtures separately cover:

- initialize rejection plus every syntactically valid pre-initialization
  operation returning the closed `PreBindingErrorResponseV1`
  `handshake_required`, echoing only request ID, operation, and protocol;
- malformed length, UTF-8, JSON, canonicality, unknown operation, or an
  undecodable correlation triple closing the connection/process with no
  fabricated response;
- every post-initialization failure echoing request ID, operation, protocol,
  provider generation, workspace, snapshot, scope digest, and the exact query
  receipt/null and operation receipt/null policy;
- one-field mismatches in each bound success/error quarantining the complete
  generation.

Search matrices prove equality filters are conjunctive, term candidates use
at-least-one-term scoring semantics, empty analyzed text requires a filter,
explain-null parity, and authenticated pagination yields every authorized hit
once across multiple pages. Delta matrices prove complete documents are sent
from the published compiler projection, never reread from the repository;
before-revision/hash, operation payload hash, replay receipt, candidate root,
and publish CAS are all bound. Delete fixtures freeze both choices: a non-null
revision/hash pair must match one present base document exactly; a null/null
pair must find the base document absent. Expected absence returns a
zero-`deleted`, unchanged-root `no_op` candidate, whereas a present document is
`precondition_conflict`; either mixed-null pair is `invalid_request` before any
candidate or receipt exists. The canonical payload retains both nulls.

Add canonical JSON vectors for `9007199254740991`,
`-9007199254740991`, rejected `±9007199254740992`, signed i64 extrema,
fraction/exponent/`-0`, and the exact signed-i128 decimal-string extrema plus
one beyond each bound. Golden explanations assert every conceptual wide field
has one fixed representation and cannot switch between JSON number and string.

### 13.7 Stateful provider and explanation closure

Replace the old two-argument conformance abstraction with the frozen suite
context:

```text
runProviderConformance({
  corpus, expected, jsFactory, simpleFactory, dbfsFactory,
  adversarialFactory, authorizationFixtures, fallbackFixture,
  applicability
}) -> [ConformanceResult]
```

`ConformanceResult` is exactly `{matrix_id, implementation, applicability,
status, evidence_path, reason}`. Applicability is `required` or
`not_applicable`; status is `pass`, `fail`, or `not_evidence`. A required
implementation/fixture missing, unavailable, unsupported, or skipped is
`fail`. `not_applicable` needs a contract-cited reason and yields
`not_evidence`, never PASS. DBFS scope isolation is required only when its
advertised capability accepts that scope; otherwise the required result is a
pre-statistics `unsupported_scope` test.

Extend the matrix:

| Matrix ID | Exact evidence |
|---|---|
| `W4-SRCH-15` Explanation closure | closed nested explanation arrays obey authorization/order/bounds/type rules and mechanically recompute every score/tie |
| `W4-SRCH-16` Scoped projection | full five-field documents derive canonical authorized subsets; absent/redacted fields disappear from root/stats/explanation; DBFS fails unsupported scopes before reads |
| `W4-SRCH-17` Signed receipts | query, operation, and separate candidate-expiry receipt IDs/signatures bind distinct domains, non-circular omitted fields, authority ID/generation, request or candidate/apply identity, scope/root/policy, time/revocation; restart replay returns identical durable bytes |
| `W4-SRCH-18` Candidate lifecycle | concurrent candidates coexist; a still-staged candidate losing the current-root CAS returns typed success `stale_base` with its own signed receipt; publish/abort/authority-expiry candidate-state races have one winner, and losing requests receive their own journaled bound terminal error with null receipt, never the winner receipt; corruption and restart/replay are deterministic and nonpublishing |
| `W4-SRCH-19` Error taxonomy | each invalid N/df/average/denominator/array/log input/overflow/canonical/binding case returns its exact code and no generic substitute |
| `W4-SRCH-20` Cancellation lifecycle | cancel/deadline races order immediately before versus after the combined terminal transaction; before prevents root/candidate/receipt/metadata commit, after returns/replays the signed terminal result; an unknown target is exactly bound `cancel_target_not_found` with `retryable:false` and null receipts; shutdown rejects, cancels, drains, and restarts deterministically |

This increment extends `runProviderConformance` through `W4-SRCH-20`; the final
required range is frozen in Section 13.8. Add fixtures for explanation nesting/recomputation,
authorized field subsets, Ed25519 valid/forged/wrong-key/revoked/expired
receipts, durable restart replay, candidate races/abort/expiry/CAS loss, every
error code, and deterministic cancel/deadline/shutdown schedules. Each receipt
test retains canonical unsigned bytes, signature, public-key fingerprint,
policy/revocation generation, and durable replay evidence without private keys.

### 13.8 Cycle-2 closure evidence

| Matrix ID | Exact evidence |
|---|---|
| `W4-SRCH-21` Scoped provider bytes | only closed `ScopedSearchDocumentV1` crosses provider/delta/root boundaries; scoped content hash excludes unauthorized fields; stats exactly match authorized field count/order and reject mismatch |
| `W4-SRCH-22` Contribution union | absent terms carry exact zero/null fields without denominator work; scored terms carry every fixed-type intermediate; exact qtf and mechanical total reconstruction agree |
| `W4-SRCH-23` Receipt wire objects | envelopes carry full signed query/operation objects or null, never IDs; candidate expiry uses only `CandidateExpiryReceiptV1` in authority/audit storage; all three domains, length framing, omitted-field sets, authority bindings, revocation/time, byte echo, and restart replay are exact |
| `W4-SRCH-24` Complete errors | every closed error code is triggered by its named operation; snapshot, semantic, protocol, cancellation, internal, and fatal cases cannot collapse or publish |
| `W4-SRCH-25` Candidate terminality | each terminal winner pre-signs its receipt; published atomically commits root pointer + terminal candidate + receipt + publication metadata, while stale/abort atomically commit candidate + receipt without root; candidate-state losers atomically fsync `DurableTerminalErrorV1`; restart preserves every result byte-for-byte |
| `W4-SRCH-27` Replay identity and absence delete | apply/publish replay has no replay-only status or outcome and returns the original canonical envelope plus signed receipt byte-for-byte across restart; paired-null delete hashes both nulls, yields an unchanged-root signed `no_op` only when absent at base, conflicts when present, and rejects mixed pairs before mutation |
| `W4-SRCH-26` Initialize closure | exact nested contracts, capabilities, limits, ID arrays, optional fields, minor-version rules, maxima, and negotiated-minimum identity reject every mutation |

`runProviderConformance` executes `W4-SRCH-01` through `W4-SRCH-27` after this
freeze. Add scoped-document/hash/stat mismatch fixtures; absent/scored
contribution vectors; receipt objects with altered domain, length, omitted
field, key, revocation generation, and signature; every error-code operation;
deterministic three-way candidate races across restart; and initialization
limit/ID/unknown-key/optional-field matrices. Missing any required fixture is
FAIL under the suite-context policy, not a skipped PASS.

`provider_protocol_vectors.json` must also carry the exact normative bytes from
detail-design Section 14.17.1. Tests assert: the 176-byte
`handshake_required` payload, `000000b0` frame header, and published SHA-256;
the 456-byte unknown-cancel bound error, `000001c8` header, published SHA-256,
`retryable:false`, and both null receipts; and the 880-byte unsigned
`CandidateExpiryReceiptV1` with required policy fields and domain plus u64be
length yielding receipt ID suffix
`5bf2e3a55ccfba6130ed059cb4c063c0db39b0f4fbf4845953cabbdf06c268cc`.
The former 771-byte no-policy record is rejected and its independently checked
NUL-domain hash is
`f13c7cce500d3d29b81c75880195f8ffcba4006ad16313a69ac1a43294731d40`.
Each operation is sent once before initialize: all syntactically valid closed
requests produce the same closed pre-binding error shape, while each malformed
framing/canonicality mutation produces EOF with zero response bytes. The
candidate race fixture fault-injects before and after the one atomic terminal
transaction, persists, restarts, and byte-compares (a) the
winner's receipt, (b) the authority expiry receipt when expiry wins, (c) a
stale-current-root success and its own receipt, and (d) every candidate-CAS
loser's separately atomic `DurableTerminalErrorV1` and bound null-receipt
response. Substitution of any winner receipt into a loser response is an
explicit failure.

The terminal-transaction fixture injects failure at three named points:
`before_terminal_transaction`, `inside_terminal_transaction`, and
`after_terminal_transaction_before_response`. After restart, the first exposes
the old root and staged candidate with no terminal receipt/metadata; the second
must expose either that complete old tuple or the complete new tuple, never a
split; the third exposes and replays the complete signed terminal result. For a
published tuple, root pointer, terminal candidate, operation receipt, and
publication metadata appear together. For stale-base/abort, candidate and
receipt appear together and root/metadata remain unchanged/absent. Cancel and
deadline schedules at the same boundaries prove the pre-transaction winner
prevents the commit and the post-transaction loser returns `already_complete`
or the signed terminal response.

Exact payload/identity vectors assert: 136-byte apply payload without its hash
maps to `53eac50845e9d3c9014580d3136062cb03e36c7863f947124e63bb674e38308f`;
the 245-byte paired-null absence-delete payload maps to
`9f3366f906834cadde2ea4b02494f47f8dc80f37418729785841e7209d1d9f08`;
the 277-byte publish payload maps to
`cf61ac4db6bd270c671a5dd63e47bcc990714d2390cfe14acbfe6131e9042eee`;
and the closed 424-byte candidate record maps to
`cand-4adcb8c9713f37d79044d0130b7117f7a4c8d1b3e57a255a9a34be40ffbdb191`,
using the three distinct NUL-terminated domains and
u64be lengths in detail-design Sections 14.12 and 14.17. Tests reject inclusion
of `payload_hash` in its own preimage, omission of any other field/empty array,
omission of either absence null, either mixed-null delete variant, hashing the
`cand-` prefix, wrong domains/terminators, noncanonical JSON, and raw
concatenation. Apply and publish are each executed, persisted, restarted, and
replayed; the second response must equal the first complete frame byte-for-byte
and retain the original status and receipt outcome.
