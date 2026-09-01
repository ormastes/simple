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
- accept the one canonical workspace-root URI
  `spipe://workspace/{workspace}/` and reject its un-slashed near miss;
- use a branded signed `AuthorizationPortV1`, rejecting duck-typed verifiers,
  invalid algorithm/issuer/key/epoch, malformed signature, expired/revoked
  receipt, and receipt payloads whose authority/workspace/project/snapshot/
  revision/view/normalized-path/selector/scope/ordering/page-limit binding
  differs from the request; prove that the verified-read grant carries a
  sealed, trusted worktree binding and that cursor issue cannot derive it;
- accept one fully authorized canonical read and one next-page cursor in the
  same complete authority/workspace/project/snapshot/revision/view/path/
  selector/scope/ordering/page-limit tuple, then reject cursor reuse across
  every bound field, a foreign workspace selector, legacy-alias remap, changed
  ordering/version, and changed page limit. Cover cursor issuer/signature,
  expiry, and revocation failure independently;
- exercise raw/once-encoded/double-encoded traversal and separators, NUL,
  controls, malformed percent escapes, Windows device/ADS forms, empty IDs,
  duplicate query parameters, hostile receipt/cursor bytes, and every public
  admission error. Assert identical public `not_found_or_unauthorized` class
  and bounded content-free work for malformed, foreign-selector, receipt- or
  cursor-failure, stale-cursor, hidden, unknown, and unauthorized targets;
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
limit and limit-plus-one for: frame 1 MiB, headers 32 KiB, JSON depth 16,
262,144 lexical tokens, 65,536 aggregate object-pair/array-element members,
method 128 bytes, URI 8 KiB, query 4 KiB, decoded string 256 KiB, aggregate
arguments 512 KiB, list 100, candidates 1,000, trace depth 8/nodes 2,000,
response 1 MiB, generated manual 200 lines/<=6,000 `spipe-markdown-token-v1@1` tokens, and 16 in-flight
requests. Expected typed protocol-envelope failures are `frame_too_large`,
`limit_exceeded`, or `invalid_request`; any attempted read admission is the
single public `not_found_or_unauthorized` class before protected effects.

Provider cases additionally test: 128 query tokens, 64 Boolean clauses, depth
8, 32 terms/phrase and 64 total phrase terms, 256 expansions, 32 filters, 64
values/filter, 1,000 hits, 128 explanation terms/hit, 32 fields/hit, 64 KiB
explanation/hit and 512 KiB/page, 1,000 delta documents, 64 fields/document,
1 MiB field value, 1,000 duplicate candidates total/100 per document, 1,000
symbols, and inclusive 1 ms..30 s client deadlines measured from acceptance of
the first frame-header byte. Regex and leading unbounded wildcard
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
# Provider parity is excluded here; it has the admitted-runtime commands below.
bin/simple test test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --mode=interpreter
```

Provider parity and its controlled-work imports use only one admitted absolute
Stage 4 executable/provenance pair. These commands replace, rather than
supplement, any `bin/simple` provider-parity command:

```bash
export SPIPE_SIMPLE_BIN=/absolute/admitted/simple
export SPIPE_STAGE4_PROVENANCE=/absolute/admitted/stage4-candidate.sdn
cd examples/05_stdlib/spipe && npm run test:wave4-conformance
cd /absolute/simple-worktree
"$SPIPE_SIMPLE_BIN" check test/fixtures/spipe_controlled_work/controlled_work_proof.spl
"$SPIPE_SIMPLE_BIN" test test/01_unit/app/spipe_knowledge_provider/provider_controlled_work_import_smoke_spec.spl --mode=interpreter
"$SPIPE_SIMPLE_BIN" test test/01_unit/app/spipe_knowledge_provider/provider_deadline_control_spec.spl --mode=interpreter
"$SPIPE_SIMPLE_BIN" test test/01_unit/app/spipe_knowledge_provider/provider_streaming_limits_spec.spl --mode=interpreter
"$SPIPE_SIMPLE_BIN" test test/01_unit/app/spipe_knowledge_provider/provider_session_owner_spec.spl --mode=interpreter
"$SPIPE_SIMPLE_BIN" test test/01_unit/app/spipe_knowledge_provider/provider_stats_count_explain_spec.spl --mode=interpreter
"$SPIPE_SIMPLE_BIN" test test/01_unit/compiler/import/spipe_controlled_work_import_regression_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 "$SPIPE_SIMPLE_BIN" test test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl --mode=native
"$SPIPE_SIMPLE_BIN" spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl --output doc/06_spec --no-index
"$SPIPE_SIMPLE_BIN" sspec-maintain scan test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl
```

The conformance command invokes the canonical Stage 4 candidate-provenance
verifier before any Simple probe. Each later command consumes the same absolute
path and the retained conformance receipt binds that binary/provenance hash.
Missing planned specs are an unimplemented/red gate, never a reason to delete a
command or fall back to an available bootstrap.

Generate and assess each changed mirror separately:

```bash
bin/simple spipe-docgen test/03_system/app/spipe/feature/<name>_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/spipe/feature/<name>_spec.spl
```

Those generic commands exclude the provider-parity mirror, whose exact
admitted-runtime docgen/assessment commands are frozen above.

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
- **Then** record type and legacy UID select identical `WS-`/`W-` mappings, each migration records its own first v2 snapshot UID, and both v1 snapshots remain unchanged.

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
- **Then** unique mappings produce `WS-`/`W-` v2 provenance/endpoints, while missing or ambiguous mappings remain historical with stable reasons.

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
`measureQualifiedSearch(profile_path, fixture_path, operation_plan_path,
functional_receipt_uri, output_path)`,
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

`measureQualifiedSearch` has only the frozen five-argument signature in detail
design Section 14.6 and must record machine/CPU and memory, OS, closed
toolchain/compiler and collector-runtime identities, versions, and binary hashes,
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

The W4-SRCH-09 oracle accepts only the closed
`spipe-qualified-search-receipt-v1` defined by detail-design Section 14.6.1.
It first validates the closed `spipe-qualified-search-profile-v1`: exact
subject, host/kernel/CPU/core-policy and adapter identities; inclusive CPU and
minimum-memory bounds; positive budgets; at least one warmup and twenty
samples; and the integer MAD variance rule with no discarded or retried
samples. An unqualified host or adapter is `NOT EVIDENCE`.
The checker recomputes all file hashes, sample cardinalities, nearest-rank P95,
lower-middle medians, and the fixed-point rebuild/publish ratio; verifies the
functional-conformance receipt; and requires one provider start, zero
per-query spawns, zero warm full-tree scans, and zero repeated source reads.
It also checks that the fixture manifest binds exactly 50,000 artifacts, the
query-plan hash and query count, and the admitted binary/provenance hashes.
Warm startup is one scalar, warm-query evidence contains exactly the bound
repetition count times query-plan cardinality, and max RSS comes from a
profile-approved OS process-tree peak counter. It also verifies the canonical
functional-conformance receipt URI and hash and the canonical
`benchmark_operation_plan_v1.json` path and hash. The plan encodes the exact
warmup and measured-round schedule, query-before-mutation rule, alternating
publish/rebuild order, untimed byte-identical `S0` resets, and expected `S0`/`S1`
hashes from detail design Section 14.6.1.

The functional prerequisite is exactly one closed canonical-JSON object:

```text
schema = "spipe-functional-conformance-receipt-v1"
subject = {implementation, provider_id, provider_version,
           protocol_version, analyzer_id, score_id}
executable = {canonical_path, sha256, stage4_provenance_sha256}
fixture = {id, sha256, snapshot_sha256, query_plan_sha256}
scope = {principal_scope_digest, policy_version}
matrix = [{id, status = "passed", evidence_sha256}]
result = {status = "passed", checker_id, checker_version,
          checker_sha256, completed_at_utc}
```

Every leaf except `matrix` is a nonempty UTF-8 string; every SHA-256 and scope
digest is exactly 64 lowercase hexadecimal characters. `matrix` contains each
required `W4-SRCH-01` through `W4-SRCH-08` and `W4-SRCH-10` through
`W4-SRCH-39` ID exactly once in ascending numeric order, with no other ID; it
explicitly excludes performance cell `W4-SRCH-09`. Ordering is acyclic:
functional conformance produces this receipt first, then qualified performance
consumes it and alone evaluates `W4-SRCH-09`; cell 09 is never a prerequisite
of the receipt it consumes. The checker requires byte-equal subject, executable,
fixture, and scope bindings to the benchmark inputs. Unknown, missing, null,
duplicate-normalized, wrong-typed, failed, duplicate, or out-of-order fields or
entries are `NOT EVIDENCE`.

The operation plan is exactly one closed canonical-JSON object:

```text
schema = "benchmark-operation-plan-v1"
plan_id = nonempty ASCII identifier
fixture = {id, sha256, query_plan_sha256}
counts = {warmup_count, sample_count, query_count_per_sample}
states = {s0_snapshot_sha256, s1_snapshot_sha256}
delta = {artifact_id, delta_sha256, before_revision,
         before_content_sha256, after_revision, after_content_sha256}
reset = {method = "restore-canonical-s0-v1", expected_snapshot_sha256}
queries = [{query_index, query_id, canonical_request_sha256,
            expected_result_sha256}]
warmup_rounds = [{round_index, operations}]
measured_rounds = [{round_index, operations}]
```

Counts and indices are non-negative JSON safe integers; counts are positive.
Digests are 64 lowercase hexadecimal characters and all other leaves are
nonempty UTF-8 strings. Query indices are contiguous from zero and array order
is execution order. Each `operations` array uses only `verify_s0`,
`query_all`, `publish_delta`, `reset_s0`, `rebuild_s0`, and `verify_s1`.
Warmup rounds encode the fixed discarded schedule; measured even and odd rounds
encode the two required alternating schedules, with `query_all` before either
mutation and an ending `reset_s0`. The arrays have exactly the declared counts,
their indices are contiguous, and their query cardinality equals
`query_count_per_sample`. `reset.expected_snapshot_sha256` equals
`states.s0_snapshot_sha256`; the delta's before/after bindings produce exactly
S0/S1. Canonicalization is `canonical-json-v1`: UTF-8 without BOM or trailing
LF, NFC strings, unsigned decimal safe integers, lexicographically sorted NFC
object keys, and preserved array order. Unknown, missing, null,
duplicate-normalized, wrong-typed, inconsistent, or noncanonical input is
`NOT EVIDENCE`; its SHA-256 covers those exact canonical bytes.

For every timed request the checker recomputes the canonical result SHA-256,
requires it to equal the operation plan's expected SHA-256 with status
`matched`, and pairs its duration with the raw duration array. The ratio is the
checked integer `floor(rebuild_median_ns * 1000 / publish_median_ns)`; zero or
overflow is `NOT EVIDENCE`, and the initial gate is `>= 20000`.

Guard and RSS evidence comes from an independent, pre-launch platform adapter
and a hash-chained canonical event journal. The checker replays the journal to
recompute containment membership, peak RSS, provider starts, query-window
spawns, warm full-tree enumerations, and repeated unchanged-source reads. The
lifecycle includes every descendant through exit even after reparenting. Event
loss, journal-chain failure, self-reported counters, post-launch attachment, an
escaped or unenumerated descendant, or an adapter without fail-closed lifecycle
support is `NOT EVIDENCE`.
The journal oracle also enforces canonical UTF-8 JSONL, contiguous sequences,
predecessor and terminal hashes, opened-root device/inode or volume/file
identity, kernel-level create/exec/enumerate/open semantics, zero overflow/loss
and zero live terminal members. Textual-prefix or provider-log inference is not
evidence.

Every closed event additionally contains `source_version`,
`source_content_sha256`, and `source_change_witness = {kind,
identity_generation, size_bytes, modified_time_ns, witness_sha256}`. For
`source_open` and `source_change` events, `source_version` is a non-negative safe
integer and `source_content_sha256` is exactly 64 lowercase hexadecimal
characters. Non-source events use `source_version = 0`,
`source_content_sha256 = ""`, and the typed zero/empty-string witness sentinel.
A successful `source_open` must carry the current per-path-identity
version, the hash of the exact bytes read, and a witness derived by the approved
adapter from the opened handle; a `source_change` event is added to the event
enum and must increment that identity's version and bind the new content hash
and witness before a later open is attributed. Replay classifies a reread as
unchanged only when path identity, version, content hash, and witness all match
and no intervening `source_change` exists. Missing, regressing, skipped, or
contradictory versions, hashes, or witnesses are `NOT EVIDENCE`, making an
unchanged-source reread mechanically replayable rather than inferred from path.

Unknown or missing fields, null samples, a seed/source-mode
binary, an unqualified host/profile, or a nonzero collector exit is
`NOT EVIDENCE` and cannot be converted to PASS by the system scenario.

The sole planned collection command is the command in detail-design Section
14.6.2. Test automation may validate a checked-in receipt but must not silently
rerun a performance measurement. Until an admitted Stage 4 executable and a
checked-in qualified profile exist, the scenario retains its fail-fast oracle.

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
| `W4-SRCH-24` Complete errors | bound `ProviderErrorV1` codes are triggered through applicable named operations; `invalid_utf8`/`frame_too_large` remain payload-free local `TransportDiagnosticV1` decoder classes, pre-binding failures close silently without a fabricated `ProviderResponseV1`, and snapshot, semantic, protocol, cancellation, internal, and fatal cases cannot collapse or publish |
| `W4-SRCH-25` Candidate terminality | each terminal winner pre-signs its receipt; published atomically commits root pointer + terminal candidate + receipt + publication metadata, while stale/abort atomically commit candidate + receipt without root; candidate-state losers atomically fsync `DurableTerminalErrorV1`; restart preserves every result byte-for-byte |
| `W4-SRCH-27` Replay identity and absence delete | apply/publish replay has no replay-only status or outcome and returns the original canonical envelope plus signed receipt byte-for-byte across restart; paired-null delete hashes both nulls, yields an unchanged-root signed `no_op` only when absent at base, conflicts when present, and rejects mixed pairs before mutation |
| `W4-SRCH-26` Initialize closure | exact nested contracts, capabilities, limits, ID arrays, optional fields, minor-version rules, maxima, and negotiated-minimum identity reject every mutation |

`runProviderConformance` executes `W4-SRCH-01` through `W4-SRCH-39` after this
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

### 13.9 Streaming, controlled-work, and admitted-runtime closure

<!-- codex-design -->

Protocol `spipe-search-provider/1.0` still carries exactly one logical request
and at most one logical response per frame. “Streaming” in this section means
incremental transport reads/writes and cooperative bounded computation; it does
not permit chunked result semantics, partial pages, more than one JSON value in
a frame, or a response whose meaning depends on OS read boundaries.

The production ownership vocabulary is frozen as `ProviderByteStreamPort`,
`ProviderFrameDecoderV1`, `ProviderFrameEncoderV1`,
`ProviderRequestControlPort`, `ProviderWorkMachineV1`, and
`ProviderSessionOwnerV1`. Tests compile against the exact Section 4.1 focused-
architecture signatures rather than defining aliases. `ProviderByteStreamPort`
read/write results each use `data | timeout | eof | error` and each call carries
an absolute transport deadline. `ProviderRequestControlPort` owns
`register`/`cancel`/`try_commit_admission`/`complete`; its
`ProviderCommitAdmissionPermitV1` binds registration generation and intent
hash, arbitrates cancel/deadline eligibility only, and is not a semantic
mutation linearization point. Durable candidate creation and the combined
terminal transaction retain that authority. `ProviderSessionOwnerV1` owns one active
`ProviderWorkMachineV1`, a FIFO of exactly 16 completely
decoded ordinary requests, one `ProviderFrameDecoderV1`, and one serialized
`ProviderFrameEncoderV1`.
`cancel` and `shutdown` are control requests: after full frame validation they
bypass the ordinary FIFO and act on the active/queued request state. The
seventeenth queued ordinary request is rejected with the fully bound
`limit_exceeded` response; a partially decoded request is never enqueued.

The normative protocol-1.0 initialization remains the immutable
`cancel:true, stats:true` capability object in detail-design Section 14.20.
Today’s `cancel:false` or platform-dependent `stats:false` implementation is a
red transition state, not a conforming negotiation. It must not emit a passing
initialize/conformance receipt. Promotion means implementing and proving both
capabilities against production owners; a direct helper, fixed clock, source
assertion, or a locally altered capability object cannot justify it. A
conforming provider never returns `unsupported_capability` for valid `cancel`
or `stats`.

No queue-depth, pending-byte, transport-timeout, work-step, or checkpoint-gap
field is added to the closed protocol-1.0 initialization record. Those values
remain host-local configuration and payload-free qualification evidence. A
wire-visible limit extension requires an explicit compatible protocol minor
and its own closed-schema vectors; this slice does not define one.

#### 13.9.1 Exact limits and accounting

- The eight-byte lowercase-hex header is not part of the payload limit.
  `00100000` plus exactly 1,048,576 canonical UTF-8 JSON bytes is admitted by
  `ProviderFrameDecoderV1`; `00100001` is rejected before payload allocation or decode.
  Total accepted wire bytes are therefore at most 1,048,584 for one frame.
- The bounded JSON owner permits at most 16 open object/array containers,
  262,144 lexical tokens, and 65,536 aggregate members (each object pair and
  each array element counts once). It checks the next increment before growing
  storage. Crossing a pre-binding parser cap closes the session with zero
  response bytes because no trustworthy correlation exists; lower
  operation-schema limits return bound `limit_exceeded` only after a complete
  canonical request is available.
  A lexical token is exactly one `{`, `}`, `[`, `]`, `:`, or `,` punctuation
  byte, one complete JSON string, one complete JSON number, or one complete
  `true`, `false`, or `null` literal. Whitespace and EOF are not tokens;
  canonical input contains no whitespace. A member is counted only after its
  complete object name/value pair or array value is recognized. Token/member
  limits are checked before accepting the token/member that would exceed them.
- Canonical encoded output is limited to 1,048,576 payload bytes; search/stats
  page output remains limited to 524,288 bytes and one explanation to 65,536
  bytes. `ProviderFrameEncoderV1` must construct and validate the complete payload before the
  first response byte. An output-limit failure returns one complete bound
  `limit_exceeded` frame and never a truncated success.
- `ProviderRequestControlPort.register` receives `first_header_at_ms`, sampled when the first header byte is
  observed, not after the header or payload completes. The client deadline is
  the closed inclusive `1..30,000` ms value and is evaluated from that time
  once decoded. A separate configured 30,000 ms
  ingress-stall bound covers an incomplete header/payload before correlation;
  a separate 30,000 ms output-stall bound covers a `ProviderFrameEncoderV1` that cannot make
  progress. Either uncorrelated ingress stall or partial-output stall closes the
  session; it must not fabricate a second error frame.
- `ProviderWorkMachineV1` checks cancellation/deadline before its first unit, after at
  most every 4,096 input bytes or equivalent bounded inner-loop quantum, before
  SHA tail/final emission, and immediately before every read-result completion
  or `try_commit_admission`. At a checkpoint where both are visible,
  cancellation wins because `ProviderRequestControlPort` tests it first.
- `ProviderFrameDecoderV1` records exact `header_bytes_read` in `0..8` and
  `payload_bytes_read` in `0..declared_length`. `ProviderFrameEncoderV1` records
  `payload_bytes_encoded`, `frame_bytes_total`, and `frame_bytes_written`.
  A write error or output stall at byte zero records
  `frame_bytes_written = 0`, abandons the prepared frame, and closes the
  session without attempting an error response. The same close-without-second-
  frame rule applies after a nonzero partial count. A success requires
  `frame_bytes_written == 8 + payload_bytes_encoded`.
- Every decoder `push` returns at most one closed event (`none`, `header`, or
  `payload`). The one `header` event follows byte eight and precedes payload
  consumption even for a coalesced read. Each `payload` event carries an
  immutable decoder-owned loan bounded by `read_chunk_bytes`, with exact
  bytes/offset/count and contiguous `frame_payload_offset`; the loan expires at
  the next decoder mutation. Concatenating the observed loans must reproduce
  the declared payload exactly once, with no gap, overlap, replay, or second
  framing cursor. A zero-length frame emits header then no payload event.
  `take_complete` returns only final length/timestamp metadata.
- Transport-local `frame_too_large` and `invalid_utf8` are payload-free local
  `TransportDiagnosticV1` classes, not `ProviderErrorV1` codes,
  not fabricated wire responses: because the decoder cannot trust a complete
  request binding, it records the payload-free class/count metrics and closes
  with zero response bytes. Bound `limit_exceeded`, `invalid_request`, and
  operation errors are legal only after one complete canonical envelope has
  established the exact correlation and authorization context. Progress
  metrics contain lengths, counts, phases, request IDs only after validation,
  and hashes where allowed; they never retain header/payload bytes, decoded
  field values, secrets, or private document content.

#### 13.9.2 Exact Wave 4 controlled-work matrix

| Matrix ID | Required oracle | REQ/NFR trace |
|---|---|---|
| `W4-SRCH-28` One-MiB byte boundary | exact-limit frame reaches canonical/schema validation; limit-plus-one is rejected before allocation/decode; header is excluded from the payload count; zero/short/uppercase/overflow headers report exact local read counts, zero semantic mutation, and silent close—never a fabricated bound error | REQ-SPKC-013–014; NFR-SPKC-011, 019–022 |
| `W4-SRCH-29` Incremental Unicode parity | scripted pipe splits at every header byte and every single split inside two-, three-, and four-byte UTF-8 scalars/combining sequences, plus deterministic mixed and randomized partition sequences, yield byte-identical decoded NFC/canonical JSON and response to the unsplit frame; negative offset, negative count, and `offset > bytes.len` reject before reading/charging bytes, producing output, or mutating UTF-8 carry, then terminally latch the exact range reason so every later update/finalize call fails with that reason; the rejected call consumes no semantic bytes; truncated EOF, overlong, surrogate, and out-of-range scalars record local `invalid_utf8`/counts and close with zero response bytes; only an executed post-fix PASS qualifies | REQ-SPKC-011, 013–014; NFR-SPKC-001, 011–012, 019–021 |
| `W4-SRCH-30` JSON structural/output caps | depth 16/token 262,144/member 65,536 and each minus-one/exact/plus-one boundary are exercised; page, explanation, canonical payload, and per-operation lower caps reject before an oversized allocation or partial response; sink output-byte plus exact new-segment-allocation charges use one `charge_all` batch, and second-category failure, duplicate aggregation overflow, zero/negative amounts, unknown category, or closed owner leaves every counter unchanged | REQ-SPKC-013–014; NFR-SPKC-011, 020–022 |
| `W4-SRCH-31` SHA block and quantum parity | state owns eight digest words, one partial 64-byte block, and one fixed reusable owner-local 64-word message schedule that remains O(1), is never passed/returned, and is not reallocated per block; no zero-copy behavior is claimed; lengths 0, 1, 55, 56, 63, 64, and 65 match the canonical SHA-256 owner at every single split; lengths 4,095, 4,096, 4,097, and 1,048,576 match at exact block/quantum/end boundaries and across multiple deterministic fixed-seed irregular partitions crossing SHA block boundaries, without requiring every possible large-input split; frozen receipt/replay/candidate/payload and domain-input preimages are streamed through their authoritative exported builders, and every partition preserves exact digest and canonical-byte parity rather than merely comparing one-shot output; negative offset, negative count, and `offset > bytes.len` reject before reading/charging bytes, producing output, or mutating buffered/compressed digest content, then terminally latch the exact range reason so every later update/finalize call fails with that reason; the rejected call consumes no semantic bytes and publishes no digest; padding across one/two final blocks is exact; injected charge failure prevents its compression, while checkpoint failure terminalizes the stream and publishes no digest without requiring rollback of already-compressed internal state; stop is observed no later than the next 4,096-byte quantum and before digest publication; only an executed post-fix full qualified 1-MiB PASS qualifies | REQ-SPKC-011, 013–014; NFR-SPKC-001, 011–012, 020–021 |
| `W4-SRCH-32` First-byte and stall deadlines | slow header, slow payload, queued wait, cooperative work, and stalled output use the first-header-byte admission time plus the separate ingress/output stall clocks; exact-minus-one proceeds and exact expiry returns/closes according to Section 13.9.1 | REQ-SPKC-013–015; NFR-SPKC-003, 011, 019–022 |
| `W4-SRCH-33` Exact cancel/deadline admission | a real cancel frame arriving through `ProviderByteStreamPort` while production work is executing wins before `try_commit_admission` as bound `cancelled` with `retryable:false`; a 1–30,000 ms deadline that expires before commit admission is `deadline_exceeded` with `retryable:true`; simultaneous visibility selects cancellation; unknown target is `cancel_target_not_found` with null receipts; cancel after the permit is `already_complete` or replays the signed result; the test separately proves the permit created no candidate/terminal/publication truth and that durable candidate creation or the combined terminal transaction is the later mutation linearization point; a synthetic clock alone cannot PASS | REQ-SPKC-013, 015; NFR-SPKC-001, 011, 020–022 |
| `W4-SRCH-34` Async FIFO control | one active operation plus exactly 16 queued ordinary requests preserves order while `ProviderSessionOwnerV1` alternates bounded work with ingress polling; the 17th queued request (18th ordinary request including the active one) is bound `limit_exceeded`; queued deadlines expire without execution; live cancel/shutdown frames bypass ordinary work, stop the target/reject new work/cancel pending work/drain commit-admitted work, and leave no live worker | REQ-SPKC-013, 015; NFR-SPKC-003, 011, 019–022 |
| `W4-SRCH-35` No partial mutation and exact linearization | stop/fault injection before parser completion, hashing, search/stats completion, candidate creation, `try_commit_admission`, and each CAS/write/rename/file-fsync/directory-fsync boundary leaves the exact valid pre-state or complete post-state root, canonical lifecycle bytes/hash, candidate/replay/publication rows, metadata, and cache state; a granted admission permit alone leaves mutation state unchanged, while a stop after durable candidate creation or the combined terminal transaction returns/replays only that complete committed result | REQ-SPKC-013–015; NFR-SPKC-001–004, 008–009, 011, 020–022 |
| `W4-SRCH-36` Framing and partial-write truth | scripted pipes cover one-byte splits, truncated header/payload, coalesced frames, UTF-8 splits, zero-progress stalls, and short writes; responses never interleave; injected writes at byte 0, every header byte, and first/middle/final payload byte distinguish zero/partial/complete emission by exact counters without a second error frame | REQ-SPKC-013–014; NFR-SPKC-001, 003, 011, 019–022 |
| `W4-SRCH-37` Platform statistics truth | every platform declared supported for provider 1.0 advertises the required `stats:true` and uses an admitted owner; `peak_rss_bytes`, `index_bytes`, scoped field statistics, document count, and a zero-cache claim are independently recomputed; a target without such an owner is an unsupported provider target/`NOT EVIDENCE`, not a conforming `stats:false`, fabricated zero, or per-request `unsupported_capability` | REQ-SPKC-013–015; NFR-SPKC-006, 011, 019–022 |
| `W4-SRCH-38` Stage 4 evidence separation | system evidence binds the exact current pure-Simple Stage 4 executable, SHA-256, source revision, provenance receipt, fixture, and checker; Rust seed, bootstrap-only, stale full CLI, source-only, missing extern, or provenance mismatch is `NOT EVIDENCE`, even when a narrow unit test is green | REQ-SPKC-013–014; NFR-SPKC-003, 020–021, 025 |
| `W4-SRCH-39` Production controlled-work closure | the import-safe proof corpus and production interfaces agree on canonical SHA/JSON bytes and stop schedules, but only production `ProviderByteStreamPort -> ProviderSessionOwnerV1 -> ProviderWorkMachineV1 -> ProviderFrameEncoderV1` execution under the admitted Stage 4 runtime can PASS; standalone fixture success with an importing-spec/compiler failure remains FAIL | REQ-SPKC-011, 013–014; NFR-SPKC-001, 011–012, 020–022, 025 |

Focused `W4-SRCH-30` canonical-decoder acceptance cases are frozen as follows:

1. A coalesced nested payload makes each `push` report an exact consumed prefix
   and at most one event; an unconsumed suffix is resubmitted. A pending event
   blocks further progress with `consumed_bytes = 0`, and moving it permits the
   next event. Concatenated consumed prefixes cover the payload once. In
   particular, a primitive immediately followed by `]` or `}` produces the
   primitive event and closing-container event from separate consumed prefixes,
   without `event_queue_full`, double emission, replay, or consuming the closer
   behind the first event.
2. Every closed kind (`start_object`, `end_object`, `start_array`, `end_array`,
   `key`, `string`, `integer`, `boolean`, `null`) has its exact half-open span.
   Empty string, integer zero, and boolean false prove nullable field validity
   cannot be inferred from sentinel values.
3. Container roots prove depth one, sixteen, and rejection before seventeen;
   primitive string/integer/boolean/null roots prove depth zero and canonical
   decoder success followed by envelope-schema rejection. Nested object/array
   fixtures prove object pairs and array elements charge once only after their
   value completes, including container-valued members.
4. The escape golden covers `\"`, `\\`, `\b`, `\t`, `\n`, `\f`, `\r`, and
   lowercase `\u00xx` for every remaining control. `\/`, uppercase hex,
   unnecessary scalar escapes, surrogate escapes, whitespace, and non-shortest
   UTF-8 reject as `noncanonical_json`/`invalid_utf8` at the proper boundary.
   `[1,]` and `{"a":1,}` reject the trailing comma, while
   `{"":1,"":2}` rejects the duplicate empty key; an empty prior key may
   not be mistaken for an uninitialized key-order sentinel.
5. Pinned UCD-17 NFC vectors cover composed/decomposed and combining-boundary
   splits. Non-NFC strings reject; normalized-equal keys are duplicates; key
   order uses unsigned UTF-8 bytes, including bytes at/above `0x80`, independent
   of host collation.
6. A scripted split matrix proves exactly one raw cursor and one SHA owner:
   each accepted prefix changes both once, pending-event calls change neither,
   and final `payload_sha256` equals the exact raw canonical bytes. The result
   has only `payload_sha256`, `raw_bytes`, `token_count`,
   `aggregate_members`, and `maximum_depth` with exact values.
7. Incomplete input, limit/range/checkpoint/SHA failure, and successful finish
   each terminalize the decoder. Every later `push`, `next_event`, or `finish`
   returns the original latched failure or `decoder_complete`, consumes zero,
   emits nothing, and never publishes a second digest.

Canonical JSON implementation and these focused cases are **in progress**;
none is marked PASS by this design update. Existing request-control and UTF-8
PASS evidence and the qualified SHA `W4-SRCH-31` FAIL/status below are unchanged.

Focused canonical-emitter cases under `W4-SRCH-30` are also frozen and remain
**in progress**:

1. Every operation schema builder produces the exact flat immutable instruction
   tape and rejects a non-NFC, duplicate, or out-of-order UTF-8 key, an unsafe
   integer, and an over-limit plan before the emitter or sink advances.
2. Exact-minus-one, exact, and plus-one boundaries cover the 262,144 plan
   instructions, 256 instructions per step, 4,096 output bytes per step,
   segment size, and `maximum_output_bytes`; they prove bounded staging and
   rejection before oversized allocation or partial publication.
3. One-byte, boundary-crossing, and irregular chunk schedules yield identical
   canonical bytes and digest. Instrumentation proves each successful chunk is
   appended and hashed from the exact same slice, followed by one checkpoint,
   with one authoritative plan cursor and no replay or gap.
4. Adversarial plan construction cannot introduce a map, `any`, raw JSON
   fragment, recursive value, caller punctuation, join buffer, or second
   cursor. Strings cover every canonical escape and multi-byte NFC boundary.
5. Inject sink, SHA, budget, and checkpoint failure before byte zero and at
   first/middle/final chunks. The first reason remains latched; subsequent
   step/take/digest calls make no progress and return that reason. Partial sink
   and hash state is unpublishable/discarded, with no retry, rollback, second
   error response, or zero-copy claim.
6. Only `ready` permits exactly one take of completed segments and digest;
   `continue`, `failed`, and subsequent completed calls cannot publish either.

No emitter source or focused test is accepted by this documentation update.
Decoder and SHA execution records below remain authoritative and unchanged.

#### 13.9.3 Planned artifacts and scenario allocation

Current acceptance status: the work-control prerequisite is accepted and
pushed; request-control has a fresh focused PASS 9/9; and `W4-SRCH-29` UTF-8
has a fresh focused PASS 7/7. SHA source static review is complete, but the
earlier pre-fix `W4-SRCH-31` execution was 4/5 and the latest full post-fix
cycle 2 was terminated at approximately 3:09 with zero output. The accepted
workspace optimization has 4,097-byte full-versus-bounded parity and a bounded
cycle-3 guard-probe PASS at 1.26 s/43,852 KiB, but the full qualified 1-MiB
oracle has not passed. Its current status is `FAIL`. Wave 4S-C remains open:
focused component evidence cannot substitute
for a post-fix PASS of every remaining oracle or for the integrated production
pipeline.

The frozen unit/evidence targets are:

- `test/fixtures/spipe_controlled_work/controlled_work_proof.spl` — diagnostic
  parity oracle only, never a production acceptance implementation;
- `test/01_unit/app/spipe_knowledge_provider/provider_controlled_work_import_smoke_spec.spl`
  — standalone-versus-imported compiler/runtime admission and SHA/JSON boundary
  vectors;
- `test/01_unit/app/spipe_knowledge_provider/provider_deadline_control_spec.spl`
  — cooperative work, exact stop precedence, before/after-commit-admission
  state, and distinct later durable mutation linearization;
- `test/01_unit/app/spipe_knowledge_provider/provider_streaming_limits_spec.spl`
  — planned `ProviderFrameDecoderV1`/JSON/Unicode/header/payload boundary table,
  including exactly-once header event, contiguous bounded payload loans, loan
  lifetime, metadata-only completion, and no duplicate framing cursor;
- `test/01_unit/app/spipe_knowledge_provider/provider_session_owner_spec.spl`
  — planned active/FIFO/control/partial-write/stall fault schedules;
- `test/01_unit/app/spipe_knowledge_provider/provider_stats_count_explain_spec.spl`
  — scoped statistics and platform capability truth;
- `test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl`
  and its mirrored manual — the sole system owner of W4 acceptance.
- `doc/07_guide/app/spipe/spipe_knowledge_compiler.md` — operator-facing
  framing, timeout, cancel/shutdown, platform-capability, evidence-admission,
  and recovery guidance updated only after the executable contract is current.

The system spec retains the shared `check_spipe_provider_parity` helper and adds
these visible titles only after the production targets exist:

1. `should preserve one logical frame across bounded Unicode transport chunks`;
2. `should stop active and queued work at exact cancellation and deadline boundaries without partial mutation`;
3. `should report truthful platform statistics and complete response-write counts`;
4. `should reject stale bootstrap evidence and admit only the current Stage 4 provider`.

Boundary rows remain folded detail. Protocol transition and byte/write counters
are retained as `protocol` evidence; stop schedules and state digests as
`artifact`; process/RSS/provenance as `log` plus `artifact`. The generated
manual must state that an accepted logical result is never a partial stream.
The operator guide and generated manual are both independently reviewed; a
current source test with either stale document is not design/verification
completion.

The conformance producer emits W4 cells 28–39 only after both the standalone
proof and importing production-target checks run under the same admitted
runtime. The exact commands are frozen in Section 10 and use the absolute
admitted Stage 4 executable from detail-design Section 14.6.2;
substitution of `src/compiler_rust/target/bootstrap/simple`, a stale `bin/simple`,
or any binary without the matching provenance receipt is rejected before test
execution. The higher-capability final reviewer must inspect the retained raw
chunk/control/fault schedules and recompute the evidence hashes; a sidecar or
source scan cannot mark any of these cells passed.

#### 13.9.4 Active `W4-SRCH-31` performance failure

Fresh interpreter verification cycle 2 exceeded the 180-second focused-test
ceiling and was terminated at approximately 3:09 with no output. The accepted
fixed reusable owner-local 64-word schedule preserves O(1) state without
per-block schedule reallocation; it is neither passed/returned nor evidence of
zero-copy processing. It has 4,097-byte full-versus-bounded parity, and the
bounded cycle-3 guard probe passed in 1.26 s at 43,852 KiB. Status remains
`FAIL`: static review, the earlier 4/5 result, smaller helper vectors, and this
bounded probe do not admit the full qualified 1-MiB row. Three cycles are
consumed and no further run is authorized in this session. Reproduction and acceptance criteria:
`doc/08_tracking/bug/spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25.md`.

The second qualified-ceiling attempt, made once after the bounded
optimization, executed the contract-complete nine-scenario matrix and exited
`124` at exactly 180 seconds without a summary. The resolved executable was
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
reported `Simple Language v1.0.0-RC`, and had SHA-256
`3ef64bffc68d0b1c2dd851d1f02976ca98fba6f88fbb406dddf56ba7f3ca27c0`;
the wrapper warning identifies Rust-built bootstrap-seed provenance, so this
is not admitted Stage 4 evidence. `/usr/bin/time` was killed and provides no
RSS measurement. This exact-ceiling failure is separate from the earlier
approximately 3:09 uncontrolled termination.

The complete matrix has passed static highest-capability review, but no
candidate matrix files are accepted and the executed full `W4-SRCH-31` gate
remains `FAIL`. Before another qualified execution, capture bounded,
payload-free stage progress receipts or use a provenance-qualified pure-Simple
Stage 4 executable. The nine-scenario matrix, 1-MiB workload, and 180-second
ceiling remain unchanged; no ten-scenario, Stage 4, or RSS claim is permitted.

#### 13.9.5 Active canonical-JSON decoder execution record

Fresh focused cycles produced `2/5`, `1/8`, and `7/8`. The final executed
failure is test syntax in the nested-value assertion (`.unwrap().bytes()`), so
no file is accepted and canonical-JSON status remains `IN PROGRESS`. The
candidate also depends on an unaccepted `streaming_sha256` `Result`-wrapper
fix.

Acceptance still requires observable proof that invalid slice/budget/canonical
input fails before SHA accounting or raw-cursor advancement, and that failure
of any category in the atomic reservation leaves stack, root, and event state
unchanged. In the next fresh session, rewrite only the nested assertion through
an import-safe local binding and execute the unchanged eight-case focused spec
once. A complete PASS must then receive highest-capability call-graph review;
the JSON files and the SHA wrapper dependency are accepted separately or not
at all. No partial count or source inspection closes this row.

#### 13.9.6 Active canonical-response-emitter execution record

Emitter status is `IN PROGRESS`. Cycle 1 ended at a parser failure; the syntax
was fixed afterward without a behavioral result. Cycle 2 executed `5/5` on the
pre-ownership draft, but highest-capability review found a structural ownership
failure. That result is not accepted evidence, and no cycle-2 source/spec is
accepted.

The redesigned candidate owns sink, SHA, budget, and checkpoint, rejects
forged plans and an incorrect predicted output size before emission, finalizes
before `ready`, and permits exactly one bytes/digest take only from `ready`.
Cycle 3 executed `0/5` because the focused spec used a nested `.bytes()` form
unsupported by the compiler. The expression was mechanically split into a
local after the run but remains unexecuted. No emitter source/spec is accepted.

One fresh-session execution of the unchanged five-case matrix is the next
allowed evidence step. Only a complete PASS proceeds to highest-capability
call-graph review of the actual ownership, validation, append/hash/checkpoint,
terminal failure, finalization, and publication paths. The canonical decoder's
separate executed result remains `7/8`; the SHA gate remains `W4-SRCH-31 FAIL`.

#### 13.9.7 Current decoder/emitter evidence update

The decoder's final permitted cycle 3 subsequently executed `PASS 8/8`, but
highest-capability review returned `FAIL`. Its added `transport_bytes` counter
creates a parallel cursor: incomplete C2 input reports consumed/transport
advance while raw/SHA progress lags, contradicting the exact consumed-prefix
hash oracle. Value-semantic rollback improved, but source/spec remains
unaccepted.

Fresh emitter cycles executed `2/5`, `2/5`, and `4/5`. The post-cap second-take
fix remains unexecuted. Highest-capability review returned `FAIL` because exact
predicted-output-size validation is absent, scratch cursor mutation precedes
sink/SHA/checkpoint acceptance, and the oracle omits first/middle/final and
cap-boundary fault injection. No decoder/emitter source/spec is accepted.
Overall status remains `IN PROGRESS`; `W4-SRCH-31` remains `FAIL`.

#### 13.9.8 V2 decoder/emitter closure record

Decoder v2 executed `PASS 8/8` in all three permitted cycles. Central
single-cursor and trial-transition structure is sound, but final high review is
`FAIL`: escape vectors compare only lengths, token/member boundaries seed
counters instead of exercising cumulative transitions, every failure class is
not checked for stable `push`/`next_event`/`finish` terminal results, and the
runtime is bootstrap-seed. No source/spec is accepted.

Emitter v2 executed `1/8`, `8/8`, and `11/11`. Trial cursor/child-copy,
exact-size/cap/fault behavior, and the member-close defect are repaired. Final
high review remains `FAIL`: no fixed global output cap guarantees
`<= 1,048,576`; payload/page/explanation maxima are caller-controlled rather
than protocol-fixed at 1,048,576/524,288/65,536; exported generic/raw
constructors bypass typed-only schema builders; and execution is bootstrap-
seed. No source/spec is accepted. Overall status remains `IN PROGRESS` and
`W4-SRCH-31` remains `FAIL`.

#### 13.9.9 Checked-BM25 and rejected DBFS evidence record

Commit `2b9f25f8604` accepts only
`src/lib/common/search/ranking.spl` and
`test/01_unit/lib/common/search/ranking_spec.spl`. Highest-capability review is
`PASS`. In a clean integration checkout the source check passed and the focused
specification passed `30/30`; both receipts have bootstrap-seed/non-Stage-4
runtime provenance. They are sufficient for the owned Lane C scorer slice but
are not Stage 4 runtime qualification.

The accompanying DBFS bundle is `FAIL` and `NOT-EVIDENCE`: the standalone
`wave4_compatibility` implementation is a second fixture scorer rather than a
facade over the accepted scorer; probe cells do not establish the contract;
the reported clean/parity run was not executed and the claim is false;
embeddings zero-use is unproved; and capability/statistics behavior is wrong.
No DBFS source or test is accepted.

The replacement DBFS evidence must exercise the real canonical-scorer facade,
idempotent remove/re-add corpus statistics, deduplicated query terms, an honest
`explain:false` capability until explanations exist, and equality against an
independently rebuilt final corpus. The clean post-push lint invocation failed
before any lint verdict because runtime/codegen dispatch could not resolve
`Array.sort_by`; its bootstrap-seed provenance makes this a tooling blocker,
not a scorer failure or pass. Duplicate check was not run. Wave 4 remains
`IN PROGRESS`.

#### 13.9.10 DBFS facade zero-execution closure

The exact clean-clone candidate set was:

- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/__init__.spl`;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/bm25.spl`;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/inverted_index.spl`;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/search.spl`;
- `test/02_integration/storage/dbfs/fts_canonical_facade_spec.spl`.

Cycles 1, 2, and 3 each executed zero owned-code assertions. Stage 3 Simple
`9ce412a1d102de421de6d7042d8dc5c65201cc514b463b9b6a5bc5de2f66970c`
has no `check`/`test` command. Rust seed
`c9c783b8568cf9a199945fe1ee98d08615b728387e6c89cbdc9b50e600f3e091`
instead failed on unrelated `nogc_async_mut/path.spl` `E1002 unsafe` and
`plan_sdn.spl` `Dedent`. These are not DBFS pass receipts.

Static highest-capability review is `FAIL` with admissible set `[]`:
value-semantic nested collection/struct writeback is incomplete; there is no
single atomic lexical+trigram+content commit; `contains_document` violates the
frozen `me fn` ABI; and the spec does not cover intermediate
statistics/averages, complete independent clean statistics, contains/absent,
exact ordering, legacy success, or checked-upsert failure/no-change.

The facade/canonical-scorer direction and focused fixture are retained only as
unaccepted positive design input. The next evidence must come from rebuilt
child copies with one owner writeback, an atomic engine transaction, corrected
ABI, the complete oracle, and a fresh bounded run on a capable pure-Simple
runtime. Wave 4 remains `IN PROGRESS`.

#### 13.9.11 Analyzer V1 contract freeze and failed candidate

The exact batch test seam is:

- `SearchFieldIdentityV1`: `Identifier,Title,Heading,Classification,Body`;
- `AnalyzerErrorV1`: `InvalidLimits,InvalidFieldIdentity,InputLimitExceeded,
  InvalidUtf8,NormalizedLimitExceeded,TokenBytesLimitExceeded,
  TokenCountLimitExceeded,DistinctTermLimitExceeded`;
- `AnalyzerIdentityV1`: eleven text fields
  `analyzer_id,unicode_version,unicode_manifest_sha256,normalization_id,
  lowercase_id,tokenizer_id,stop_words_id,stop_words_sha256,stemming_id,
  field_schema_id,limits_schema_id`;
- `AnalyzerLimitsV1`: five i64 fields
  `max_input_bytes,max_normalized_bytes,max_token_bytes,max_tokens,
  max_distinct_terms`;
- `AnalyzedTokenV1(value:text,position:i64,exact_identifier:bool)`;
- `AnalyzedTextV1(normalized:text,tokens:[AnalyzedTokenV1])`;
- `AnalyzedQueryTermV1(value:text,qtf:i64)`;
- `AnalyzedQueryV1(normalized:text,terms:[AnalyzedQueryTermV1])`;
- `analyze_field_v1(text,SearchFieldIdentityV1,AnalyzerIdentityV1,
  AnalyzerLimitsV1)->Result<AnalyzedTextV1,AnalyzerErrorV1>`;
- `analyze_query_v1(text,AnalyzerIdentityV1,AnalyzerLimitsV1)
  ->Result<AnalyzedQueryV1,AnalyzerErrorV1>`;
- `unsigned_utf8_less(text,text)->bool`.

The oracle must prove UCD17 NFC -> default lowercase (never fold) -> NFC;
maximal `Alphabetic|Decimal_Number|Mark|_` tokens; one-based positions before
stopword removal; exact `[a,an,and,of,the,to]` stopwords with digest
`6f0a7c26d3d0e3d06a2fbbbeaa1843294f83c3be26baf1c04651191e011510bf`;
identifier full-normalized/no-trim exact token appended last at position zero
and deduplicated; and QTF terms in unsigned UTF-8 order.

Query limits are `4096,4096,4096,128,128` in struct order. Field input is at
most 1,048,576 bytes and configured `max_tokens <= 524288`. Cache identity
changes for Unicode manifest, stopwords, any limit, or either schema. Tests
must prove zero embedding/process/network/locale use.

This layer sits beneath the unchanged `ProviderAnalyzerLimitsV1`,
`ProviderAnalyzedTokenV1`, `ProviderAnalyzedTokenSinkPort`, and
`ProviderStreamingAnalyzerV1`; adapter parity is mandatory. The analyzer lane
owns only `src/lib/common/search/analyzer.spl` and
`test/01_unit/lib/common/search/analyzer_contract_spec.spl`; `__init__.spl`
is merge-owned. UCD17 tables/manifest are absent on `main` and prerequisite.
The existing candidate is unbounded and parity-false: static review `FAIL`,
admissible `[]`. Wave 4 remains `IN PROGRESS`.

#### 13.9.12 Unicode 17 prerequisite evidence closure

The atomic fixture contains exactly 14 files: the Unicode generator and
license; seven UCD 17.0.0 sources (`UnicodeData`,
`DerivedCoreProperties`, `PropList`, `SpecialCasing`, `CaseFolding`,
`CompositionExclusions`, `NormalizationTest`); generated JavaScript and
Simple tables; the Unicode manifest; the JavaScript unit test; and
`test/01_unit/lib/common/search/unicode_17_0_0_spec.spl`. Their roots are
`examples/05_stdlib/spipe/tools/unicode/`,
`examples/05_stdlib/spipe/src/search/generated/`,
`src/lib/common/search/generated/`,
`examples/05_stdlib/spipe/test/fixture/wave4_search/`, and
`examples/05_stdlib/spipe/test/unit/`. Partial acceptance is forbidden.

Algorithm work now uses stable 256-code-point CCC buckets with bounded-linear
behavior, O(n) sigma contexts, and 4,096-element bounded JavaScript chunks.
The JavaScript oracle passed 7/7 over 20,034 normalization records in all five
forms, every scalar, and 1 MiB.

Bundle status is nevertheless `FAIL`, admissible `[]`. Cycle 2's Rust-seed
Simple run timed out `124` with no summary. Cycle 3 only repeated the green
JavaScript check and is not additional evidence; it also violates the process
plan. Static review still lacks proof for Simple push/value semantics and the
optimizer bound, finds direct `rt_file_read_text` use in the spec, an orphan
`REQ-SPK-SEARCH-UNICODE-001`, a wrong generated-JavaScript license path, and
an insufficient independent lowercase matrix for `Case_Ignorable`
final-sigma contexts.

The next run is permitted only after those static defects are repaired, and it
must execute full parity once on a capable pure-Simple runtime. No code is
accepted; the analyzer prerequisite remains missing and Wave 4 remains
`IN PROGRESS`.

## 14. Current evidence status (2026-08-26)

The five system specifications and their Markdown manuals are executable-design
scaffolds, not passing evidence. Four fail closed with `DESIGN-SCAFFOLD`; the
provider-parity spec fails closed with `NOT-EVIDENCE`. Requirements `REQ-SPKC-001` through
`REQ-SPKC-030` and NFRs `NFR-SPKC-001` through `NFR-SPKC-025` remain active;
header ranges and family allocation rows are planning aids and do not replace a
named scenario plus oracle and retained receipt for each ID. Do not mark AC-13,
NFR-SPKC-020, or final verification complete until the real oracles replace the
scaffolds and the manuals are regenerated from the executed specs.

Accepted implementation evidence currently covers Waves 1–3 and the checked
common BM25 scorer only. DBFS parity, RRF, the JavaScript fallback/provider,
Unicode analyzer parity, canonical JSON, and the native identity candidate are
`FAIL`, `BLOCKED`, or `NOT-EVIDENCE`. Later wave tests must not use those
candidates as prerequisites until an accepted commit and focused receipt are
recorded in the execution ledger.

## 21. Wave 5a snapshot-authority admission matrix (2026-08-26)

Wave 5 URI/resource/materializer scenarios are **not executable acceptance
evidence** until the following Wave 5a prerequisite has a production oracle.
The tested surface is `SnapshotAuthorityPortV1` plus `ProjectionPortV1`; a
raw `ImmutableSnapshotStore` or a duck-typed substitute cannot satisfy it.

| ID | Setup/action | Required oracle |
|---|---|---|
| W5A-01 | Open one exact workspace/project/worktree/snapshot/revision tuple | Opaque authority view has the matching binding and verified manifest digest |
| W5A-02 | Resolve artifact and section IDs in that view | Each exists in exactly one matching manifest inventory entry before rendering |
| W5A-03 | Use absent UID or a valid UID with the wrong kind | Bounded denial and zero ProjectionPort render/list calls |
| W5A-04 | Reuse snapshot UID across a foreign workspace/worktree | Bounded denial before inventory access |
| W5A-05 | Use stale revision, changed manifest digest, or unavailable snapshot | Bounded denial before inventory access |
| W5A-06 | Pass structural/duck-typed authority or projection objects | Constructor/invocation rejects; no fallback is accepted |
| W5A-07 | Resolve `spipe://skill` or another legacy alias | Alias yields only a canonical candidate; the sealed authority proves that target, then fresh authorization is verified, before any ProjectionPort call |
| W5A-08 | Generate inventory by clean rebuild and equivalent incremental update | Manifest inventory and rendered projection bytes are identical |
| W5A-09 | List a bounded virtual directory | Every child is inventory-proved; deterministic order, cursor, and receipt bindings hold |
| W5A-10 | Exercise malformed/hidden/foreign/mismatch paths | Same bounded public class, no canonical path or inventory disclosure |
| W5A-11 | Build aggregate from clean rebuild and equivalent incremental update | Byte-identical ordered `contributingProjectRoots`, inventory root, authority tuple, and projection bytes |
| W5A-12 | Remove one otherwise valid aggregate contributor | Denial before target lookup or ProjectionPort call |
| W5A-13 | Add an otherwise valid extra contributor or substitute one contributor root | Denial before target lookup or ProjectionPort call |
| W5A-14 | Present the same contributor records in non-canonical order | Denial before target lookup or ProjectionPort call |
| W5A-15 | Create `ExpectedReadBindingV1` only from a proven authority view, canonical target/directory, and normalized request; independently mismatch authority instance or manifest digest | Construction/verification denies structural or mismatched input before `AuthorizationPortV1` or ProjectionPort call; the closed tuple preserves both authority claims |

The eventual MCP system spec uses `step("Browse virtual knowledge views")` and
`check_spipe_virtual_view_safety`; its fail-fast helper remains fail-fast until
these fourteen cases observe real ports. A Wave 5 URI candidate that proves only
syntax, receipt signatures, or mocked membership is `NOT-EVIDENCE`.

### 21.2 Seal and alias additions (repair cycle 2)

W5A additionally injects swapped/tampered inventory bytes, authority-manifest
root mismatch, and a deliberately cyclic base-snapshot/inventory construction;
each rejects before target lookup. It proves alias absence, ambiguity,
foreign-authority alias reuse, and alias-index root tampering. A positive alias
must use `SnapshotAuthorityPortV1.resolveCanonicalAlias` in the sealed view;
external registry/path alias lookup is `NOT-EVIDENCE`.

### 21.1 Required additions to W5A evidence

W5A-01 through W5A-10 additionally require: (a) swapped/tampered inventory
bytes and sealed-manifest/root mismatch reject before target lookup; (b)
project UID mismatch is independently rejected; (c) positive manifest-proved
workspace-root, trace, diagnostics, and directory aggregate cases use the
defined null-project `workspace_aggregate` scope; (d) project scope rejects
null project while aggregate scope rejects a supplied project; (e) two genuine
branded authority instances/views/targets cannot be cross-mixed; and (f) each
`ExpectedReadBindingV1` field, including `authorityInstanceUid` and
`authorityManifestDigest`, is mutated independently. The worktree negative
uses a valid receipt whose snapshot tuple belongs to another worktree, proving
the receipt's intentionally absent worktree field is enforced transitively
rather than silently ignored; genuine branded cross-instance and
manifest-digest mismatch negatives prove the two authority claims are equally
closed rather than adapter-supplied.

### 21.3 Aggregate-manifest exactness

For each positive workspace-aggregate root/view/trace/diagnostics case, W5A
builds a `contributingProjectRoots` manifest with canonical records
`{projectUid, baseSnapshotUid, authoritySnapshotUid, targetInventoryRoot}` and
requires exact canonical ordering. It then independently attempts a missing
contributor, an extra contributor, a substituted root for an existing project,
and a reordered equivalent list. Every variation must deny before target
lookup or ProjectionPort calls; only byte-identical canonical manifest and
authority tuple can be admitted. The same fixture verifies that a project
scope containing this field, and an aggregate scope omitting it, reject.

## 22. CursorReceiptV1 authority admission matrix (2026-08-26)

Wave 5 URI v3 is **NOT-EVIDENCE** until a real branded extension of the
existing AuthorizationPortV1 passes all cases below. Trust/Edge-only behavior,
a local signer, a mock verifier, or an in-memory receipt map cannot PASS.

| ID | Setup/action | Required oracle |
|---|---|---|
| W5C-01 | Verify an authorized read after sealed authority proof, then issue a cursor | `ExpectedReadBindingV1` and opaque read grant contain exactly the sealed `baseSnapshotUid`, `authoritySnapshotUid`, `worktreeUid`, `authorityInstanceUid`, and `authorityManifestDigest` claims; cursor signs all five and every other closed field |
| W5C-02 | Mutate `authorityKeyId`, `authorityKeyEpoch`, `baseSnapshotUid`, `authoritySnapshotUid`, `authorityInstanceUid`, `authorityManifestDigest`, workspace, project, worktree, revision, target, view, path, selector, scope, order, limit, position, policy, issuer, epoch, or time field independently | Denial before ProjectionPort; same public bounded class |
| W5C-03 | Substitute Trust, Edge, canonical-read, wrong algorithm, unknown issuer/key, forged receipt, or structural verifier/grant | Domain/brand/allowlist/signature denial; no fallback or disclosure |
| W5C-04 | Use exact-before, exact-at, and exact-after expiry/revocation; request expiry beyond read grant or TTL | Only `issued <= now < expires` and current durable epoch pass; issue rejects overshoot |
| W5C-05 | Restart with durable policy and KeyProvider, then verify/issue valid, expired, revoked, and foreign-policy cursors | Pre/post restart parity; no in-memory state; missing active private handle fails closed |
| W5C-06 | Submit a rotation then apply due transitions before activation, at activation, during grace, and at prior-key revocation | Unique pending/current/grace/revoked transitions and only one durable revocation-epoch advance; old verification only in grace |
| W5C-07 | Replay same rotation UID with identical bytes, then with changed bytes or stale policy version | Idempotent same-result replay; changed/stale input fails without duplicate durable record |
| W5C-08 | Continue a positive multipage directory through restart and key grace | Stable ordering with no gap/duplicate; inbound cursor verifies against the same read grant and outbound receipt follows list |
| W5C-09 | Recompute cursor identity preimage, UID, signing payload, and signature bytes from production fixture | UID excludes UID/signature; signing includes derived UID and excludes signature; canonical bytes are exact |
| W5C-10 | Force outbound cursor issuance failure after a successful list | Page is discarded, no content leaks, and public response remains `not_found_or_unauthorized` |

The execution ledger records the durable policy fixture and independent review
receipt. Private telemetry may retain a closed reason such as `stale_cursor`,
but no test accepts a public distinction between absent, hidden, unauthorized,
or stale targets.

### 22.1 Production authority/store evidence required before W5A/W5C admission

| ID | Setup/action | Required oracle |
|---|---|---|
| W5A-16 | Supply `WT-*`, path-derived, or malformed worktree UID | Reject before registry/store access; only `W-<opaque-base32>` is accepted |
| W5A-17 | Change registry or snapshot revision between open and final revalidation | Bounded denial; no view, grant, or ProjectionPort call |
| W5A-18 | Publish project and aggregate through production publisher; supply string/structural permit or caller-selected aggregate | Reader sees either no manifest or fully recomputable roots; aggregate has all and only selected complete contributors; only the non-forgeable publisher permit succeeds |
| W5A-19 | Clean rebuild versus equivalent incremental commit for artifact, section, directory, aggregate | Byte-identical roots, pages, and projection bytes |
| W5A-20 | Request limits 0, 101, 1, and 100 | Invalid denies; valid page <=100 entries, <=200 lines, <=6,000 `spipe-markdown-token-v1@1` tokens, authenticated continuation |
| W5C-11 | Crash at initial policy-directory create and at write/fsync/rename/CAS of each policy, key, issuer, rotation, and revocation record | Restart sees prior complete state or one complete monotonic state, never partial/ambiguous; no acknowledgement precedes durable state |
| W5C-12 | Replay same operation UID for every record class; alter bytes; use stale policy version | Equal replay idempotent; altered/stale denies without second durable transition |

Fake registry/store, raw fixture manifest, mock projection, or a rejected
sealed-read implementation is `NOT-EVIDENCE`.

### 22.2 Sealed-publication and durable-policy production oracles

| ID | Setup/action | Required oracle |
|---|---|---|
| W5A-21 | Substitute manifest/inventory bytes, or bind a copied/stale registry record after exact open | Canonical roots and live registry/snapshot revalidation deny before target lookup or ProjectionPort |
| W5A-22 | Forge/serialize publisher permit; omit/add/reorder/substitute an aggregate contributor; provide incomplete root schema | Only commit-root brand publishes; reader admits all-and-only registry-complete ordered schema-valid roots |
| W5A-23 | Duplicate/unlisted directory child, reorder page, widen limit, change continuation domain/position, or use foreign/malformed token | Bounded denial or sealed deterministic page; no leak, gap, duplicate, or unbounded output |
| W5A-24 | Make both `issueCursorReceiptV1` and `verifyCursorReceiptV1` independently recompute `continuationDomain` only after AuthorityManifest/TargetInventoryManifest verification; exercise `spipe-markdown-token-v1@1` (Unicode 15.1 separator table) at exact 6,000/6,001 boundaries; mutate signed manifest/target/order/limit inputs | Only canonical derived domain and <=6,000 deterministic tokens pass; no manifest entry/root/digest contains the domain, no new grant/cursor field exists, and mutated existing binding denies before list/render |
| W5C-13 | Race processes at each policy operation with same/different UID and expected version | One monotonic durable transition; equal replay same result; altered/stale input creates no record |
| W5C-14 | Crash at temp creation, write, file fsync, rename, parent fsync, or recovery with malformed record | Restart observes old complete state or one schema-valid contiguous prefix; acknowledgement never precedes durability |

These are prerequisites for W5C-01..10 and all URI/MCP/materializer tests.

### 22.3 Commit-path publication prerequisite

The current stores do not supply the production KnowledgeCompiler transaction
needed for W5A-18/W5A-19. The following production-oracle cases target
`KnowledgeCompilerCommitPublisherV1`; fixture maps, raw manifests, and a
standalone authority primitive are `NOT-EVIDENCE`.

| ID | Setup/action | Required oracle |
|---|---|---|
| W5A-25 | Commit from exact prior base/publication tuple, then supply caller permit/root/aggregate | Only closure permit publishes; adapters cannot choose contributors or infer prior state |
| W5A-26 | Commit artifacts, sections, directories; compare clean and incremental | Base/authority snapshots, roots, pages, and projections are byte-identical |
| W5A-27 | Missing/extra/reordered/substituted/incomplete aggregate contributor | Denial before publication; no partial project/aggregate visibility |
| W5A-28 | Fault stage/write/**AuthorityPublicationJournalV1 publication-journal atomic rename**/file-fsync/parent-fsync/current-pointer-CAS/ack/restart; concurrently read at every boundary | AuthorityPublicationJournalV1 validates one AuthorityPublicationRecordV1; recovery and concurrent reader see only old complete or new complete dual-scope state, never staged/partial state |
| W5A-29 | Equal commit-ID/exact tuple/input then altered input, stale revision, or changed expected base/publication UID | Equal replay idempotent; altered/stale denies without publication |
| W5A-30 | Substitute manifest/inventory/snapshot/revision/section/target/directory root | Revalidation denies before lookup or ProjectionPort |
| W5A-31 | Supply public journal, `instanceof` lookalike, structural permit, serialized permit, or caller aggregate/root | Only TargetInventoryStoreV1's composition-root closure brand publishes; no write or visible record otherwise |
| W5A-32 | Replay same commit ID with altered expected IDs or normalized deltas | Exact canonical replay-envelope SHA-256 returns the original durable result; altered envelope denies before write |
| W5A-33 | Corrupt current record, inventory/manifest object, object hash, project/aggregate root, page root, or exact tuple after publication | Open/recovery deep validation denies before lookup; it never returns a partially checked head |
| W5A-34 | Kill publisher process or leave writer lock at each journal state/rename/fsync/CAS boundary; start independent recovery process | Recovery resolves stale lock and exposes prior complete or next complete record only, never null/staged/partial |
| W5A-35 | Compare a clean commit and equivalent delta sequence, then list bounded directory pages with forged/foreign continuations | Byte-identical dual snapshots/inventories/manifests/roots/pages/projections; only sealed ordered <=100-entry/<=200-line/<=6,000-token pages continue |

W5A-25..30 run against real composition-root registry, snapshot, inventory,
journal, and filesystem owners. They gate W5A-18..24, W5C, URI, MCP, and
materializer re-attempts.
W5A-31..35 are additional non-admission gates for the rejected publisher
implementation; focused or in-memory substitutes do not satisfy them.

### 22.4 Ordered remediation gates (blocking test execution)

| Gate | Must pass before next gate | Mandatory added/retained proof | Explicit non-evidence |
|---|---|---|---|
| P2 durable publisher | W5A-25..35 foundation | Same canonical envelope replays; changed revision/expected IDs/deltas deny; independently launched writer race and SIGKILL/recovery prove old-or-new complete state. First-use nested ledger ancestors are all durable; stale unlock revalidates exact observed owner/lock identity before removal. | In-process-only lock/race, timer-only stale detection, path-blind unlink, public permit/journal, or focused unit success. The known `EEXIST` first-use race is a FAIL. |
| A read authority | P2 PASS | Real `SnapshotAuthorityPortV1.openBoundSnapshot` opens production registry/snapshot state through branded `TargetInventoryStoreV1.openPublishedAuthorityInventoryV1` and rejects every dual-snapshot, manifest, instance, worktree, revision, target, and brand substitution before AuthorizationPort/ProjectionPort. | Fixture manifests, caches, maps, structural views, mocked stores, or public journal access. |
| U URI/projection | A PASS | Resolver candidate undergoes sealed target proof plus real receipt signature/window/revocation and full receipt/binding comparison; URI hostile matrix and canonical-positive families prove zero pre-admission projection calls and one public denial. | Raw paths, local signers, duck-typed grants, alias-only output, or old rejected URI code. |
| C cursor/adapters | U PASS | W5C plus bounded-page/cache/materialization cases prove authenticated domain/position/limit and read-only adapters. | Mock ProjectionPort, synthetic cursor state, or adapter-only fixture. |

Every gate additionally requires an exact-scope diff inspection and independent
highest-capability review PASS. Any failure marks the gate and all successors
`NON-ADMITTED`; no successor test may be counted as substitute evidence.
The gates are additive to the normative authority/cursor and raw-snapshot
contracts, including exact `spipe-markdown-token-v1@1` <=6,000 testing;
rejected cursor code cannot remove or relax any of those cases.
