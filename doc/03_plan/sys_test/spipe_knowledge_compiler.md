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
- explicit/generated accepted trace edges satisfy strict profiles while
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

- **Given** a schema-v1 snapshot containing workspace and worktree `W-` records
- **When** schema v2 is published
- **Then** record type selects deterministic `WS-`/`WT-` identities, migration records are emitted, and v1 bytes remain unchanged.

### Scenario: Edge authority fails closed

- **Given** forged, revoked, expired, wrong-policy, and wrong-edge receipts
- **When** strict trace is evaluated
- **Then** none satisfies an obligation and each produces a stable diagnostic.

### Scenario: Delta replay distinguishes identity and conflict

- **Given** one published graph delta
- **When** the identical delta and a different same-base delta are replayed
- **Then** only the first returns `already_applied`; the second is stale.

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
