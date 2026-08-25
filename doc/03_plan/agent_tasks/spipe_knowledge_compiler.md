<!-- codex-design -->
# SPipe Knowledge Compiler — Agent Task and Integration Plan

**Date:** 2026-08-25  
**Status:** Implementation handoff  
**Source:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`  
**Merge owner:** `/root`  
**Final reviewer:** best available normal/highest-capability model, independent of implementation lanes

## 1. Delivery contract

Implement dependency Waves 0–10 in order. A later wave may be explored in parallel, but it may not merge until every predecessor exit gate is evidenced. Wave 11 (FUSE/ProjFS) is explicitly deferred and is not required for feature completion.

The merge owner alone edits shared schemas, `.spipe/spipe_knowledge_compiler/state.md`, cross-lane indexes, integration manifests, and this plan. Agents must preserve unrelated dirty files, stage only explicit owned paths, and return commit hashes plus verification evidence. No agent may declare the feature complete; the final reviewer audits AC-1 through AC-17 plus delivery criterion DC-1 against current files and command evidence.

## 2. Interfaces frozen before fan-out

Wave 0 derives and publishes these names and versioned contracts from accepted requirements before lower-model sidecars or implementation lanes begin. It does not pre-approve architecture decisions before the requirements and threat model are complete:

- Core: `KnowledgeCompiler`, `KnowledgeSnapshot`, `KnowledgeDelta`, `ArtifactRecord`, `SectionRecord`, `TraceEdge`, `DiagnosticRecord`. `KnowledgeDelta` is the sole incremental envelope and contains ordered `ArtifactDelta`, `GraphDelta`, and `IndexDelta` payloads; those payload types are not competing top-level update protocols.
- Internal ports: `LexicalSearchPort`, `SemanticSearchPort`, `SymbolIndexPort`, and `ProjectionPort`. Core services depend only on these exact `*Port` contracts; no generic search or source-symbol port alias is part of the frozen interface.
- External accelerators: `SearchProvider`, `SourceSymbolProvider`, and `ProjectionProvider`. Adapter mappings are explicit: `SearchProviderAdapter` satisfies `LexicalSearchPort` and, only when advertised, `SemanticSearchPort`; `SourceSymbolProviderAdapter` satisfies `SymbolIndexPort`; and `ProjectionProviderAdapter` satisfies `ProjectionPort`. Dependency-free in-process implementations satisfy the same ports without masquerading as external providers.
- Mutations: `RefactorPlan`, `TransactionReceipt`, `RebalanceProposal`, `PromotionCandidate`. `RefactorPlan` is the only mutation-plan contract name.
- Protocol operations: `spipe_list`, `spipe_read`, `spipe_search`, `spipe_resolve`, `spipe_trace`, `spipe_diagnostics`.
- Phase exchange: the task/research/architecture/spec/implement/refactor/verify/ship UID input/output records used by Wave 7. Their contracts freeze in Wave 0; harness generation remains a separate Wave 9 deliverable.
- Manual flow helpers: `step("Index canonical knowledge artifacts")`, `step("Browse virtual knowledge views")`, `step("Search and trace artifacts")`, `step("Apply a transactional refactor")`, and `step("Audit tree balance and promotion candidates")`.
- Setup/checkers: `setup_spipe_knowledge_fixture`, `check_spipe_knowledge_compiler`, `check_spipe_provider_parity`, `check_spipe_refactor_recovery`, `check_spipe_virtual_view_safety`.
- Any incomplete scenario or adapter must fail fast with `assert(false)` or `fail(...)`; empty bodies, TODO passes, and inferred-only strict evidence are forbidden.

Contract changes require an ADR/design update, merge-owner approval, and coordinated consumer changes. Sidecars propose changes; they do not silently rename an interface.

## 3. Non-overlapping ownership lanes

| Lane | Exclusive implementation ownership | Published boundary | Forbidden concurrent edits |
|---|---|---|---|
| A — SPipe core | SPipe `src/core`, `src/model`, `src/storage`, `src/format`, `schema` | snapshot/delta/model/storage APIs | MCP, search, rebalance internals |
| B — Workspace/parser | SPipe `src/parser`, `src/workspace` | deterministic parse deltas and project registry | model schemas without A approval |
| C — Search core | Simple `src/lib/common/search` | canonical scoring/provider protocol | database adapters |
| D — SPipe search/view/MCP | SPipe `src/search`, `src/view`, `mcp` | `spipe://` resolver and read-only protocol | canonical parser/model schemas |
| E — Database adapters | Simple textual, embedded/DBFS, server search paths | common-search adapters | scorer internals |
| F — Trace/source/SSpec | SPipe `src/graph`, `src/diagnostics`; Simple provider app/symbol export | typed trace and symbol snapshot | rebalance objective |
| G — Refactor | SPipe `src/refactor` | plan/apply/rollback transaction API | arbitrary canonical writes elsewhere |
| H — Rebalance | SPipe `src/rebalance` | audit/proposal only | graph model and physical moves |
| I — Promotion/skills | SPipe `src/promote`, `src/skill`, `skill_src`, `knowledge` | reviewed promotion and generated surfaces | generated harness files by hand |
| J — Tests/guides | owned feature specs, mirrored manuals, fixtures, benchmarks, operator guide | evidence and documentation | product code except agreed test hooks |

Shared files are integrated only by `/root`. If a path is already dirty from an unknown lane, the assignee stops editing that path and reports the conflict.

## 4. Dependency waves

### Wave 0 — Requirements, baseline, threat model, and contracts

**Owners:** merge owner + audit sidecars.  
**Deliverables:** final REQ/NFR set and acceptance-to-evidence matrix; current CLI/MCP/setup/link behavior snapshots; repository and search/DB/trace inventories; path/URI/symlink/junction, authorization/cache, prompt-content, remote-provider, transaction, worktree, and linked-project threat model; benchmark corpora; linked-project and multi-worktree fixtures; extended config schema proposal; architecture decision candidates derived after requirements; startup, doctor, scan, duplicate, and search baselines. The performance baseline records fixed hardware/OS/toolchain/build mode, fixture revision and size, warm/cold procedure, sample count, latency percentiles, maximum RSS, and raw evidence location; later NFR comparisons must use the same qualified baseline or explicitly requalify a replacement. NFR-014 is selected as: on that qualified fixture and hardware, the warm elapsed wall-clock time for a one-artifact incremental graph/index update must be at least 20× cheaper than a warm full rebuild, measured by the same harness and aggregation rule. Research values such as an absolute P95 latency in milliseconds are provisional qualification candidates only; Wave 0 freezes an absolute budget only after the machine, corpus, profile, warm/cold state, and measurement method are fixed.
**Published interfaces:** all names in Section 2, serialization/versioning rules, provider capability negotiation, diagnostic-code registry, file ownership map.  
**Exit gates:** requirements are selected and stable; baseline evidence is reproducible on the recorded hardware qualification; threats have owners, mitigations, and negative-test evidence plans; SPipe/Simple ownership has no ambiguity; fixture includes missing link, dirty worktree, and visibility classes; all research decisions map to a requirement or post-requirement ADR candidate. Network HTTP and every mutating operation remain disabled until their specific threat-model gates pass.

### Wave 1 — Modularize SPipe without behavior change

**Depends on:** Wave 0. **Owners:** A with narrow B/D participation.  
**Deliverables:** thin `cli/spipe.js` and `mcp/server.js`; extracted CLI routing, config/link/doctor and protocol/transport modules; deterministic SDN/JSON result types; no new baseline Node dependency.  
**Exit gates:** existing command/setup/doctor fixtures retain behavior; on the fixed Wave 0 hardware-qualified harness, no-op `spipe doctor` elapsed wall-clock regresses by no more than 10% from baseline (using the declared sample/aggregation method), and other compatibility-command regressions are likewise no more than 10% unless explicitly waived with evidence; legacy MCP stdio still initializes; output compatibility differences are documented and approved; dispatcher files contain no new domain logic.

### Wave 2 — Schemas, identity, parsers, workspace registry

**Depends on:** Wave 1. **Owners:** A and B.  
**Deliverables:** project/artifact/section/edge/alias/view schemas; Markdown, SDN, SSpec, and source-metadata parsers; dry-run UID injection; linked-project/worktree registry; content-addressed cache and per-worktree overlay; inventory diagnostics.  
**Exit gates:** deterministic parse/round trip; duplicate UID and ambiguous alias detection; adoption moves no canonical file; dirty overlays are isolated; paths are locations, never identities.

### Wave 3 — Read-only graph and diagnostics

**Depends on:** Wave 2. **Owners:** F consuming A/B contracts.  
**Deliverables:** typed graph/query APIs; provenance-bearing link, heading, requirement, SSpec, test, and source edges; broken-link and trace-gap diagnostics; `TRC231`/`TRC232` compatibility; trace matrix.  
**Exit gates:** every edge records origin/status/confidence/evidence; inferred edges cannot satisfy strict policy; one-file incremental graph equals clean rebuild; snapshots and diagnostics are deterministic.

### Wave 4 — Canonical BM25 and provider protocol

**Depends on:** Waves 2–3 contracts. **Owners:** C plus D fallback adapter.  
**Deliverables:** shared documents/analyzer/corpus stats/scorer/top-k/explanations/provider protocol; exact + BM25 + graph candidate fusion using deterministic Reciprocal Rank Fusion as the foundation; dependency-free fixed-point JavaScript fallback; migration of the DBFS scorer compatibility facade to the canonical common scorer; golden corpus and adapter conformance kit; initial search/resolve/read commands. Remaining textual, embedded, and server database adapters consume this contract but are implemented only in Wave 10.
**Exit gates:** provider ordering/ties and RRF explanations match golden results; real document lengths are used by the DBFS path; DBFS legacy entry points preserve compatibility while producing canonical-scorer golden parity; embeddings are optional; incremental index equals clean rebuild; the adapter conformance kit is frozen for Wave 10.

### Wave 5 — Virtual resources, tools, and materialization

**Depends on:** Waves 3–4. **Owners:** D.  
**Deliverables:** authoritative `spipe://` resolver; lifecycle/feature/component/layer/matrix/trace/project/status/diagnostic projections; bounded MCP list/read/search/resolve/trace/diagnostic tools and resources; legacy stdio plus a stateless MCP 2026 HTTP implementation held disabled until its Wave 0 transport/auth/cache threat gates pass; deterministic pagination/cache hints; `.spipe/view/` materializer; editor-provider skeleton.  
**Exit gates:** model navigates without canonical paths; each artifact-representation file maps to exactly one canonical artifact UID, while directory indexes, search pages, trace matrices, diagnostics, and other aggregate outputs carry deterministic synthetic projection UIDs bound to the immutable snapshot UID and query/view parameters; writes fail closed; outputs are deterministic, paginated, and bounded; private data never receives public cache scope; unchanged materializations are not rewritten; HTTP cannot be enabled without path/auth/cache negative tests passing.

### Wave 6 — Transactional refactoring and repair

**Depends on:** Wave 5. **Owner:** G.  
**Deliverables:** artifact move/rename and section/tag/feature/component rename; reverse-reference index; hash-preconditioned plan/journal/apply/verify/rollback; raw-move recovery; cross-project checks; pre-commit/CI hooks. Mutation entry points ship disabled until the transaction, path-escape, authorization, concurrent-worktree, and rollback threat gates from Wave 0 pass.  
**Exit gates:** phase-by-phase fault injection yields valid old or new state; UID, aliases, and accepted trace survive; approved operations introduce no broken links; ambiguity fails closed; rollback restores content and graph hashes; unauthorized, stale-snapshot, and cross-root mutations fail closed before mutation can be enabled.

### Wave 7 — Full traceability and phase integration

**Depends on:** Waves 3 and 6. **Owner:** F with I/J consumers.  
**Deliverables:** stable Simple source-symbol snapshot provider; SSpec scenario/run/result nodes; advisory/standard/strict/mission-critical profiles; stale-result logic; implementation of the Wave 0-frozen phase UID input/output contracts; explained trace suggestions. Skill/harness compilation does not belong to this wave.
**Exit gates:** representative research-to-result matrices are complete; strict modes reject inferred-only evidence; trace survives physical reorganization; readable `state.md` remains while UIDs are authoritative.

### Wave 8 — Hybrid tree audit and rebalancer

**Depends on:** Waves 5 and 7. **Owner:** H.  
**Deliverables:** tree metrics; weighted graph/hyperedges; constrained Leiden-compatible communities; balanced multilevel partitioning; local refinement, hysteresis/cooldown/churn penalties; automatic virtual projection and proposal-only physical changes. Lane H owns a versioned deterministic seed derivation (`snapshot UID + scope UID + algorithm version`), fixed-point/quantized comparison precision, stable iteration/tie ordering, memory and candidate-edge budgets, and an explicit fallback path (deterministic threshold audit/proposal with no clustering) for unavailable providers or exceeded budgets.  
**Exit gates:** communities are connected; must/cannot-link and fixed roots hold; identical inputs, seed, precision, and algorithm version produce byte-identical proposals; peak memory stays within the fixed hardware-qualified Wave 0 NFR budget; provider/budget failure selects the documented deterministic fallback rather than partial clustering; unchanged runs produce no churn; each move has objective/evidence/rollback explanation; physical application requires explicit approval.

### Wave 9 — Common knowledge and skill compiler

**Depends on:** Waves 4, 7, and 8. **Owner:** I.  
**Deliverables:** two separately gated products: (1) exact/MinHash/SimHash/BM25/structural/graph/optional-semantic candidate discovery, scored review reports, family/common catalog, and provenance-preserving `extends`/override; (2) canonical skill sources and deterministic Claude/Codex/Gemini generators implementing the already-frozen phase contracts. Skill generation neither depends on nor implies approval of a promotion candidate.
**Exit gates:** promotion is never automatic; conflicts and revisions are recorded; every consumer validates; project constraints remain; generated files carry source UID/version/hash and stale outputs fail verification; skill generation passes independently when the promotion catalog is empty or disabled.

### Wave 10 — DB optimization and optional semantics

**Depends on:** Wave 4 common search/provider contract; Wave 9 is required only for optional promoted-knowledge/semantic consumers, not for core database adapters. **Owners:** E with C review.  
**Deliverables:** database work remaining after Wave 4's DBFS scorer-facade migration: textual BM25 side index; remaining embedded adapters with exhaustive/WAND paths; server segmented/Block-Max-WAND index, shard merge, capability filtering, cancellation/budgets; optional ANN/embedding providers. These adapters add textual, embedded, server, and optional semantic candidate sources to the deterministic RRF foundation already implemented and verified in Wave 4; Wave 10 neither introduces nor redefines fusion.
**Exit gates:** each DB kind proves transactional/snapshot consistency; deny-wins tests prevent field/document leakage; exhaustive and optimized top-k are identical; provider failure degrades to lexical/graph behavior; performance and RSS gates have named evidence.

### Wave 11 — OS virtual filesystem (explicitly deferred)

FUSE/ProjFS is out of the committed implementation scope. Reconsider only if measured client evidence shows MCP tools/resources, materialized views, and the editor adapter are insufficient. Any future wave requires a new ADR, threat model, invalidation design, read-only enforcement tests, and separate user approval.

## 5. Sidecar strategy and review

Lower-cost sidecars may perform bounded, read-only audits or draft fixtures after Wave 0 freezes interfaces:

- repository/current-state and compatibility inventory;
- requirements/AC/trace matrix audit;
- security, URI, worktree, and linked-project threat audit;
- search/provider/database parity fixture drafting;
- MCP pagination/cache/visibility review;
- refactor fault-injection and rebalancer adversarial fixtures;
- SSpec manual readability and guide completeness review;
- duplicate/common-knowledge candidate evaluation.

Sidecars return paths, findings, and evidence; they do not mark exclusions or done. Broad findings, generated manuals, security decisions, and acceptance marks require review by the highest-capability primary/final reviewer. `/root` resolves contradictions and owns merges.

## 6. Commit, rebase, and push checkpoints

This is a massively dirty plain-Git worktree shared with concurrent agents. Use these controls for every checkpoint:

1. Before editing, record `git status --short -- <owned paths>` and the tracked-file count (`git ls-files | wc -l`). Do not inventory or stage the whole dirty tree repeatedly.
2. Stage only explicit owned pathspecs: `git add -- <path...>`. Never use `git add -A`, `git add .`, broad globs, stash, reset, clean, or checkout to discard work.
3. Inspect `git diff --cached --name-status`; abort if any path is outside the lane. Commit one coherent, verified increment with wave/feature in the message.
4. Push at each stable wave or smaller contract-compatible checkpoint: schemas/contracts; modularization; graph; search; views/MCP; refactor; trace; rebalancer; promotion/skills; DB optimization; final guides/evidence.
5. Before synchronization, confirm no other agent owns the affected paths. Fetch and rebase linearly onto `main@origin`; do not merge. Re-check tracked-file count before/after and investigate any unexpected deletion/addition.
6. Push GitHub `main` only from the merge owner, with credential environment overrides unset as required by repository policy. A lane agent returns a commit hash and never pushes an integration branch over `main` independently.
7. If rebase conflicts touch unrelated dirty work, stop and hand the commit to `/root`; do not absorb, revert, or repair another lane's files.

“Push often” means after verified, reviewable increments—not after broken intermediates and never by sweeping unrelated dirty content into a commit.

## 7. Verification and completion ownership

Lane J maintains a requirement-to-evidence matrix covering AC-1 through AC-17 and DC-1. Each wave gets one focused verification pass; failures permit at most three distinct verify/fix cycles, and already-green unchanged checks are not rerun. Required evidence includes unit/property/integration/SSpec tests, generated manual review, provider parity, incremental-versus-clean parity, refactor fault injection, path/security isolation, rebalancer stability, promotion safety, DB authorization, latency/RSS benchmarks, runtime-facade audits, applicable compiler/lib/MCP/LSP/package smokes, and DC-1's path-scoped linear-sync/push evidence.

Final sequence:

1. `/root` integrates only reviewed path-scoped commits and updates state/evidence indexes.
2. Independent highest-capability reviewer audits every AC, exclusion, sidecar claim, generated manual, security boundary, and “done” mark against authoritative current state.
3. `/root` fixes accepted findings within the three-cycle cap.
4. Verify emits `STATUS: PASS`; documentation and guides are already current.
5. Merge owner performs the final linear rebase, tracked-file-count check, and GitHub `main` push. Release/versioning is a separate authorized step.
