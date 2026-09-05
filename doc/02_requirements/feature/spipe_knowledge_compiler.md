<!-- codex-research -->
# SPipe Knowledge Compiler — Feature Requirements

**Status:** Selected / final  
**Date:** 2026-08-25  
**Source:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`  
**State acceptance criteria:** `.spipe/spipe_knowledge_compiler/state.md`

## Selection Record

The user selected the full knowledge-compiler direction documented by the source research: a canonical lifecycle tree, immutable artifact identity, virtual multidimensional views, typed traceability, deterministic hybrid retrieval, transactional refactoring, hybrid tree rebalancing, and reviewed common-knowledge promotion. For host authority, F1/N1 is selected: the transactional authority service is the required portable P3 publisher. F2/N2 is retained only as a separately admitted optional native backend. F3/N3 is rejected: offline work may continue, but it is not a substitute for canonical publication or canonical authority-open. These requirements therefore record a completed selection; no requirement option remains pending.

Normative terms `must`, `must not`, `should`, and `may` have their usual requirements meaning. Paths are locations, never identities.

## Requirements

### Canonical knowledge and identity

#### REQ-SPKC-001 — Canonical lifecycle organization

SPipe must retain one canonical, single-copy physical document tree organized by lifecycle/artifact kind. Feature, component, layer, project, status, and trace classifications must be orthogonal metadata and generated projections. Changing a top-level lifecycle root must require an explicit architecture decision.

Source: research §§1.1, 3, 6.1–6.2; ADR-001. Traces: AC-1, AC-2, AC-5, AC-9.

#### REQ-SPKC-002 — Stable artifact and section identity

Every managed artifact must have an immutable opaque UID. Referenced or trace-critical sections must have stable section UIDs. Human-readable keys, titles, headings, canonical paths, and virtual paths may change without changing identity; old semantic keys and heading slugs must remain resolvable aliases according to policy.

Source: research §§4.2, 8.1–8.2, 13.3; ADR-002. Traces: AC-1, AC-3, AC-7, AC-8.

#### REQ-SPKC-003 — Typed knowledge graph

The compiler must represent the documented workspace, project, revision, artifact, section, evidence, requirement, design, plan, specification, source, test, result, classification, and common-knowledge node kinds in a typed graph. Every edge must record its type, provenance, origin, review status, confidence, creator, and supporting evidence where applicable.

Canonical edge names must use active direction (`contains`, `classifies`, `evidence_for`, `derives`, `satisfies`, `realizes`, `schedules`, `specifies`, `implements`, `verifies`, `covers`, `produces`, `links_to`, `aliases`, `supersedes`, `extends`, `promoted_from`, `depends_on`, and `mounted_as`). Inverse relations are derived queries and must not be persisted as separate edge types.

Source: research §§8.3–8.5, 9.1; ADR-007–008. Traces: AC-1, AC-2, AC-8, AC-10.

#### REQ-SPKC-004 — Deterministic parsing and snapshots

The dependency-free SPipe core must parse canonical Markdown, SDN, SSpec, and supported source metadata into deterministic immutable snapshots plus incremental deltas. Missing, duplicate, malformed, or ambiguous identity must produce stable diagnostics. A path move alone must never create a new artifact.

Source: research §§5, 12, 18.1, Waves 2–3. Traces: AC-3, AC-4.

#### REQ-SPKC-005 — Project and workspace registry

The registry must model semantic dependency, physical linkage, consumed revision, mount location, and trust independently. It must support standalone repositories, linked projects, submodules, path/symlink/junction mounts, packages, and Git worktrees without inferring semantic dependency from physical linkage.

Source: research §§4.1, 12.4–12.5. Traces: AC-2, AC-3, AC-8, AC-14.

### Virtual views and LLM access

#### REQ-SPKC-006 — Required virtual projections

The projection service must expose read-only lifecycle-, feature-, component-, layer-, matrix-, trace-, project-, status-, and diagnostics-first views over the same canonical artifacts. Virtual reorganization must not duplicate or move canonical content.

Source: research §§6.3, 14.1; ADR-003–004. Traces: AC-5, AC-9.

#### REQ-SPKC-007 — Unambiguous virtual paths

Every generated virtual artifact document must resolve to exactly one canonical artifact UID. Aggregate directory, search, trace, and diagnostics documents must instead resolve to exactly one deterministic synthetic `ProjectionUid`, represented as `spkp1-<lowercase-sha256>`, where `<lowercase-sha256>` is the 64-character lowercase hexadecimal SHA-256 digest of the canonical, length-delimited UTF-8 tuple `projection_v1(workspace_uid, snapshot_id, view_kind, normalized_logical_path, normalized_parameters_hash, effective_auth_scope_hash, page_start_key)`. Each tuple field must use the architecture-defined canonical normalization; an absent page start key must use the canonical empty value, not omission. A projection UID must never masquerade as an artifact UID or canonical ownership. Generated slugs must be deterministic, collisions must use a deterministic short-UID suffix, and each materialized directory must provide a machine-readable mapping to canonical artifact or synthetic projection identity as applicable.

Source: research §6.4. Traces: AC-5.

#### REQ-SPKC-008 — MCP resources and model-callable tools

SPipe must expose equivalent discovery through MCP resources and model-callable tools. The tool surface must include list, read, search, resolve, trace, and diagnostics operations. Every request must carry an authenticated principal and workspace/project scope where the transport supports identity; refactor, tree, promotion, and every other mutation must require a separately authorized, operation-bound capability and must not be reachable by presenting a read credential.

Source: research §§1.2, 7.2–7.3; ADR-003. Traces: AC-5, AC-6, AC-7.

#### REQ-SPKC-009 — Materialized and editor views

SPipe must provide bounded generated read-only files under `.spipe/view/` for file-only agents. It should provide a read-only editor virtual-filesystem adapter when client demand justifies it. Direct writes to either view must fail closed and approved canonical changes must route through refactor operations. Any supported operation that creates, replaces, removes, or cleans entries beneath the dedicated generated-view root must execute only through an admitted `SafeFilesystem.Materializer` capability that provides descriptor-relative root containment, no-follow ancestor/target traversal, post-open identity validation, and safe temporary-file replace/remove for that platform. This narrower capability must grant no access to canonical artifacts. If the adapter cannot prove those capabilities, materializer mutation capability must be reported unavailable and no mutation may be attempted.

Source: research §§7.5–7.6. Traces: AC-5, AC-7, AC-14.

#### REQ-SPKC-010 — MCP compatibility and negotiation

The MCP core must remain transport-neutral, preserve existing stdio-client behavior, and support the target stateless MCP 2026 transport through negotiated protocol capabilities. Pagination, cache hints, notifications, and response fields must only be emitted where supported by the negotiated protocol. HTTP requests must authenticate before workspace resolution, authorize every resource/tool invocation, bind cursors to principal, scope, snapshot, and query, and prevent shared caches from mixing principals, visibility classes, authorization results, or private payloads. Stdio's local trust assumptions must not be inherited by HTTP.

Source: research §7.4; ADR-014. Traces: AC-6, AC-15.

### Search and providers

#### REQ-SPKC-011 — Exact and lexical retrieval

Search must support exact UID/key/alias/metadata lookup and deterministic fixed-point BM25 over weighted identifier, title, heading, classification, and body fields. Stable document identity must break equal-score ties.

Source: research §§10.1–10.3. Traces: AC-4, AC-12.

#### REQ-SPKC-012 — Hybrid retrieval and explanations

Hybrid retrieval must combine exact, BM25, graph-neighborhood, and optional semantic candidates. Reciprocal Rank Fusion must be the initial cross-signal fusion contract; bounded boosts and penalties may rerank results. Every result and suggested trace must explain contributing matches, ranks, graph proximity, and stale/deprecated state.

Source: research §11; ADR-009. Traces: AC-4, AC-10, AC-14.

#### REQ-SPKC-013 — Portable provider protocol

SPipe must operate without Simple, an embedding model, a network service, or external Node dependencies for offline parsing, graph, exact/lexical search, diagnostics, and other non-canonical work. A versioned provider protocol must allow a Simple-native or server provider when configured and healthy, while a dependency-free deterministic JavaScript lexical fallback remains mandatory for that offline/search baseline. This portability does not apply to P3 canonical publication or canonical authority-open: both require the transactional authority service in REQ-SPKC-031, and neither Node nor the JavaScript fallback may emulate, select, or replace it. Provider executables/endpoints must be selected from trusted configuration rather than artifact content; launch arguments and environment must be allowlisted and secret-minimized. Responses must be size/time/schema/version bounded, treated as untrusted until validated, and unable to inject canonical paths, accepted trace authority, capabilities, prompt policy, or executable instructions. Protocol 1.0 request deadlines must be in the inclusive range 1 through 30,000 milliseconds and measured from acceptance of the first frame-header byte, so framing, decoding, validation, normalization, hashing, execution, and response construction consume the same semantic budget. `invalid_utf8` and `frame_too_large` are payload-free local `TransportDiagnosticV1` classes, never bound `ProviderErrorV1` codes; before complete typed host binding they close the transport silently without fabricating a response.

Source: research §§10.5, 18.3; ADR-006. Traces: AC-4, AC-12, AC-15.

#### REQ-SPKC-014 — Shared Simple search core

`std.common.search` must own the canonical Simple lexical-scoring contract. Existing DBFS search entry points must remain compatibility facades during migration, and every implementation must be validated against one golden corpus and ordering contract. Parsers, analyzers, phrase expansion, postings traversal, ranking, explanation generation, and provider responses must obey configured byte, token, nesting, term, clause, candidate, time, and memory budgets and return a stable bounded failure instead of continuing unbounded work.

Source: research §§2.3, 10.1–10.3, 19.1. Traces: AC-4, AC-12.

#### REQ-SPKC-015 — Three database adapters

Simple must provide explicit adapters for textual DB, embedded DB/DBFS, and DB server search. Each adapter must preserve its tier's transaction, checkpoint, snapshot, durability, tenancy, cancellation, query-budget, field-redaction, and capability semantics rather than pretending the three database kinds are interchangeable. Explanations, counts, timing, and cache behavior must not leak unauthorized document or field existence.

Source: research §§2.4, 10.4, 19.2. Traces: AC-12, AC-14.

#### REQ-SPKC-016 — Source-symbol provider

Simple must expose stable compiler/HIR-derived source-symbol snapshots containing identity, module, kind, name, signature hash, definition/reference spans, trace annotations, and revision/content hashes. Export must apply project visibility and path-redaction policy before crossing a provider boundary. Other languages may use pluggable analyzers or non-authoritative textual fallback subject to the same parser budgets and trust restrictions.

Source: research §19.4. Traces: AC-8, AC-12.

### Traceability and safe change

#### REQ-SPKC-017 — Trace policy profiles

SPipe must provide advisory, standard, strict, and mission-critical trace profiles. Strict and mission-critical gates must count only accepted explicit or deterministic generated evidence created by an authorized actor or trusted generator. Structural, lexical, semantic, provider-returned, document-authored, and LLM-inferred edges must remain untrusted review candidates unless a profile explicitly permits advisory use; artifact text must never self-assert accepted trace authority.

The design must define the required edge-authority table for every profile and lifecycle transition.

Source: research §§9.2–9.4; ADR-008. Traces: AC-8, AC-14.

#### REQ-SPKC-018 — Trace diagnostics and compatibility

Trace checking must diagnose missing design, SSpec, implementation, unit/integration/system test, and stale-result evidence across linked projects and worktrees. It must preserve the existing mirrored SSpec/manual validation and `TRC231`/`TRC232` behavior as a compatibility projection while treating stable IDs as authoritative.

Source: research §§2.5, 9.3–9.5. Traces: AC-8, AC-13.

#### REQ-SPKC-019 — Transactional refactoring

Artifact, section, tag, feature, and component rename/move operations must resolve identity, enumerate references, validate authorization plus revision/hash/file-identity preconditions and collisions, journal the complete plan and original metadata, apply descriptor-relative operations without re-resolving attacker-changeable paths, preserve permissions and required ownership/timestamps, preserve aliases and accepted trace edges, reindex incrementally, verify the result, and support recovery and rollback. Canonical mutation requires the distinct admitted `SafeFilesystem.Refactor` capability, which includes canonical-root-scoped descriptor-relative open/create/replace/rename/remove, no-follow traversal, post-open identity validation, cross-device detection, metadata preservation, durability primitives, and rollback support; possession of `SafeFilesystem.Materializer` must not imply or grant it. If any required primitive is unavailable, that refactor capability or operation must fail closed. Apply must require a short-lived, single-use token bound to principal, workspace/worktree, snapshot, operation digest, targets, and expiry; replay, partial-scope use, or post-plan target substitution must fail closed.

Transaction journals are durable per-worktree operational state until commit or rollback completes; they must not be treated as disposable search cache. Recovery must distinguish pre-commit, partially applied, committed-but-unverified, rollback-in-progress, and irrecoverable states; injected crash, I/O, permission, concurrent-write, and rollback failures must never be reported as success. The design owns exact storage, retention, locking, metadata policy, and platform-specific atomicity.

Source: research §§13.1–13.3, 24.5; ADR-004. Traces: AC-7, AC-8, AC-14.

#### REQ-SPKC-020 — Raw change recovery

For changes made outside SPipe, identity recovery must consider UID, exact content hash, Git rename evidence, bounded near-duplicate fingerprints, lexical/semantic candidates, then explicit review. Candidate generation must obey configured parser/query/resource budgets and must not follow content-controlled paths or launch content-selected providers. Ambiguous, unauthorized, cross-trust, or metadata-conflicting recovery must be diagnosed rather than guessed.

Source: research §13.4. Traces: AC-7, AC-14.

### Rebalancing and reusable knowledge

#### REQ-SPKC-021 — Constrained hybrid rebalancing

Tree audit and rebalancing must use a sparse weighted graph or hypergraph with explicit trace and cohesion evidence, must-link/cannot-link constraints, connected community detection, balanced multilevel partitioning, and constrained local refinement. Must-link constraints express clustering cohesion and must not override fixed lifecycle physical roots.

Source: research §§14.2–14.6; ADR-010. Traces: AC-9.

#### REQ-SPKC-022 — Conservative physical organization

Virtual views may rebalance automatically and deterministically. Physical canonical moves must require an explainable approved proposal that records objective change, confidence, affected references, aliases, constraints, and rollback mapping. Threshold values remain design/configuration decisions calibrated from Wave-0 evidence.

Source: research §§14.1, 14.7–14.9; ADR-011. Traces: AC-9, AC-14.

#### REQ-SPKC-023 — Common-knowledge candidate discovery

Candidate discovery must use a sparse cascade of normalized hashes, shingles/fingerprints, BM25, structural and trace-role evidence, existing duplicate analysis, and optional semantic similarity. Reports must explain every score component, source project, conflict, and proposed scope.

Source: research §§15.2–15.4. Traces: AC-10.

#### REQ-SPKC-024 — Reviewed promotion and extension

Promotion to project-family or SPipe-common knowledge must require provenance, conflict analysis, authorized human/expert approval, license and attribution compatibility, secret/credential/personal-data scanning, trust/visibility review, and validation in every consuming project. Content that fails or cannot prove these gates must not be published. Normal common promotion requires evidence from at least two independently configured projects; an expert exception must record its authority and rationale but must not waive license, secret, or visibility gates. Project-specific constraints must remain expressible through `extends` and local overrides.

Source: research §§15.1, 15.5–15.6; ADR-012. Traces: AC-10, AC-14.

#### REQ-SPKC-025 — Canonical skill and rule compiler

One canonical skill/rule source must deterministically generate supported Claude, Codex, Gemini, and agent-facing surfaces. `trust_scope` is a closed enum with exactly `untrusted_data`, `reviewed_reference`, and `executable_policy`. New or ordinary indexed content, retrieved/provider output, and content lacking an authorized registry record must derive as `untrusted_data`; accepted human-reviewed knowledge may be assigned `reviewed_reference`; only a principal holding the dedicated policy-publisher capability may assign `executable_policy` to a canonical source in an approved skill/rule registry. Content, front matter, aliases, paths, linked-project trust, providers, and generated output must never self-elevate trust scope. Only registry-authorized `executable_policy` sources may generate executable agent instructions; all other content must remain quoted/delimited data. Generated artifacts must identify source UID, `trust_scope`, registry/policy version, generator version, and content hash. Before generation and verification, SPipe must validate the registry authorization, source hash/revision, publisher authority, visibility, and absence of an intervening trust downgrade; verification must reject unknown enum values, stale or unauthorized sources, secret-bearing output, trust escalation, or hand divergence.

Source: research §16; ADR-013. Traces: AC-11, AC-16.

### Operation, compatibility, and delivery

#### REQ-SPKC-026 — Stable CLI surface

The CLI must provide the documented index, view, search, resolve, trace, refactor, tree, knowledge, skill, and doctor command families with stable text, SDN, and JSON machine output where applicable.

Source: research §17. Traces: AC-5, AC-7, AC-9, AC-10, AC-15.

#### REQ-SPKC-027 — Compatibility-preserving modularization

Existing SPipe CLI commands, setup/link surfaces, and doctor behavior must remain available. The current CLI and MCP monoliths must become thin compatibility dispatchers over separately testable services without adding a baseline Node runtime dependency.

Source: research §§2.2, 18.1–18.3, Waves 0–1. Traces: AC-6, AC-15.

#### REQ-SPKC-028 — Phase graph contracts

Development phases must exchange stable graph identities and typed relations for task, evidence, requirement, design, plan, SSpec, source, test, result, and release objects. Human-readable `state.md` logs must remain available but must not be the sole machine-readable contract.

Source: research §16.2–16.3. Traces: AC-8, AC-11, AC-16.

#### REQ-SPKC-029 — Staged migration without identity loss

Migration must proceed through observation, stable identity, virtual views, typed trace conversion, safe refactors, virtual rebalancing, approved physical cleanup, and reviewed promotion. Adoption must not require an initial canonical tree move or invalidate existing SSpec/manual paths.

Source: research §23. Traces: AC-2, AC-7, AC-8, AC-9, AC-10, AC-16.

#### REQ-SPKC-030 — Deferred OS virtual mounts

FUSE/ProjFS implementation is excluded from the initial required implementation. The design must retain a read-only adapter boundary and an evidence-based decision gate; implementation may proceed only if MCP, materialized, and editor views are proven insufficient for required clients.

Source: research §§7.6, Wave 11; ADR-015. Traces: AC-14.

### Host authority selection

#### REQ-SPKC-031 — Transactional publication authority

P3 publication must use an admitted transactional authority service as the sole portable owner of `replaceCurrentIfExactV1`. The service must make each identity-scoped, fence-bound compare-and-publish request at one durable linearization point, persist its decision before acknowledging success, and expose `current` only as a validated projection of that decision. Clients, including Node, must never make a local pointer, cache, rename, lock, write-then-compare sequence, or provider-selection seam authoritative.

The service must accept only the closed P3 request algebra: exact raw predecessor bytes/digest for every successor, paired-null only for genesis, and `(scopeBytes, generation)` fencing. Its result must preserve the existing closed `replaced` or `mismatch` result and the only fatal shape, a thrown/rejected `HostReplaceFatalV1` with exactly code `SPK704`, reason `corrupt_successor_missing_current`, and generation `G`. A fatal result must contain no `outcome`, winner/current bytes, retry token, or receipt. A `ServiceTransportFailureV1` is a distinct request-layer failure only before journal admission, outside the P3 `replaced`/`mismatch`/fatal algebra; it contains no P3 result, receipt, or authority mutation. An absent `current` is a mismatch only for a paired-null genesis request and is fatal/corrupt state for a successor.

After journal admission, a timeout, partition, or lost response must never let a client infer success or construct a fallback. The client must resolve the immutable request/idempotency key through the service and receive either the exact accepted terminal/winner evidence or a definitive no-admission result; ambiguous local state is not a result. An invalid but authenticated operation capability, scope, trust epoch, or authorization binding must instead return an explicit non-enumerating `CapabilityDeniedV1` before admission; only service authentication/availability/transport failure uses `ServiceTransportFailureV1`. Both pre-admission failures leave no journal admission, current mutation, or receipt.

The service must authenticate the caller and bind authorization, workspace, project/revision, scope, proposal/record digest, predecessor, generation, idempotency/replay key, and response evidence to its durable decision. It must prevent split brain, stale replay, cross-tenant publication, and publication by an untrusted or unavailable client. Restart/recovery must expose exactly one complete old-or-new authority state and preserve an auditable decision record.

Source: selected F1/N1; research §43.8; architecture §21.10; detail design §12.10. Traces: AC-5, AC-7, AC-8, AC-14, AC-17.

#### REQ-SPKC-032 — Optional admitted native authority backend

A platform-specific native provider may implement the same transactional authority-service interface only after separate admission for an explicit OS/kernel/filesystem/version tuple. It must preserve byte-for-byte request and response semantics, the same durable linearization/fencing/recovery evidence, and the same closed error algebra as REQ-SPKC-031. It is an optional backend, not an alternative feature direction: no unsupported tuple may activate it, and Node must never select, emulate, or fall back to it through filesystem primitives, environment, argv, globals, or a public factory.

Source: selected F2/N2 as constrained optional backend; research §43.8. Traces: AC-7, AC-14, AC-17.

## Acceptance-Criteria Trace Summary

| State AC | Primary feature requirements |
|---|---|
| AC-1 | REQ-SPKC-001–032 |
| AC-2 | 001–005, 013–016, 021–030 |
| AC-3 | 002–005 |
| AC-4 | 004, 011–014 |
| AC-5 | 006–009, 026, 031 |
| AC-6 | 008, 010, 027 |
| AC-7 | 008–009, 019–020, 026, 029, 031–032 |
| AC-8 | 002–005, 016–020, 028–029, 031 |
| AC-9 | 001, 006, 021–022, 026, 029 |
| AC-10 | 003, 012, 023–024, 026, 029 |
| AC-11 | 025, 028 |
| AC-12 | 011–016 |
| AC-13 | 006–024 (behavioral test scope) |
| AC-14 | 005, 009–010, 012–013, 015, 017, 019–024, 030–032 |
| AC-15 | 010, 013–015, 027 |
| AC-16 | 025, 028–029 |
| AC-17 | All requirements, including 031–032 |
| DC-1 | Delivery control: each verified increment is isolated, committed, linearly rebased with tracked-file-count protection, and pushed according to repository policy; no product requirement substitution |

## Design-Owned Decisions

The requirements deliberately leave these choices to architecture/detail design and evidence:

- exact schema encoding, storage engines, and module/file partitioning;
- the profile-by-edge trace authority matrix;
- section-UID warning/error policy during staged migration;
- transaction-journal location, retention, locking, and fsync profile;
- negotiated MCP method/field details for each supported protocol version;
- final BM25 field weights, RRF parameters, graph boost caps, and provider wire encoding;
- final tree objective weights, size thresholds, confidence, hysteresis, and cooldown;
- benchmark hardware/corpus definitions and final absolute performance budgets;
- whether optional editor or OS-level filesystem adapters pass their decision gates.
