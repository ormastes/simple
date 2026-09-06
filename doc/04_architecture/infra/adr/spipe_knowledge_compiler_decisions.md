<!-- codex-architecture -->
# SPipe Knowledge Compiler Decision Records

**Architecture:** `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md`  
**Research:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`  
**Decision date:** 2026-08-25

These records are accepted as the baseline for implementation. A later change
must supersede the affected record explicitly; editing a path, projection, or
provider configuration does not silently revise an architectural decision.

## ADR-SPKC-001: Keep Canonical Physical Organization Lifecycle-First

### Status

Accepted

### Context

Artifacts belong simultaneously to features, components, layers, projects, and
trace chains. A physical tree can encode only one primary hierarchy without
duplication or path churn.

### Decision

Keep the fixed lifecycle roots (`research`, `requirements`, `plan`,
`architecture`, `design`, `spec`, `guide`, `tracking`, and `report`) as the
canonical physical organization. Other dimensions are metadata and projections.

### Consequences

- Positive: canonical ownership remains obvious and stable.
- Negative: feature-first navigation requires compiler-generated views.
- Neutral: changing lifecycle roots requires a separate architecture decision.

## ADR-SPKC-002: Make UIDs Identity and Paths/Headings Locations

### Status

Accepted

### Context

Paths, titles, keys, and headings change during normal refactoring. Treating
them as identity breaks links and traceability.

### Decision

Artifacts and managed sections receive immutable opaque UIDs. Keys, aliases,
canonical paths, titles, headings, and heading slugs are renameable names.
Section markers become mandatory when a section is referenced, traced, or
transaction-managed.

### Consequences

- Positive: approved moves and renames preserve conceptual identity.
- Negative: UID/alias validation and marker tooling are required.
- Neutral: unreferenced prose sections need no marker.

## ADR-SPKC-003: Expose Virtual Knowledge Through Three Initial Surfaces

### Status

Accepted

### Context

LLM hosts differ in whether they expose resources to models, support tools, or
provide only ordinary filesystem access.

### Decision

Expose the same projection model through MCP resources, model-callable MCP
tools, and bounded materialized `.spipe/view/` files. Every entry maps to one
canonical UID and one snapshot-bound projection identity consisting of
`workspace + snapshot + view + logical path + page + visibility scope`.
The exact `ProjectionUid` is `spkp1-<lowercase sha256>` over canonical SDN
`projection_v1(workspace_uid, snapshot_id, view_kind,
normalized_logical_path, normalized_parameters_hash,
effective_auth_scope_hash, page_start_key)`, using SnapshotId's UTF-8 NFC and
no-omitted/extra-field rules.
Materialization uses descriptor-relative no-follow traversal from a pre-opened
root and fails closed where equivalent handle safety is absent. URI normalization
decodes once and rejects encoded separators, NUL, dot segments, drive/UNC/device
forms, backslash ambiguity, and case-fold collisions.

### Consequences

- Positive: clients can navigate without knowing canonical paths.
- Negative: parity must be tested across all three surfaces.
- Neutral: an editor virtual filesystem may reuse the same projection port.

## ADR-SPKC-004: Keep Projections Read-Only and Refactors Transactional

### Status

Accepted

### Context

Writing through duplicated virtual locations makes canonical ownership and
conflict behavior ambiguous.

### Decision

All virtual views reject writes. Canonical edits, moves, and renames use the
sole `RefactorService`, hash preconditions, a durable pre-mutation journal,
atomic publication, validation, receipts, recovery, and rollback.
The hash-chained journal precedes every effect; replay is idempotent and never
overwrites foreign state. Rollback preserves content, type, permissions/ACL,
supported ownership/timestamps/xattrs, symlink identity, and membership.
Planning rejects unpreservable metadata; fault tests cover every durability and
publication boundary.

### Consequences

- Positive: one auditable mutation authority prevents divergent copies.
- Negative: clients need plan/apply operations rather than direct view edits.
- Neutral: raw external edits remain possible but are diagnosed and reconciled.

## ADR-SPKC-005: Make `std.common.search` the BM25 Contract Owner

**Trace:** REQ-SPKC-014

### Status

Accepted

### Context

SPipe and Simple currently have or need several lexical-search implementations.
Independent scoring contracts would drift.

### Decision

Simple's `std.common.search` owns the canonical fixed-point BM25 contract for
Simple adapters. SPipe owns provider-neutral query normalization, field weights,
tie-breaking, RRF, and golden fixtures. The dependency-free JavaScript provider
is the portable normative fallback and must have exact required parity.

### Consequences

- Positive: textual, embedded, server, DBFS, and SPipe results are comparable.
- Negative: scorer/analyzer versioning and cross-provider fixtures are mandatory.
- Neutral: accelerated top-k may differ internally but not in results.

## ADR-SPKC-006: Preserve SPipe Independence Through Provider Ports

### Status

Accepted

### Context

Simple supplies valuable acceleration and source semantics, but SPipe must work
in repositories that do not contain a Simple binary.

### Decision

SPipe core remains dependency-free and correctness-complete. Simple search,
symbol, duplication, and database capabilities attach through versioned,
capability-honest ports. Provider failure degrades to supported fallback
behavior and never changes graph truth.
Executable providers require approved path/digest or signature, safe ownership,
argv/env allowlists, shell-free launch, and resource limits. Their responses are
untrusted and must pass framing, schema, bound, snapshot/query, document-set,
ordering, and explanation validation before use or caching.

### Consequences

- Positive: SPipe stays portable while benefiting from Simple when available.
- Negative: provider negotiation, parity, and degradation need explicit tests.
- Neutral: optional semantic capability may be unavailable without failure.

## ADR-SPKC-007: Represent Traceability as a Typed Directed Multigraph

### Status

Accepted

### Context

Knowledge relations are not one linear pipeline. The same node pair may have
several relations with different provenance, authority, status, and revisions.

### Decision

Use a typed directed multigraph. Store one active-verb edge direction
(`test verifies requirement`, `source implements requirement`, and so on);
inverse labels are query projections. Each edge has its own UID, origin,
acceptance status, confidence, evidence, project/revision scope, and generator
identity where applicable.

### Consequences

- Positive: parallel relations and provenance remain independently auditable.
- Negative: graph storage and queries must support multiple edges per node pair.
- Neutral: release policy may select a DAG-shaped accepted subgraph without
  constraining the complete knowledge graph to be acyclic.

## ADR-SPKC-008: Exclude Inference From Strict Compliance Evidence

### Status

Accepted

### Context

Lexical, structural, semantic, and LLM inference can recover missing trace
candidates but may be confidently wrong.

### Decision

Only accepted explicit edges and accepted deterministic generated edges may
satisfy strict or mission-critical gates. All inferred edges remain proposals
until reviewed; confidence never substitutes for authority.
Retrieved artifacts are provenance-labelled untrusted data, never policy/tool
schema input. Body instructions cannot route tools, gain capabilities, approve
edges or transactions, widen scope, or suppress diagnostics.

### Consequences

- Positive: automation cannot silently manufacture compliance.
- Negative: strict adoption requires explicit review work.
- Neutral: advisory profiles may display inference with evidence breakdowns.

## ADR-SPKC-009: Use Exact + BM25 + Graph + Optional Semantics With RRF

### Status

Accepted

### Context

Exact identifiers, lexical relevance, graph proximity, and semantic similarity
have different strengths and incompatible raw score scales.

### Decision

Generate candidates from exact lookup, deterministic BM25, accepted graph
neighborhoods, and optional semantic providers. Fuse ranked lists initially
with Reciprocal Rank Fusion, apply bounded deterministic boosts, and return a
complete explanation.
`resolve` short-circuits on an authorized unambiguous exact UID/key/alias and
errors on ambiguity. General `search` pins such an exact hit at rank 1,
deduplicates it, and fuses remaining candidates. SPipe alone owns candidate-
source orchestration, graph traversal, RRF, boosts, and final ordering.
Providers return one named ranked candidate list and never own graph fusion.

### Consequences

- Positive: retrieval works without embeddings and remains explainable.
- Negative: judged corpora must calibrate bounded boosts and candidate limits.
- Neutral: semantic failure removes one candidate source, not core search.

## ADR-SPKC-010: Balance Documentation as a Constrained Graph Problem

### Status

Accepted

### Context

Directory quality depends on semantic cohesion, trace relationships, depth,
fanout, ownership, trust boundaries, and migration cost—not ordered keys.

### Decision

Use deterministic threshold auditing, connected community detection,
balanced multilevel partitioning, constrained local refinement, and a churn/
migration-aware objective. Trace relations are weighted by default. Must-link
is limited to generated spec/manual pairs, explicit protected bundles, and
policy-selected sole strict evidence; cannot-link enforces lifecycle, project,
visibility, and trust boundaries.

### Consequences

- Positive: clusters remain meaningful without collapsing whole trace chains.
- Negative: weights and thresholds require evidence-based calibration.
- Neutral: AVL/B-tree algorithms remain irrelevant to this organization task.

## ADR-SPKC-011: Automate Virtual Reorganization, Gate Physical Moves

### Status

Accepted

### Context

Virtual regeneration has low migration cost; canonical path moves affect links,
public interfaces, Git history, and concurrent work.

### Decision

Regenerate deterministic virtual views automatically. Emit explainable physical
move proposals only after hysteresis, stability, constraint, and improvement
gates; apply them solely through an approved refactor transaction with aliases
and rollback map.

### Consequences

- Positive: navigation improves without automatic path churn.
- Negative: physical cleanup needs human review.
- Neutral: unchanged input must yield no proposal churn.

## ADR-SPKC-012: Require Reviewed, Provenance-Preserving Promotion

### Status

Accepted

### Context

Repeated project knowledge may be reusable, but premature generalization can
erase project constraints or expose private content.

### Decision

Discovery may use exact, fingerprint, lexical, structural, graph, semantic, and
LLM evidence. Publication to family/common scope requires provenance, conflict
review, visibility/trust approval, consuming-project validation, and a separate
publish capability. Project differences use `extends` and scoped overrides.
Publication also requires compatible explicit licensing and a versioned
secret/private/personal-data scan. Unknown/incompatible license, missing
attribution, unresolved finding, or forbidden redistribution fails closed;
paraphrase does not bypass provenance restrictions.

### Consequences

- Positive: common knowledge stays attributable and safely reusable.
- Negative: promotion is deliberately slower than detection.
- Neutral: LLM generalization is advisory, never publication authority.

## ADR-SPKC-013: Compile Harness Skills From One Canonical Source

### Status

Accepted

### Context

Hand-maintained Claude, Codex, Gemini, and agent copies drift semantically.

### Decision

Store one canonical skill/rule source plus harness adapters. Deterministically
generate supported surfaces with source UID, generator version, and content
hash; stale output fails verification and generated files are not hand-edited.
Every artifact has exactly one instruction-trust value: `untrusted_data`,
`reviewed_reference`, or `executable_policy`. Only an artifact explicitly
registered by the policy registry as `executable_policy` may activate
instructions. `reviewed_reference` remains data/reference despite human review
and cannot route tools, grant capabilities, or alter policy. Promotion,
generation, path placement, signature, or provenance alone cannot change the
trust value; registry authorization is mandatory and auditable.

### Consequences

- Positive: shared semantics have one reviewable owner.
- Negative: generator compatibility becomes release-critical.
- Neutral: harness-specific adapters may add syntax but not alter core meaning.

## ADR-SPKC-014: Target MCP 2026 With Explicit Legacy Compatibility

### Status

Accepted

### Context

Current SPipe clients use legacy stdio while the target protocol provides a
stateless core and cache-aware list/read behavior.

### Decision

Keep the knowledge core transport-neutral. Negotiate the highest mutually
supported allowlisted version, retain legacy stdio compatibility, and target
MCP `2026-07-28` for stateless transport. Unknown versions and unimplemented
capabilities fail closed. Pagination and cache hints bind a projection identity
and authorization-filtered snapshot.
HTTP requires TLS outside explicit local development and validated scoped bearer
tokens or mTLS. Responses default to `private, no-store` and `Vary:
Authorization`; public immutable caching requires snapshot/content ETag. CORS
denies by default, logs redact credentials, and mutations use anti-replay IDs.

### Consequences

- Positive: migration does not strand installed clients.
- Negative: conformance and equivalence tests cover multiple protocol adapters.
- Neutral: transport sessions never own knowledge truth.

## ADR-SPKC-015: Defer OS-Level Virtual Filesystems

### Status

Accepted

### Context

FUSE and ProjFS add platform-specific mount lifecycle, invalidation, permission,
and write-through risks. MCP, tools, materialization, and editor adapters cover
the expected initial clients.

### Decision

Defer FUSE/ProjFS until measured client evidence proves the initial surfaces
insufficient. Any later adapter must remain read-only and use the same
projection and authorization ports.

### Consequences

- Positive: initial delivery avoids unnecessary platform and security scope.
- Negative: a client requiring an OS mount is not supported initially.
- Neutral: deferral does not change the virtual URI or projection model.

## Cross-Cutting Snapshot Identity

All ADRs use one `SnapshotId` external form: `spks1-` plus lowercase SHA-256 of
canonical SDN bytes for the exact ordered tuple
`snapshot_v1(project_uid, worktree_uid, revision_id, base_generation_hash,
overlay_generation_hash, schema_version, parser_version, analyzer_version,
provider_contract_version, policy_hash)`. Text is UTF-8 NFC, integers are
unsigned decimal, the clean overlay is exactly 64 zero hex characters, no field
is omitted, and no extra field is admitted. `revision_id` is the resolved
committed/base revision, not floating or a dirty-overlay label.
Semantic model identity keys provider/query evidence rather than graph snapshot
identity. Local generation numbers and timestamps are forbidden substitutes.

## Cross-Cutting Interface Vocabulary

Internal injection uses `LexicalSearchPort`, `SemanticSearchPort`,
`SymbolIndexPort`, and `ProjectionPort` for the shared provider boundary.
They map respectively to `SearchProvider` (both search ports),
`SourceSymbolProvider`, and `ProjectionProvider`. SPipe retains projection truth
and authorization. Identity, graph, storage, authorization, transaction,
safe-filesystem, and snapshot-publication authority cannot be externalized; no `StorageProvider` is
declared by this shared contract. `RefactorPlan` is the only mutation-plan name;
`TransactionPlan` is forbidden. `DiagnosticRecord` is the only public diagnostic
record name. `KnowledgeDelta` is the atomic child-to-parent envelope binding one
base snapshot and coherent `ArtifactDelta`, `GraphDelta`, `IndexDelta`, and
`DiagnosticRecord` collections; constituents cannot publish independently.

`RefactorSafeFilesystemPort` is internal and callable only by `RefactorService`
with non-copyable `SafeFilesystem.Refactor` issued by `AuthorizationPort` for one
transaction/project/worktree/snapshot/path-operation set. Its frozen API is
`open_project_root`, `read_regular`, `capture_metadata`, `stage_regular`,
`create_directory`, `atomic_replace`, `atomic_move`, `restore_metadata`,
`remove_empty_directory`, `sync_file`, and `sync_directory`. All paths are
descriptor-relative and no-follow. Removal moves content to the transaction
rollback area; no arbitrary path, raw write, recursive delete, or symlink-
following mutation exists.

`SafeFilesystem.Materializer` is issued only to the authorized
`ProjectionService` adapter and is never exposed to a provider. The adapter
derives non-authorizing `MaterializerRootGrant`, containing only opaque root,
normalized path/operation bounds, projection/snapshot, budget, and expiry—no
principal, policy, token, credential, or authorization. The provider-facing
`MaterializerSafeFilesystemPort` frozen API is
`open_view_root(MaterializerRootGrant)`, `stage_generated`, `create_generated_directory`,
`atomic_replace_generated`, `remove_generated`, `sync_generated_file`, and
`sync_generated_directory`. `SafeFilesystem.Refactor` and
`SafeFilesystem.Materializer` are least-authority/non-implying;
`MaterializerRootGrant` is not a capability and cannot authorize another root.

## Cross-Cutting Performance Measurement

NFR-SPKC-014 means median warm elapsed wall-clock for one-artifact incremental update
versus full rebuild on the qualified Wave-0 fixture. Use the same machine/power
profile, provider, configuration, and cache state, one untimed warmup, and at
least 20 alternating samples. Exclude setup/provider launch/cache priming from
both; include parse, graph, index, and publication in both. Wave 1 blocks if the
recorded no-op `spipe doctor` or any legacy compatibility command regresses more
than 10% warm P95 from its Wave-0 baseline.
P95 elapsed time, CPU time, and maximum RSS are diagnostics, not substitutes for
the normative median 20x ratio. The Wave-1 P95 gate remains independently
normative under NFR-SPKC-016.

Absolute latency values in the architecture are Wave-0 qualification candidates
until the hardware/corpus/provider profile is locked; they are not release
budgets before that decision. Wave 4 includes DBFS compatibility migration
behind its supported facade and parity proof against common exact-length,
fixed-point BM25; its approximate scorer is not a second authority.

## Cross-Cutting Security Ordering

The following ordering constrains all records above:

1. Define assets, principals, trust/visibility classes, attack surfaces, and
   misuse cases before enabling a transport, remote provider, or mutation API.
2. Resolve every operation against a pinned `workspace + project + revision +
   snapshot + visibility scope`; authorization and cache identity use the same
   tuple so a cached result cannot outlive or escape its authority.
3. Canonicalize/realpath registered roots and reject traversal, symlink/junction
   escape, cross-root operations, stale hashes, and ambiguous identity before
   content disclosure or mutation.
4. Keep reads, refactor application, and common publication as distinct
   capabilities. Deny wins at every intersection.
5. Treat repository content as untrusted data. It cannot become agent policy
   merely because a search result or virtual resource contains instructions.

Transport and mutation implementation cannot precede the executable threat
model and negative tests for path escape, cache-scope leakage, confused deputy,
cross-worktree disclosure, stale snapshot authorization, journal tampering,
provider response poisoning, and untrusted prompt content.

## ADR-SPKC-016 — Graph identity, delta, and publication contract

### Status

Accepted

**Decision:** The graph is a snapshot projection of canonical typed records.
Wave 3 uses `RQ-`, `NFR-`, `SS-`, `SY-`, `WS-`, and `WT-`; `R-` remains a
project relation. Existing schema-v1 `W-` workspace/worktree identities are
decoded by record type and migrated through tracked old-type-to-new-UID records;
new publications use only `WS-`/`WT-`. Alias and mount records remain
registry-owned and receive graph projections. `GraphDelta` owns disjoint,
before-hash-guarded node and edge changes. Graph roots hash canonical nodes and
edges. Publication stages immutable objects and performs writer-locked
`current.sdn` compare-and-swap; all reads use one store-issued, scope-bound,
revocable immutable pin. Strict accepted edges require a verified `D-`
authorization receipt binding the exact edge and policy.

**Rationale:** This removes UID collisions, gives requirement/scenario/symbol
trace endpoints canonical identity, makes clean and incremental graph roots
falsifiably equivalent, and prevents mixed-generation reads.

**Consequences:** Wave 3 must add canonical trace-node models and snapshot
publication lifecycle before graph extraction. Markerless candidates and
inferred edges remain non-authoritative. Endpoint/type/origin/provenance changes
create a new EdgeUid. `Behavior`, test-run, and result nodes remain Wave 7.
