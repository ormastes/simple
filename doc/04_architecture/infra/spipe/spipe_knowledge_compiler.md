<!-- codex-architecture -->
# SPipe Knowledge Compiler Architecture

**Status:** Accepted design baseline  
**Date:** 2026-08-25  
**Research:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`

## 1. Decision and Scope

SPipe compiles one lifecycle-first canonical document tree into an immutable,
typed knowledge snapshot. Feature, component, layer, project, status, matrix,
and trace trees are read-only projections. Artifact and section UIDs are
identity; keys, headings, paths, and generated URIs are mutable names.

The dependency-free SPipe implementation owns correctness. Simple may provide
faster search, symbol analysis, duplicate analysis, and persistence through
versioned ports, but provider availability cannot alter graph truth, identity,
authorization, or deterministic ordering.

This architecture covers the compiler core, storage and worktree isolation,
virtual views, MCP boundaries, search providers, refactoring transactions,
trace authority, rebalancing proposals, promotion proposals, security, and
performance. Physical FUSE/ProjFS mounts remain deferred adapters.

The normative focused extension
`spipe_knowledge_compiler_cooperative_streaming.md` owns provider raw-byte
transport, iterative JSON/SHA/Unicode analysis, cooperative deadline and
cancellation admission, portable process statistics, and the migration
gate from honest protocol-1.0 `cancel:false` to qualified `cancel:true`.

## 2. Architectural Invariants

1. There is exactly one canonical content copy and one immutable UID per
   conceptual artifact. A move does not create a new artifact.
2. A published `KnowledgeSnapshot` is immutable. A request observes one pinned
   generation and never mixes graph, index, alias, or projection generations.
3. The parent `KnowledgeCompiler` is the only snapshot publication authority.
   Child services return deltas or proposals; siblings never mutate each other.
4. `RefactorService` is the only canonical-file mutation authority. Analyzers,
   projections, rebalancers, and promotion analysis are read-only.
5. An accepted explicit or deterministic generated edge may satisfy strict
   trace policy. Inference never silently becomes compliance evidence.
6. A virtual path cannot select a host path. Resolution always proceeds through
   workspace, project, revision, artifact UID, and authorization.
7. Committed-revision segments may be shared; dirty worktree state, locks,
   journals, generated views, and authorization caches may not.
8. Provider fallback changes capability and latency, never observable ranking
   order on the shared lexical golden corpus.

## 3. MDSOC Structure

`KnowledgeCompiler` is a virtual capsule whose application layer owns startup,
incremental compilation, publication, and shutdown. Cross-cutting security,
metrics, cache policy, and tracing are feature transforms around stable ports.
Runtime-selectable search/source/storage implementations are adapters.

```text
KnowledgeCompiler (parent and publication authority)
├── WorkspaceRegistry      project, linkage, revision, trust
├── ParserService          Markdown, SDN, SSpec, source metadata -> deltas
├── IdentityService        UID/key/alias/section resolution
├── GraphService           typed nodes and edges
├── IndexService           exact, lexical, graph, optional semantic indexes
├── ProjectionService      read-only virtual resources
├── DiagnosticService      link, trace, security, balance diagnostics
├── RefactorService        sole canonical mutation authority
├── RebalanceService       proposal producer only
└── PromotionService       proposal producer only
```

Common owns contracts and immutable records. Adapters may depend on common;
common never imports an adapter. Sibling implementations communicate only via
ports or parent-applied deltas.

### 3.1 Stable ports

| Port | Responsibility |
|---|---|
| `WorkspacePort` | Resolve registered project/worktree/revision roots and trust |
| `ArtifactParserPort` | Parse bytes into deterministic artifact/section/edge deltas |
| `IdentityStorePort` | Resolve UID, semantic key, alias, canonical path, section UID |
| `GraphStorePort` | Apply/query versioned typed graph deltas |
| `LexicalSearchPort` | Fixed-point BM25, phrase, filters, explain, deterministic top-k |
| `SemanticSearchPort` | Optional candidates only, with model/version disclosure |
| `SymbolIndexPort` | Versioned language-specific symbols and references |
| `SnapshotStorePort` | Load/store immutable content-addressed generations |
| `ProjectionPort` | List/read bounded virtual resources from a pinned snapshot |
| `AuthorizationPort` | Deny-wins read/write/publish decisions |
| `TransactionJournalPort` | Durable transaction state, receipts, recovery |
| `RefactorSafeFilesystemPort` | Descriptor-relative canonical refactor mutations and durability |
| `MaterializerSafeFilesystemPort` | Descriptor-relative generated-view mutations and durability |
| `ClockPort` | Injectable time for TTL, staleness, and deterministic tests |

Ports return typed capability or error results. No fallback may claim a
capability it cannot provide exactly.

### 3.2 Internal-port and external-provider freeze

`*Port` names are internal dependency-injection contracts; `*Provider` names
are versioned external protocol roles. `LexicalSearchPort` and
`SemanticSearchPort` adapt `SearchProvider` capabilities; `SymbolIndexPort`
adapts `SourceSymbolProvider`; `ProjectionPort` adapts `ProjectionProvider` for
external delivery while SPipe retains projection truth and authorization.
Workspace, identity, graph, storage, authorization, transaction, safe-filesystem,
and snapshot-publication authority remain internal and cannot be delegated. No
`StorageProvider` is part of this shared contract.

### 3.3 Safe filesystem capability and API freeze

`AuthorizationPort.authorize_refactor(plan, principal, snapshot)` issues one
non-copyable `SafeFilesystem.Refactor` bound to transaction, project, worktree,
pinned snapshot, allowed canonical relative paths/operations, metadata policy,
and expiry. Only `RefactorService` may hold it. The exact
`RefactorSafeFilesystemPort` API is:

```text
open_project_root(capability) -> SafeRoot
read_regular(root, relative_path, expected_hash) -> bytes
capture_metadata(root, relative_path) -> FileMetadata
stage_regular(root, transaction_id, relative_path, bytes, FileMetadata) -> StagedFile
create_directory(root, relative_path, DirectoryMetadata) -> CreatedDirectory
atomic_replace(root, StagedFile, destination, expected_old_hash?) -> AppliedMutation
atomic_move(root, source, destination, expected_source_hash, expected_destination_hash?) -> AppliedMutation
restore_metadata(root, relative_path, FileMetadata) -> AppliedMutation
remove_empty_directory(root, relative_path, expected_metadata) -> AppliedMutation
sync_file(root, relative_path) -> DurabilityReceipt
sync_directory(root, relative_path) -> DurabilityReceipt
```

Paths are descriptor-relative and no-follow. There is no absolute-path, raw
write, recursive-delete, or symlink-following mutation. Content removal is an
atomic move into the transaction rollback area; cleanup follows commit receipt.

`AuthorizationPort.authorize_materializer(view, principal, snapshot)` separately
issues non-copyable `SafeFilesystem.Materializer`, bound to one worktree's view
root, projection/snapshot, generated relative paths, budget, and expiry. Only
the authorized `ProjectionService` adapter may hold it; it must never pass that
capability to a provider. The adapter validates the binding and derives a
sanitized, non-authorizing `MaterializerRootGrant` containing only opaque root
identity, normalized generated-path bounds, allowed operation set,
projection/snapshot binding, byte/count budget, and expiry. It contains no
principal, policy, token, credential, capability, or reusable authorization.
The provider sees only this operation/root-bound grant. The exact
`MaterializerSafeFilesystemPort` API is:

```text
open_view_root(grant: MaterializerRootGrant) -> SafeViewRoot
stage_generated(root, projection_uid, relative_path, bytes) -> StagedGeneratedFile
create_generated_directory(root, relative_path) -> CreatedDirectory
atomic_replace_generated(root, StagedGeneratedFile, destination) -> AppliedMutation
remove_generated(root, relative_path, expected_projection_uid) -> AppliedMutation
sync_generated_file(root, relative_path) -> DurabilityReceipt
sync_generated_directory(root, relative_path) -> DurabilityReceipt
```

Both ports are descriptor-relative and no-follow. `SafeFilesystem.Refactor` and
`SafeFilesystem.Materializer` are least-authority and non-implying: neither port
accepts the other capability, and neither canonical/rollback root namespace can
address a generated-view root or vice versa. `MaterializerRootGrant` is not a
third capability and cannot be exchanged at `AuthorizationPort`.

### 3.4 Common records

The frozen vocabulary is `WorkspaceId`, `ProjectId`, `WorktreeId`,
`RevisionId`, `ArtifactUid`, `SectionUid`, `EdgeUid`, `SnapshotId`,
`ContentHash`, `KnowledgeDelta`, `ArtifactDelta`, `GraphDelta`, `IndexDelta`, `QueryRequest`,
`QueryResult`, `QueryExplanation`, `RefactorPlan`, `TransactionReceipt`,
`RebalanceProposal`, `PromotionCandidate`, and `DiagnosticRecord`.

`KnowledgeDelta` is the sole child-to-parent compilation envelope. It binds one
base snapshot and coherent `ArtifactDelta`, `GraphDelta`, `IndexDelta`, and
`DiagnosticRecord` collections; constituent deltas cannot publish separately.
`RefactorPlan` is the sole mutation-plan name. `TransactionPlan` and bare
`Diagnostic` are non-canonical at public boundaries.

`SnapshotId` is the digest of one canonical ordered tuple, serialized as
canonical SDN with UTF-8 NFC text, decimal unsigned integers, no omitted or
additional fields, and this exact order:

```text
snapshot_v1(
  project_uid,
  worktree_uid,
  revision_id,
  base_generation_hash,
  overlay_generation_hash,
  schema_version,
  parser_version,
  analyzer_version,
  provider_contract_version,
  policy_hash
)
```

`revision_id` is the resolved committed/base content revision, never a floating
ref or dirty-overlay label. The clean overlay is exactly 64 lowercase zero hex
characters. `policy_hash` binds
visibility, authorization, trace, search-field/weight, and projection policy;
optional semantic model identity belongs in provider-generation/query evidence,
not `SnapshotId`, because it cannot change canonical graph truth. The external
form is `spks1-` plus lowercase hex SHA-256 of the canonical tuple bytes. It is
not a timestamp and no implementation may substitute a local generation number.

## 4. Identity, Sections, and Edge Direction

### 4.1 Dual identity

Opaque UIDs are immutable and never reused. Semantic keys are human-readable,
renameable, and retained as aliases. Canonical path is a location. Content hash
detects a version. A UID collision is fatal; ambiguous aliases fail resolution.

### 4.2 Section-ID policy

A stable marker immediately follows a managed Markdown heading:

```markdown
## Incremental Index Maintenance
<!-- spipe:section uid=S-... key=design.search.incremental-maintenance -->
```

Markers are required for sections that are externally referenced, trace
targets, transaction targets, or strict-profile evidence. They are optional for
unreferenced prose. The compiler may propose marker injection but never changes
a canonical file during read-only indexing. Heading rename preserves the UID
and records the former heading slug as an alias. Moving a marked section between
artifacts preserves its section UID only through an approved transaction that
records old and new parentage. Duplicate section UIDs are fatal.

### 4.3 Canonical edge direction

Edges use active-verb direction `subject -> object`; inverse labels are query
views only and are never stored independently.

### 4.4 Wave 3 graph identity and node ownership

The graph is a projection of canonical records, never a second identity owner.
`GraphNode` contains `uid`, `node_kind`, nullable `project_uid`, `revision_id`,
`record_type`, `record_hash`, `visibility`, `trust_scope`, and `status`.
Wave 3 admits `Workspace`, `Worktree`, `Project`, `ProjectRelation`, `Mount`,
`Alias`, `Artifact`, `Section`,
`Requirement`, `NonFunctionalRequirement`, `SSpecScenario`, `SourceSymbol`,
`UnitTest`, `IntegrationTest`, `SystemTest`, `Feature`, `Component`, `Layer`,
and `Tag`. Alias and mount content remains owned by registry records; graph
nodes are immutable projections of those records solely so `aliases` and
`mounted_as` have typed endpoints. Alias projection UIDs use `AL-` plus the
first 26 characters of uppercase Crockford base32 (alphabet
`0123456789ABCDEFGHJKMNPQRSTVWXYZ`, no padding, digest bits consumed
most-significant-bit first) of SHA-256 over UTF-8
`spipe-alias-projection-v1\0` followed by canonical JSON
`[workspace_uid,project_uid-or-null,kind,alias,canonical_target_uid]`; mount
projection UIDs use the same encoding of SHA-256 over UTF-8
`spipe-mount-projection-v1\0` followed by
`[workspace_uid,relation_uid,linkage,mount,canonical_target_uid]`. Workspace
nodes and workspace-scoped aliases set `project_uid=null`; hash collisions are
fatal. `Behavior`, `TestRun`, `TestResult`,
`Claim`, and promotion nodes enter only with their later canonical models.

New canonical namespaces are `RQ-` for requirements, `NFR-` for non-functional
requirements, `SS-` for scenarios, `SY-` for source symbols, `WS-` for
workspaces, and `WT-` for new worktree identities. Schema-v1 `W-` values are
decoded by record type (`workspace` or `worktree`) and never compared across
types. Schema v2 writes only `WS-`/`WT-` and records a tracked
`IdentityMigrationRecord(old_uid, old_record_type, new_uid, migrated_in_snapshot_uid)`.
The new UID is derived, not randomly allocated: `WS-` or `WT-` plus the first
26 Crockford characters under the encoding above of SHA-256 over UTF-8
`spipe-identity-migration-v1\0`, the target record type, a NUL byte, and the
legacy `W-` UID bytes. Mutable record content is excluded. Identical
`(old_record_type,old_uid)` therefore produces one identity across snapshots;
a derived-UID collision is fatal. Existing
immutable snapshots remain byte-readable and are never rewritten. Snapshot
and projection validators accept legacy `W-` only when `schema_version=1` and
emit v2 identities for new publications. `R-` remains exclusively
`ProjectRelation`. Human labels such as `REQ-SPKC-003` are display aliases;
their normalized semantic keys are lowercase (`req-spkc-003`), never UIDs.
Markerless requirement sections, scenarios, or symbols are candidates and
cannot become canonical graph endpoints or strict evidence.

### 4.5 Graph provenance, deltas, and publication

Every stored edge adds immutable provenance `(project_uid, worktree_uid,
revision_id, input_snapshot_uid, source_uid?, source_location?, decision_uid)` and
optional verified authority `(explicit_review|trusted_generator, receipt_uid,
policy_hash, policy_version)`. `receipt_uid` is the `D-` UID of an Ed25519
authorization receipt verified by the internal `AuthorizationPort`; the receipt
binds exact edge UID and acceptance-subject hash, endpoints, origin, status, project/worktree,
input snapshot, policy, issuer key, expiry, and capability
`trace.accept.explicit` or `trace.accept.generated`. Revoked/expired/mismatched
receipts fail closed. `decision_uid` is nullable for non-authoritative edges and
must equal the verified receipt UID for strict evidence. Strict evidence requires canonical endpoints,
`accepted` status, and verified explicit-review or deterministic-generator
authority. Inferred origins remain candidates even if reviewed; they never
satisfy strict or mission-critical policy.

The acceptance-subject hash excludes `status`, `decision_uid`, and `authority`
to avoid circular receipt hashing; it includes every immutable identity,
endpoint, origin, provenance-source, and generator field. The stored edge hash
includes the completed receipt reference.

`GraphDelta` owns both node and edge changes:

```text
GraphDelta {
  base_snapshot_uid, base_graph_root,
  nodes: {added, updated[{before_hash,node}], removed[{uid,before_hash}]},
  edges: {added, updated[{before_hash,edge}], removed[{uid,before_hash}]}
}
```

The nested `base_snapshot_uid` must equal the enclosing `KnowledgeDelta` base.
`before_hash` is SHA-256 of the UTF-8 canonical-JSON bytes of the complete
stored `GraphNode` or `EdgeRecord` wrapper. Each operation set is UID-disjoint and canonically ordered. Edge endpoint,
type, origin, or provenance changes require a new `EdgeUid`; an update may only
change status or append verified authority. Apply rejects stale bases and
before-hash mismatches. The root is SHA-256 of UTF-8 canonical JSON with the
exact shape `{schema:1,nodes:[...],edges:[...]}`, nodes sorted by UID and edges
sorted by `(from_uid, edge_type, to_uid, edge_uid)`, with no omitted/additional
fields. A delta applies only to its base. A byte-identical replay identified by
delta hash returns `already_applied` and the recorded output root. `delta_hash`
is SHA-256 over `spipe-graph-delta-v1\0` plus canonical JSON of the complete
delta. Publication retains
`{delta_hash,base_snapshot_uid,base_graph_root,output_snapshot_uid,output_graph_root}`
for the output snapshot retention lifetime; any other
post-publication replay is a stale-base error.

`GraphStorePort` provides `build`, `apply`, `node`, `edge`, bounded `edges`,
bounded `traverse`, and paginated `trace_matrix`. Default/hard limits are:
depth `8/32`, visited nodes `2,000/20,000`, returned edges `10,000/50,000`,
work units `50,000/500,000`, edge page `100/1,000`, and trace-matrix rows
`100/1,000`. Exhaustion returns a deterministic partial result with
`exhausted=true`, `reason`, consumed counters, and a snapshot-bound cursor; it
never silently truncates. Every read consumes an authorized
`SnapshotPin`; cursors bind snapshot, filter, page limit, and authorization
scope. `SnapshotPin` is an unforgeable store-issued branded handle (or an
authenticated opaque token across a process boundary) binding snapshot UID,
graph root, authorization-scope digest, policy version, issuance/expiry, and
liveness generation. Released/expired/wrong-store pins fail before lookup.
Snapshot storage stages objects and manifest first, then publishes
`current.sdn` with writer-lock-protected compare-and-swap. Readers acquire and
release immutable pins. One CAS conflict permits one compiler rebase; a second
returns `SPK901` without retry loops.

| Stored edge | Direction and meaning |
|---|---|
| `contains` | container -> member |
| `classifies` | artifact -> feature/component/layer/tag |
| `evidence_for` | research evidence/claim -> supported node |
| `derives` | derived node -> source node |
| `satisfies` | design/implementation -> requirement |
| `realizes` | design/component -> architecture decision |
| `schedules` | plan task -> scheduled work node |
| `specifies` | SSpec scenario -> requirement/behavior |
| `implements` | source symbol -> requirement/design/spec |
| `verifies` | test/test result -> requirement/spec/source behavior |
| `covers` | test -> source symbol/module |
| `produces` | run -> result/report |
| `links_to` | referring node -> target node |
| `aliases` | alias node -> authoritative node |
| `supersedes` | replacement -> replaced node |
| `extends` | project/family node -> common base node |
| `promoted_from` | common unit -> contributing project unit |
| `depends_on` | dependent project/artifact -> dependency |
| `mounted_as` | project relation -> concrete mount record |

The table is the full-system edge vocabulary. Wave 3 enables every row except
`produces` and `promoted_from`; those fail closed until later waves publish the
canonical run/result and promotion node schemas.

### 4.6 Trace authority

Authority and acceptance are independent fields.

| Origin | May be accepted automatically? | Advisory gate | Standard gate | Strict/mission-critical gate |
|---|---:|---:|---:|---:|
| `explicit` | no; validation creates a proposal | candidate or verified accepted | verified accepted | receipt-bound accepted |
| `generated` | no; deterministic generation creates a proposal | candidate or verified accepted | verified accepted | receipt-bound accepted |
| `structural` | no; proposal until reviewed | candidate | no | no |
| `lexical_inference` | no | candidate | no | no |
| `semantic_inference` | no | candidate | no | no |
| `llm_inference` | no | candidate | no | no |

Only `status=accepted` edges count. `generated` evidence records generator ID,
version, input snapshot, and rule. Mission-critical profiles additionally
require immutable result evidence and configured signature/trust validation.
Existing `TRC231`/`TRC232` are compatibility projections from authoritative
UID relationships, not a second trace store.

## 5. Snapshot and Worktree Model

### 5.1 Composition

```text
shared immutable committed-revision base segments
  + private per-worktree dirty overlay
  + private in-memory current delta
  = request-pinned KnowledgeSnapshot
```

Snapshot identity is exactly the `snapshot_v1` tuple defined in Section 3.4.
Repository identity is resolved into the registered project/worktree UIDs before
serialization. Optional semantic model/revision is query/provider evidence and
may key its own cache, but does not alter canonical snapshot identity. A
content-addressed object may be reused only when all applicable tuple fields
match.

### 5.2 Isolation

Committed objects are immutable and may be shared by hash. Every worktree owns
its overlay directory, writer lock, journal namespace, materialized view,
watcher cursor, and private cache partition. A worktree ID is derived from
canonical Git common-dir identity plus canonical worktree Git-dir identity,
not merely its filesystem path. Cross-worktree queries require an explicit
capability and identify the target snapshot; dirty data never enters another
worktree implicitly.

Linked projects are namespaced by project UID and pinned/floating revision
policy. Missing or revision-mismatched projects yield diagnostics, never local
name-based fallback.

### 5.3 Publication and invalidation

Children build deterministic deltas against one base generation. The parent
validates identities, edge targets, index parity metadata, and projection
collisions, then atomically swaps one snapshot manifest. Readers holding the old
manifest remain valid. Events invalidate only affected artifact, reverse-edge,
index posting, directory projection, and diagnostics entries. Parser/schema/
analyzer version changes invalidate their complete dependent segment. Full-tree
scans occur only for explicit build/audit/recovery operations.

## 6. Transactional Refactoring

### 6.1 State machine

```text
Planned -> Prepared -> Applying -> Validating -> Committed
                     \-> RollingBack -> RolledBack
Prepared/Applying/Validating --startup recovery--> RecoveryRequired
RecoveryRequired -> Applying | RollingBack
```

Planning resolves UIDs and reverse references against a pinned snapshot,
calculates exact canonical targets, authorization, collisions, and old/new
hashes. `Prepared` means the complete plan, original bytes or recoverable object
references, intended bytes, permissions, and directory operations are durably
journaled before the first canonical mutation.

### 6.2 Durability contract

For each transaction:

1. Write journal and staged content beneath a private same-filesystem staging
   directory; flush file contents and journal.
2. Flush the staging directory before setting `Prepared`.
3. Verify source hashes and authorization immediately before each mutation.
4. Use atomic replace/rename where supported; record every applied operation.
5. Flush changed files and parent directories according to configured normal or
   critical durability policy.
6. Parse and validate the proposed snapshot, links, strict trace, and aliases.
7. Atomically publish the new snapshot manifest and durable `Committed` receipt.
8. Only then garbage-collect staging material.

Normal mode guarantees recoverability after process failure. Critical mode also
requires filesystem durability barriers and fails closed where the platform
cannot prove them. A failed validation rolls back to journaled original hashes.
Startup recovery never guesses: hash states select resume, rollback, or explicit
`RecoveryRequired`. Virtual-view writes are rejected before journaling.

The append-only journal binds each record to transaction ID, sequence,
previous-record digest, plan digest, actor/capability, snapshot ID, and operation
digest. Recovery rejects gaps, reordered/duplicate records, invalid transitions,
or digest mismatch. Replay is idempotent and classifies each target as original,
intended, or foreign; foreign state fails to `RecoveryRequired` without
overwriting user work. Rollback preserves bytes, file type, mode/ACL, supported
owner/timestamps/xattrs, symlink target without following it, and original
directory membership. Planning rejects metadata the platform cannot preserve.
Fault injection covers every journal/stage/metadata write and flush, rename,
directory flush, validation, manifest publish, and receipt publish boundary.

## 7. Virtual Projections and MCP

The authoritative URI space is `spipe://workspace/...` and
`spipe://project/.../artifact/{uid}`. Directory reads are bounded generated
indexes; pages contain at most 100 entries, 200 Markdown lines, and an
approximately 6,000-token payload. Collision suffixes use a deterministic short
UID and every generated entry declares canonical UID/path.

Every virtual entry/page has `ProjectionUid = spkp1-<lowercase sha256>`, where
the digest is SHA-256 of canonical SDN bytes for exactly
`projection_v1(workspace_uid, snapshot_id, view_kind,
normalized_logical_path, normalized_parameters_hash,
effective_auth_scope_hash, page_start_key)`. Text follows SnapshotId's UTF-8 NFC
rules and no field is omitted or added. `page_start_key` is empty only for the
first page. Projection/cache identity therefore binds effective authorization
and normalized parameters, not merely the requested URI.

Resources and tools expose equivalent list/read/search/resolve/trace/
diagnostics behavior. Mutation tools default to plan-only and require a
separate apply capability/token.

`MaterializerSafeFilesystemPort` traverses from a pre-opened view-root descriptor with
descriptor-relative no-follow operations, verifies each opened object, and
keeps staging/replace beneath the held parent descriptor. String-prefix checks
and check-then-open realpaths are not security boundaries; platforms without
equivalent handle-relative safety fail closed. URI parsing decodes once and
rejects encoded separators, NUL, dot segments, drive-relative/UNC/device forms,
backslash ambiguity, and case-fold collisions before filesystem mapping.

### 7.1 Protocol negotiation

The protocol-neutral core supports legacy stdio plus target MCP `2026-07-28`.
Initialization selects the highest mutually supported protocol from a declared
allowlist; unknown versions fail with `unsupported_protocol`, never optimistic
downgrade. Capabilities are emitted only for implemented operations. Ordering,
pagination cursors, and serialization are deterministic within a pinned
snapshot. Cache hints include snapshot ID, TTL, and scope; private or
authorization-filtered results never receive public scope. Transport sessions
hold no graph truth and stateless requests carry or resolve an authorized
workspace/snapshot context.

HTTP requires TLS except in an explicit local-development profile and uses
validated scoped bearer tokens or mTLS. Credentials bind principal, audience,
expiry, workspace/project, and operations. Responses default to `Cache-Control:
private, no-store` plus `Vary: Authorization`; public caching requires proven
public immutable content and snapshot/content ETag. CORS denies by default,
logs redact credentials, and mutations require an authenticated anti-replay ID.

## 8. Search and Provider Boundary

For `resolve`, exact UID/key/alias lookup is a dominance short-circuit: one
authorized unambiguous result returns directly and never enters RRF; ambiguity
is an error. For general `search`, an authorized unambiguous exact identity hit
is pinned at rank 1 and deduplicated while lexical, accepted graph-neighborhood,
and optional semantic lists are fused for remaining results. Without an exact
hit, all results come from fusion. Explanations identify exact pinning or ranks,
trace distance, filters, staleness, and provider capability.

### 8.1 Provider contract and parity

SPipe owns query normalization, exact-resolution dominance, field schema/weights,
fixed-point arithmetic contract, candidate-source orchestration, graph traversal,
RRF, post-fusion boosts, tie-breaking by document UID, filtering semantics, and
golden fixtures. Providers return only a named ranked candidate source with
per-candidate source score/rank and explanation; they do not fuse lists, apply
graph proximity, or compute final rank. Providers negotiate protocol major/
minor, analyzer/scorer versions, capabilities, maximum limits, and implementation
digest. A required-major or semantic mismatch rejects the provider.

The dependency-free JavaScript provider is normative. Simple-native and server
providers must return identical normalized tokens, document statistics,
fixed-point lexical scores, ordering, phrase behavior, deletion behavior, and
explanations for golden and randomized parity corpora. WAND/Block-Max WAND must
equal exhaustive top-k. Optional ANN may add candidates but cannot satisfy
strict trace or change lexical parity. Provider crash/timeout degrades to the
fallback for supported operations and emits a diagnostic.

Use an in-process adapter or long-lived provider process/session. Per-request
process launch is forbidden on hot paths.

Executable providers require a configured canonical path, approved digest or
signature, safe ownership/permissions, argv/env allowlists, fixed working
directory, shell-free launch, and resource/deadline/output limits. Responses
are untrusted: validate framing, schema, bounds, UTF-8/numbers, snapshot/query
binding, document-ID membership, ordering, and explanation consistency before
use or caching. Malformed, replayed, cross-snapshot, or extra-document responses
reject the provider generation and cannot poison persistent caches.

Protocol 1.0 separates transport evidence from semantic provider errors. A
payload-free local `TransportDiagnosticV1` records `invalid_utf8` or
`frame_too_large`; before a complete typed envelope is host-bound, either class
closes the transport silently and cannot fabricate a `ProviderResponseV1`.
Only an applicable bound operation may carry a `ProviderErrorV1`. Its semantic
deadline is 1..30,000 milliseconds inclusive and starts when the decoder
accepts the first frame-header byte, not when parsing or dispatch completes.
The focused `spipe_knowledge_compiler_cooperative_streaming.md` architecture
owns the byte-stream, diagnostic, deadline, and commit-admission mechanics;
durable provider transactions remain the semantic mutation linearization
authority.

### 8.2 Accepted graph-candidate authority and continuation

Graph search consumes an already authorization-filtered, digest-bound graph
snapshot. A fixed-count metadata-free node-authorization pass rechecks every
declared node under the current receipt before traversal; it is a TOCTOU guard,
not a filter, and any denial invalidates the snapshot without identifying the
node. Only schema-v2 accepted explicit/generated edges with matching provenance,
policy, authority kind, decision receipt, and verified receipt may contribute.
Proposed, inferred, structural, stale, rejected, superseded, legacy, malformed,
or unverifiable edges never become search evidence.

The standalone traversal is deterministic both-direction BFS with these exact
v1 limits: depth `3`; `sourceK` `1..1000` (default `1000`); page work
`1..50,000` (default `50,000`); configurable total work `1..500,000`;
authorized nodes `20,000`; authorized edges `50,000`; roots `1001`
(one exact plus 1,000 lexical); and document IDs at most 512 UTF-8 bytes. No
path repeats a node or edge. Cycles are legal. The generator keeps the best path
per `(nodeUid, distance)` and replaces/re-expands a same-distance state when its
tuple improves. The exact ascending comparison tuple is:

```text
distance,
seedTier,                 # exact=0, lexical=1
seedRank,                 # exact=0, lexical=sourceRank
generatedEdgeCount,
-bottleneckConfidenceMilli,
edgeUidSequence unsigned-UTF-8 lexicographic,
directionSequence,       # out < in
nodeUidSequence unsigned-UTF-8 lexicographic
```

Final candidates sort by that tuple and then artifact UID by unsigned UTF-8.
Only authorized Artifact nodes are emitted, roots are excluded, and `sourceK`
is applied only after exhaustive bounded traversal. Hitting a hard bound fails
closed rather than returning a partial source.

Budget continuation uses a single-use, factory-branded, deeply frozen,
null-prototype in-process object with no enumerable state. A factory-local
`WeakMap` binds the normalized request (excluding budget/cursor), exact immutable
snapshot and digest, frontier, best-path tables, counters, and consumed bit.
Continuation atomically consumes the old state before work and emits a new
handle only if still partial. It never reopens the snapshot or repeats authority
calls. A copied, reconstructed, cross-factory, serialized, or replayed cursor is
invalid. Partial success is exactly `{status:'partial', contractVersion, cursor,
counters}` with no candidates/source/evidence/digests. Total-cap failure destroys
the state. Only frontier exhaustion yields a complete digest-bound graph source.
All retained collections are bounded by the limits above; abandoned cursor keys
and their WeakMap state are garbage-collection eligible. The handle has no clock,
randomness, MAC, expiry, cross-process portability, or restart guarantee.

The authorized snapshot is already filtered before it crosses the port, so
hidden nodes/edges cannot affect counts, caps, work, ordering, errors, cursor
state, or digests. The current-operation recheck calls `authorizeNode` exactly
once for every declared canonical node, in canonical UID order, with only
`{pin,nodeUid,nodeKind}`. It records all failures and completes the fixed call
count rather than exiting early; any denial, malformed decision, or exception
collapses to generic `snapshot_unavailable`. Edge receipt verification binds
edge UID/type/endpoints/origin, receipt/authority kind, graph snapshot/root,
scope, search receipt, and exact policy hash/version. No port error exposes a
UID, count, position, or hidden existence.

Accepted-edge evidence is losslessly represented as ordered
`{edgeUid, authorityReceiptUid}` pairs. Independently unique edge and receipt
arrays are derived views, because one decision receipt may authorize multiple
edges. A reranker contract that assumes an injective edge-to-receipt mapping
cannot consume the general graph source; pair-based reranker evidence is a
prerequisite for integrated graph boosting.

## 9. Rebalancing and Promotion Boundaries

Rebalancing consumes a snapshot and returns a deterministic proposal. Fixed
lifecycle roots, trust/project boundaries, generated SSpec/manual mirrors,
explicit protected bundles, and explicitly configured sidecars form hard
must-link/cannot-link constraints. Trace relations are weighted edges by
default, not must-links: making every trace chain a must-link would collapse
large features. A strict profile may must-link a requirement to its sole
irreplaceable verification artifact only when policy explicitly requests
co-location. Physical changes always pass through `RefactorService`.

Promotion similarly emits candidates with provenance, conflict analysis,
visibility/trust checks, and consuming-project validation requirements. Only a
separate publish capability may create common knowledge. LLM classification and
semantic similarity remain advisory.

Promotion requires a versioned secret/private/personal-data scan and explicit
license/provenance compatibility for every source. Unknown/incompatible license,
missing attribution, unresolved findings, or forbidden redistribution fails
closed. Paraphrase cannot launder restricted text; the receipt binds source
hashes, licenses, scan evidence, reviewer, and consuming-project validation.

## 10. Security Architecture

1. Canonicalize and realpath registered roots and targets. Reject `..`, encoded
   traversal, absolute injection, symlink/junction escape, device paths, and
   cross-root rename before reads or writes.
2. Authorize the intersection of principal, workspace, project, revision,
   artifact visibility, fields, and operation. Deny wins.
3. Treat repository content as untrusted data. Only approved rule/skill scopes
   may influence agent policy; retrieved instructions carry trust metadata.
4. Views are read-only. `refactor.apply` and `knowledge.publish` are distinct
   capabilities with auditable receipts.
5. Cache keys include authorization/visibility scope. Secret/private artifacts
   cannot enter public MCP caches, logs, embeddings, or explanations.
6. Remote semantic providers require explicit project policy and an allowlist;
   local-only/excluded paths remain local. Credentials are never indexed.
7. File watching is diagnostic, not authority. TOCTOU is controlled by open/
   hash preconditions immediately before mutation and post-write validation.

Prompt isolation is structural: retrieved artifacts are quoted data carrying
UID, trust, visibility, and boundaries; they are never concatenated into policy
or tool schemas. Instructions in artifact bodies cannot route tools, request
capabilities, approve mutations/edges, widen scope, or suppress diagnostics.
Generated summaries remain untrusted until authorized skill/rule promotion.

## 11. Startup, Hot Paths, Cache, and Observability

### 11.1 Startup path

Startup loads configuration and project registry, validates roots, recovers
unfinished journals, loads only snapshot manifests/alias tables, and opens
indexes lazily. It does not parse the full tree or start optional providers
until their capability is needed. A background warmup may not block basic
list/read/resolve.

### 11.2 Hot request paths

List/read/resolve/search/trace pin one snapshot, authorize once at the narrowest
safe scope, read immutable objects/index segments, and return bounded output.
They perform no full-tree scan, canonical write, repeated file reread, retry
sleep, or per-request subprocess. Cache misses schedule or perform bounded
single-artifact work.

### 11.3 Cache strategy

Immutable parsed objects and committed index segments are content-addressed.
Projection pages are keyed by snapshot/view/path/page/authorization scope.
Negative resolution caches have short TTLs and are invalidated by alias or
project-registry changes. Dirty-overlay caches are private to a worktree.

### 11.4 Targets and evidence

Wave 0 records hardware/corpus baselines and locks the performance profile. The
following absolute latency values are qualification candidates until that
profile is accepted; they are not release budgets before profile lock:

| Measure | Target |
|---|---:|
| Warm CLI/MCP startup to basic resolve | P95 <= 250 ms |
| Warm exact resolve/read | P95 <= 20 ms |
| Warm lexical search at 50k artifacts | P95 <= 100 ms |
| Warm list page | P95 <= 50 ms |
| One-document graph/index update | P95 <= 100 ms diagnostic; median warm elapsed wall-clock >=20x lower than full rebuild |
| Virtual regeneration | unchanged generated files rewritten: 0 |
| Provider parity | 100% ordering/score/explanation parity on required corpus |
| Wave-1 no-op `spipe doctor` and compatibility commands | <=10% warm P95 regression from Wave-0 baseline |

If baseline evidence makes an absolute target infeasible, requirements may
revise it explicitly; implementation may not silently weaken it. Counters and
timings cover startup phases, snapshot pins, parse/index deltas, object and
projection cache hit/miss, provider calls/fallbacks, query candidate counts,
journal recovery, authorization rejects, stale results, and generated rewrites.

NFR-SPKC-014's normative 20x comparison is median warm elapsed wall-clock on the qualified Wave-0
fixture: same machine/power profile, provider, configuration, and cache state;
one untimed warmup; at least 20 alternating incremental/full samples; compare
medians. Exclude setup, provider launch, and cache priming from both, while including
parse, graph, index, and publication work. Wave 1 separately runs the recorded
no-op `spipe doctor` and legacy compatibility corpus under that harness; any
command above 10% P95 regression blocks the wave unless the NFR is revised.
P95 elapsed time, CPU time, and maximum RSS remain required diagnostics but do
not replace the normative median ratio.

Wave 4 includes DBFS compatibility migration: preserve its supported public
facade while routing exact document lengths, corpus statistics, fixed-point
BM25, update/delete behavior, and explanations through the common contract.
Golden fixtures must prove compatibility; the former approximate scorer cannot
remain a second scoring authority.

## 12. Failure Model

Stable failures distinguish invalid/ambiguous identity, stale snapshot/hash,
unsupported protocol/provider capability, provider semantic mismatch, project
revision unavailable, authorization denied, unsafe path, view read-only,
transaction conflict, durability unavailable, recovery required, graph/trace
invalid, projection collision, and budget exceeded. Partial results explicitly
name omitted optional capabilities; they cannot be reported as strict PASS.

## 13. Verification Obligations

- Clean rebuild equals every equivalent incremental update sequence.
- Concurrent worktrees cannot observe or mutate each other's dirty overlays,
  journals, locks, views, or private caches.
- Fault injection at every transaction state leaves old or new valid state, or
  a fail-closed recoverable journal.
- Symlink/junction, encoded traversal, cache-scope, and cross-revision attacks
  fail before content disclosure or mutation.
- Legacy stdio and MCP 2026 produce equivalent core results.
- JS and Simple providers satisfy lexical parity; exhaustive and accelerated
  top-k agree exactly.
- Strict trace ignores inferred-only edges and survives approved moves/renames.
- Unchanged rebalancer input yields byte-identical proposals and no churn.

## 14. Recorded Decisions

1. Canonical physical organization stays lifecycle-first.
2. UID is identity; path, title, heading, key, and virtual path are names.
3. Snapshots are immutable and atomically parent-published.
4. Committed segments may be shared; mutable worktree state is isolated.
5. Typed edges have one stored active-verb direction and explicit authority.
6. Section markers are mandatory when a section becomes a managed target.
7. Views are read-only; canonical mutation is journaled and transactional.
8. Journal durability precedes mutation; critical mode fails closed when
   durability cannot be proven.
9. SPipe fallback defines provider parity; Simple is optional acceleration.
10. Protocol negotiation is explicit, deterministic, and fail-closed.
11. Trace edges are weighted for clustering; must-link scope remains narrow.
12. Physical rebalancing and common promotion require separate approval.

## 15. Consequences

The model supports stable cross-project trace and many navigational trees
without content duplication. Immutable snapshots simplify concurrent readers,
caching, rollback, and deterministic MCP responses. The costs are metadata,
journal/recovery machinery, parity fixtures, and careful provider/version
governance. Those costs are accepted because path-based identity, writable
views, and provider-dependent truth would make refactors and strict evidence
unsafe.

## 16. Authority-Bound Lexical Source Checkpoint

Commit `9eb667e23b` admits the dependency-free lexical-source capsule. Its only
public operation is built from exactly four captured synchronous ports:

```text
verifySearchReceipt(binding) -> frozen exact binding echo
readLexicalProviderPage(page_request) -> frozen provider page
authorizeArtifactCandidate(candidate) -> frozen authorization decision
verifyLexicalEvidence(evidence) -> frozen aggregate evidence decision
```

The capsule owns request validation, query/binding digests, page-chain
validation, fixed-count candidate authorization, aggregate evidence, and the
complete RRF-v2 source envelope. It does not own scoring or provider storage.
`readLexicalProviderPage` is therefore an untrusted port: provider identity
must remain `spipe-search-provider/1.0` with analyzer
`spipe-unicode-lex-v1`, score contract `bm25-fixed-v1`, and one stable
implementation digest for the entire request.

### 16.1 Cursor and page authority

Every non-null provider cursor hashes under
`spipe-authorized-lexical-provider-cursor-v1\0` with the request binding digest.
A page receipt binds the inbound cursor digest, exact requested limit, next
cursor digest, page digest, and exact-pin exclusion. The next page must echo the
previous next-cursor digest as its inbound digest. Rank numbering is dense and
continuous across pages; candidates are ordered by descending non-negative
fixed-point source score and then unsigned UTF-8 artifact UID. Reused cursors,
cursor digests, receipts, artifact UIDs, rank gaps, short non-exhausted empty
pages, or provider-identity changes fail closed.

The complete page evidence list is hashed separately from the complete ordered
candidate/rank evidence. `verifyLexicalEvidence` runs exactly once only after
all locally provable page checks and exactly one authorization call per
candidate. Its receipt and both digests become source identity. No partial or
unverified page set may enter fusion.

### 16.2 Canonical evidence contract

Digest preimages use restricted `spipe-canonical-json-v1`: strings and record
keys are Unicode scalar text normalized to NFC; normalized keys must be unique
and sort by unsigned UTF-8; arrays are dense; records are closed data records;
numbers are safe integers other than negative zero; and C0 controls are emitted
as lowercase long escapes (`\u0009` for U+0009). Independent test
canonicalization is required so digest parity is not self-asserted.

### 16.3 Exact-pin exclusion boundary

The accepted design now requires the provider to apply
`excludedDocumentUid` before ranking and pagination. The binding, page,
page-receipt, page-set, rank-evidence, and final evidence receipt all attest the
same value and `exclusionApplied` decision. Client post-filtering is forbidden:
after a provider-limited top 1,000 it can supply at most 999 remaining entries
and cannot prove a complete `sourceK=1000` lexical pool.

This changes no ownership rule: a versioned provider adapter/protocol mapping
remains a prerequisite before the source can be wired to an implementation.
The admitted lexical capsule cannot be treated as an adapter or an integrated
search endpoint.

### 16.4 Non-admitted graph candidate and integration order

The two-file graph candidate in `/tmp/spkc-graph-candidates-4OKnKd` is rejected
as evidence after the bounded third cycle: focused `13/14` with an uncontracted
cyclic `workUnits <= 9` oracle. Seven static defects were patched, but the full
suite and final highest-capability review did not run. It has no commit and
cannot close graph boost or AC-4.

Integration proceeds only through separately owned, reviewable boundaries:

1. graph generator and its independent oracle;
2. provider-adapter/protocol interface and ownership freeze, then its parity
   implementation (filenames are not yet frozen);
3. standalone cross-source rerank-evidence assembler/verifier;
4. integrated pipeline consuming admitted exact, lexical, graph, RRF-v2, and
   pair-based reranker contracts.

Rerank-evidence is not folded into either graph generation or the pipeline;
separate evidence admission prevents orchestration from manufacturing authority.

## 17. Accepted Graph Capsule and Authorized Lexical Provider Boundary

Section 16.4 records a real rejected attempt and remains useful provenance, but
its non-admission status is superseded by commit `626b3e0797`. The accepted
graph capsule is the product/oracle pair
`src/search/graph_candidates.js` and
`test/unit/search_graph_candidates_test.js` under
`examples/05_stdlib/spipe/`. It passed focused `16/16`, full `174/174`, Wave 2
`9/9`, Wave 3 `25/25`, Wave 4 `9/9`, legacy integration, performance, and both
pre-runtime and final highest-capability review.

### 17.1 Capsule authority and lifecycle

`createAcceptedGraphCandidateGeneratorV1` remains a read-only child capsule of
search orchestration. It captures exactly `readGraphSnapshot`,
`authorizeNode`, and `verifyEdgeReceipt`; it owns deterministic bounded
traversal and evidence construction, but it does not own snapshots, policy,
fusion, reranking, or user-visible result limits.

Its fixed resource envelope is depth 3, at most 1,000 output candidates,
50,000 incident-edge work units per page, 500,000 total work units, 20,000
nodes, 50,000 edges, and 1,001 roots. The accepted cyclic oracle is exactly ten
work units. Canonical authorization runs for every declared node before edge
verification; only accepted explicit/generated edges with exact authority
receipts enter traversal. Opaque WeakMap continuation state is factory-local,
single-use, and destroyed on total exhaustion. Continuations resume the exact
edge without repeating authority ports.

The path order is deterministic by distance, seed tier, seed rank, generated
edge count, negative bottleneck confidence, unsigned-UTF-8 edge sequence,
out-before-in direction sequence, and unsigned-UTF-8 node sequence. The source
order adds artifact UID as its final tie-break. Ordered
`{edgeUid,authorityReceiptUid}` pairs are authoritative; derived unique arrays
must not erase shared-receipt multiplicity. Four independent literal digest
goldens bind the admitted edge set, evidence records, source identity, and RRF
candidate pool.

### 17.2 Provider protocol versus semantic identity

The provider adapter is a separate boundary from the lexical-source capsule:

```text
lexical_source (synchronous evidence consumer)
        │ admitted nine-field D-* receipt projection
        ▼
authorized lexical-page adapter
        │ wire 1.1 lexical_page / qr-* transport receipt
        ▼
JS in-process provider now; Simple process provider after async design
```

Wire `1.1` adds only the `lexical_page` operation and
`authorized_lexical_page:true`. It does not fork the search semantics:
`spipe-search-provider/1.0`, `spipe-unicode-lex-v1`, and `bm25-fixed-v1` remain
the provider, analyzer, and scorer identities. The new bridge identities are
`spipe-authorized-lexical-provider-page-v1` for page records and
`spipe-authorized-lexical-provider-adapter-v1` for the adapter.

Exact exclusion is provider-owned and happens before scoring/top-k insertion;
corpus statistics remain snapshot-owned and unchanged. Cursor identity binds
generation/implementation, workspace, snapshot, authorization scope, lexical
root, binding/query digests, exclusion, and next rank. It intentionally omits
the per-page `qr-*` receipt and requested limit, because transport receipts are
page-local and the terminal fragmented page can request fewer candidates.

The `qr-*` and `D-*` namespaces separate transport integrity from evidence
authority. Simple wire returns a query receipt. The adapter verifies it, stores
a signed `D-*` page receipt, and exposes the nine fields required by the
lexical-source capsule. Aggregate authority later resolves the `D-*` receipts;
neither the pipeline nor the provider may mint that evidence locally.

### 17.3 Ownership and process boundary

JavaScript protocol/schema and in-process semantics stay in
`examples/05_stdlib/spipe/src/index/{contracts,logical_index}.js` and
`src/provider/{protocol,adapter,js_fixed_point,index,lexical_page}.js`. The
independent conformance owner is
`test/unit/search_lexical_provider_page_test.js` with the fixed Wave 4 vector
fixture. Simple-native mapping stays in
`src/app/spipe_knowledge_provider/{lexical,wire_query,wire_core,protocol,service}.spl`;
no parallel native scorer or lifecycle owner is introduced.

The current lexical-source port is synchronous, while a long-lived Simple
process speaks asynchronous streams. This is an unresolved architectural
boundary, not permission to block the hot path or spawn per request. The first
implementation slice is in-process JavaScript. Native integration requires a
reviewed async lexical-source v2 or an async-collect/immutable-replay capsule.

### 17.4 Performance, integration, and status

The provider remains lazily started and must not perform process spawning,
full-tree scans, repeated file reads, or retry sleeps on the request path.
Candidate gates are startup P95 at most 250 ms and warm lexical P95 below
100 ms on 50,000 artifacts. Maximum RSS needs both a qualified receipt and a
configured process cap; the numeric budget is blocked on Wave 0 measurement.

Graph admission does not imply provider conformance or integrated search.
Rerank-evidence implementation is active as its own authority capsule. The
only accepted integration sequence is exact identity, provider-owned lexical
exclusion, complete lexical collection, graph generation, complete-pool RRF
v2, rerank-evidence verification, pair-based reranking, explanation assembly,
and user limit last. AC-4 remains open until that complete path is admitted.

### 17.5 Authority bridge correction and capsule ownership

The full synchronous JavaScript authority bridge is now the only accepted
first slice. The earlier reading of `lexical_page.js` as a wire-independent
translator that manufactures a nine-field `D-*` projection is a rejected
pre-authority alternative. The projection is compatibility data consumed by
`lexical_source.js`; authority comes only from a verified transport receipt
plus a signed, stored, and re-resolvable evidence record.

```text
createAuthorizedLexicalSourceV1
  ├─ verifySearchReceipt                    existing trusted search binding
  ├─ authorizeArtifactCandidate             existing per-artifact decision
  └─ createAuthorizedLexicalProviderPageBridgeV1
       ├─ providerSession                    frozen wire/root/scope/policy pin
       ├─ issueTransportQueryReceiptV1       qr-* issuer
       ├─ verifyTransportQueryReceiptV1      qr-* verifier
       ├─ executeLexicalPageV11              synchronous in-process provider
       ├─ lexicalEvidenceAuthority           identity/sign/verify for D-*
       ├─ lexicalEvidenceStore               reserve/commit/resolve/tombstone
       └─ clockNowMs                         trusted expiry observation
```

The factory exposes exactly the frozen
`{readLexicalProviderPage,verifyLexicalEvidence}` pair. It is a parent-owned
adapter capsule: the provider owns ranking and pre-ranking exclusion; the
authority owns signatures and current key/policy/revocation identity; the store
owns immutable receipt objects and replay keys; the lexical source owns page
collection and digest construction. No child may reach into a sibling's
private state or mint another child's identity.

The transport remains wire `{major:1,minor:1}`, capability
`authorized_lexical_page:true`, and operation `lexical_page`, while provider,
analyzer, and score identities remain `spipe-search-provider/1.0`,
`spipe-unicode-lex-v1`, and `bm25-fixed-v1`. A successful wire response echoes
the full verified `spipe-query-receipt-v1` (`qr-*`). The bridge signs a full
`spipe-lexical-page-evidence-receipt-v1`, stores it atomically, resolves it
again, and only then derives the nine-field `D-*` projection. Aggregate
verification resolves every page `D-*` in order, re-verifies its signature,
embedded `qr-*`, root, scope, policy, authority/revocation generation, expiry,
cursor/rank chain, and page content, then signs/stores/re-resolves a
`spipe-lexical-aggregate-evidence-receipt-v1`.

Initialization supports exact minors 1.0 and 1.1 without silent negotiation:
the legacy closed 1.0 capability record stays byte-compatible, while the closed
1.1 record adds final `authorized_lexical_page:true`. The semantic identity
arrays, limits, and empty optional-field list do not change. The bridge can be
composed only from a validated 1.1 result.

The provider-side executor is frozen separately as
`createInProcessLexicalPageExecutorV11({provider,providerSession,
verifyTransportQueryReceiptV1,lexicalCursorAuthority,clockNowMs})`. It verifies
the `qr-*` before reaching the raw index. Non-null cursors are signed
`spipe-authorized-lexical-cursor-v1` records bound to provider implementation/
generation/session, root, scope, policy, query, exclusion, and next rank; they
omit requested page size and page-local `qr-*` by design.
The frozen provider session also carries the expected transport key,
authority-generation, and revocation-generation tuple. Verifier-current
decisions must echo it on both sides; a revocation-generation change invalidates
the session.
`lexicalCursorAuthority` uses the exact closed authority
`identity/sign/verify` capability and must match that transport tuple and
policy; the evidence signer may be distinct but cannot change policy.

Authority signatures and receipt/store identities use restricted canonical
JSON with the framed form
`UTF8(domain + "\0") || U64BE(length) || canonicalBytes`. Existing admitted
lexical hashes keep their unframed lowercase-domain convention. Exact domains,
preimages, record fields, error precedence, and caps are frozen in detail
design Section 17.7 and are not reinterpreted by adapters.

The store is a bounded synchronous process-local capsule for this slice: all
reserved, active/replay, and tombstoned operations share a 4,096-entry and
64-MiB accounted-byte cap; page/aggregate records are limited to 1/2 MiB.
Each reservation pre-charges exactly 2,048 bytes of worst-case tombstone
headroom, which is retained if commit cannot fit. Entries remain until
generation destruction. Exact live replay resolves/re-verifies and returns the
same receipt without transport issuance, provider execution, signing, or
commit. Operations reserve atomically before `qr-*` issuance; every
post-reservation failure tombstones the key, so an identical retry cannot make
a second transport/evidence chain. Conflicting, expired, revoked, wrong-root,
wrong-policy, or wrong-generation replay fails closed. Persistence across
restart is not claimed. Provider selection occurs before bridge construction,
so a failed page cannot switch providers mid-collection.

The public-error and storage capsules intentionally use different closed
vocabularies. After reservation, an unclassified malfunction of trusted cursor
authority `identity`, `sign`, or `verify` is stored as the existing legal
`interrupted` tombstone before the bridge returns public `internal_error`.
`internal_error` never enters the tombstone enum. A specific expiry,
revocation, binding, authority-generation, policy, or record-corruption result
established first retains precedence.

Successful bridge and provider-executor paths both observe their trusted clock
before work and immediately before return. The end observation rechecks expiry
and current revocation; work that crosses expiry is tombstoned and cannot
produce evidence.

Implementation ownership adds
`examples/05_stdlib/spipe/src/provider/lexical_evidence_store.js`; the complete
bridge stays in `provider/lexical_page.js`, protocol validation in
`provider/protocol.js`, translation/session state in `provider/adapter.js`, and
provider-side receipt checking plus page execution in `provider/js_fixed_point.js`.
`index/contracts.js`, `index/logical_index.js`, and `provider/index.js` retain
the roles stated above. `provider/durable_lifecycle.js` is not reused: it owns
asynchronous mutation-candidate persistence, not synchronous query evidence.

This architecture deliberately makes no subprocess, async stream, native, or
cross-restart durability claim. A later provider may implement the same
semantics only through a separately reviewed asynchronous boundary. Until the
full JS oracle proves both signatures and store resolution, the bridge is
design-frozen but not conforming, and AC-4 remains open.

### 17.6 Admission status and next dependency order (2026-08-26)

Commit `47a922eec6` admits this provider-authority **architecture contract**
after highest-capability review; it does not admit an implementation. The
attempt in `/tmp/spkc-lexical-provider-z15Uhp/repo` reached its pre-runtime
review cap without producing an in-scope product or oracle edit. The next
provider implementation must start from the complete capsule, authority,
store, replay, cursor, clock, and error ABI in Section 17.5/detail design
Section 17.7. The previously rejected minimal projection adapter remains
architecturally invalid.

The candidate rerank-evidence capsule in
`/tmp/spkc-rerank-evidence4-aIcFIZ/repo` is uncommitted and unadmitted. Its
focused `16/16`, full unit `190/190`, Wave 2 `9/9`, Wave 3 `25/25`, Wave 4
`9/9`, legacy, security, workflow, and performance gates are retained, but
final highest-capability review after cycle three found two blockers:
`limit_exceeded` must retain precedence for oversized derived evidence arrays,
and the semantic contract string must be bound to the admitted consumer
contract. A fresh session owns the exact source/oracle pair and its review.

Dependency order is provider implementation/admission, rerank-evidence
repair/admission, then integrated exact/lexical/graph/RRF/evidence/rerank
orchestration. AC-4 remains open.

### 17.7 Superseding capsule admission status (2026-08-26)

The rerank-evidence capsule is now admitted by commit `4455b760da`. Syntax,
focused `18/18`, unit `192/192`, Wave 2 `9/9`, Wave 3 `25/25`, Wave 4 `9/9`,
legacy, security, workflow, and performance gates passed, followed by an
independent xhigh `PASS` in verify/fix cycle 2 of 3. This admits the standalone
authority-evidence boundary only; it does not admit the provider or integrated
pipeline.

The provider-authority ABI repair did not land. After the mandatory third
cycle its status is `FAIL` because collision-result signaling, executor error
classification, cursor error precedence, and canonical-byte accounting versus
heap/RSS limits remain under-specified. No product edit or product test was
performed and no draft entered repository history. Failed object
`3827a1099e`, retained under `/tmp/spkc-provider-abi-repair2-clean`, is
non-authoritative forensic material and must not be used to extend this
architecture contract.

The architecture dependency order is now provider-ABI repair, provider
implementation/admission, then integrated pipeline admission. Wave 4 and AC-4
remain open.

### 17.8 Cursor-authority failure mapping (2026-08-26)

The final-four representability conflict is resolved with no ABI expansion.
For a trusted cursor-authority malfunction after reservation, storage records
the existing legal `interrupted` tombstone and the public boundary returns
`internal_error`, in that order. This is explicit capsule translation, not
implicit coercion; `internal_error` remains absent from the tombstone enum.
Specific already-established failure classifications retain precedence.
Provider implementation and admission, Wave 4, AC-4, and pipeline admission
remain open.

### 17.9 Full ABI consolidation status (2026-08-26)

The eleven-item consolidation attempt stopped `FAIL` at the mandatory
three-cycle cap. It produced no product edit, product test, admitted contract,
or push. Snapshot `e5c556de59d` at
`/tmp/spkc-provider-abi-full-uWb9kD/repo` is immutable forensic evidence, not
architecture authority.

Although implementation-readiness review passed, independent
highest-capability review found the proposed capsule non-self-contained:
Section 17.11 excludes Section 17.7.1 while relying on its exact
`providerSession`, authority, and executor schemas, and excludes Section 17.7.9
without defining the complete public error record/field shapes and exhaustive
precedence. The next fresh architecture session must restate those definitions
inside Section 17.11 and must not inherit excluded control prose. Provider
readiness/implementation/admission, Wave 4, AC-4, and pipeline admission remain
open.

### 17.10 Self-containment repair status (2026-08-26)

The fresh repair stopped `FAIL` at the mandatory third review/fix cycle. It
produced no authoritative contract or product edit, product test, or push.
Snapshot `e77cb713d5703d864f32d16ab3abab0afb5d3215` at
`/tmp/spkc-provider-self-contained-JdUR6t/repo` is immutable forensic evidence,
not architecture authority; its rejected clauses must not be copied.

Implementation-readiness review passed, while independent highest-capability
review found three blockers: overlapping generic code-only unauthorized and
provenance arms; contradictory reserve ordering around binding/cursor checks
and `Cidentity`/`Cverify`; and no exact `requestedLimit` range despite the
candidate cap. A fresh architecture session must define a structurally
disjoint executor-error union, one reserve/cursor order with a single
tombstone owner, and `requestedLimit` in `1..1000`. Provider readiness,
implementation/admission, Wave 4, AC-4, and pipeline admission remain open.

### 17.11 Fresh authority-bridge correction candidate (2026-08-26)

The architecture now freezes three repair constraints for the synchronous
in-process bridge. First, its executor failure algebra is structurally
disjoint: the generic `{code}` branch excludes `unauthorized`; the only
unauthorized branch has exact private `{code:"unauthorized",tombstoneReason}`
data, where the reason is one of the existing seven store reasons and never
crosses the public boundary. The bridge owns persistence/redaction; the
executor owns no evidence-store mutation.

Second, every page path performs only closed-shape/type/capability checks before
the one atomic reservation. Cursor identity, decoding, signature verification,
binding, generation, policy, and liveness checks are all post-reservation for
both fresh and replay branches. The bridge maps their first established fact
through the existing ordered tombstone table and makes exactly one tombstone
attempt; malformed/oversized cursors remain pre-reservation errors. Third,
`requestedLimit` is a fixed required positive safe integer `1..1000` in every
bridge/wire/executor/page/replay contract, while cursors deliberately do not
bind its per-page value.

This candidate retains bounded-store and public-error contracts and is not
provider implementation/admission evidence. Wave 4, AC-4, and pipeline
admission remain open pending static and independent high-capability review.

### 17.12 Provider implementation non-admission: configuration ABI conflict (2026-08-26)

The provider implementation attempt at
`/tmp/spkc-provider-admission4-kVaqO2/repo`, based on
`f7ec2dc1b0c0de4b42bb97940b17bec9db29e5a1`, stopped before runtime work after
two immutable xhigh pre-runtime `FAIL` reviews. The final review attempt added
no edit to its exact ten-file scope and ran no runtime test, commit, or push.
The forensic candidate itself has an existing dirty diff. It is forensic
context only; do not reuse its code or contract wording.

The decisive architecture contradiction is that Section 17.14.3 requires the
bridge to own post-reservation cursor identity, decode, and verification, but
the frozen seven-field bridge factory configuration provides no cursor-authority
port. Therefore no implementation can conform without a fresh configuration-ABI
decision. Mandatory tombstones, exact executor-error discrimination, full
replay verification, cursor digest, store accounting/idempotency, closed-object
accessors, and oracle vectors remain unimplemented. A fresh design session must
resolve that configuration ABI before a new implementation lane begins. Provider
admission, Wave 4, AC-4, and pipeline admission remain open.
