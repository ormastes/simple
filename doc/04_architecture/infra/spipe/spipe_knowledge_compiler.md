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

`AuthorizationPort` is an authenticating composition-root service, not a
shape-compatible object accepted from a handler. The composition root creates a
branded `AuthorizationPortV1` only after loading its signature verifier,
issuer/algorithm/key allowlist, and durable key/revocation policy. The following
is the **required** cursor/read extension of that same port (not a description
of the currently admitted Trust/Edge-only implementation):

```text
verifyCanonicalReadReceiptV1(receipt, expected_binding, clock_now_ms)
  -> Result<VerifiedReadGrantV1, AdmissionFailure>
issueCursorReceiptV1(verified_read_grant, expected_cursor_binding, page_position, requested_expires_at_ms, clock_now_ms)
  -> Result<CursorReceiptV1, AdmissionFailure>
verifyCursorReceiptV1(receipt, expected_binding, clock_now_ms)
  -> Result<VerifiedCursorGrantV1, AdmissionFailure>
rotateCursorReceiptKeyV1(rotation_request, clock_now_ms)
  -> Result<CursorReceiptKeyPolicyV1, AdmissionFailure>
applyDueCursorReceiptKeyTransitionsV1(clock_now_ms)
  -> Result<CursorReceiptKeyPolicyV1, AdmissionFailure>
```

`ExpectedReadBindingV1` (`expected_binding`) is an authority-created closed
tuple of authority key/epoch, **authority instance UID**, **authority manifest
digest**, normalized alias URI-or-null, canonical URI, workspace UID, project
UID-or-null, **worktree UID**, target kind/UID, immutable **base snapshot UID**,
content-addressed **authority snapshot UID**, revision ID, view kind,
normalized logical path, normalized selector/filter digest, effective scope
digest, ordering version, page limit, and policy version. The signed legacy
`CanonicalReadReceiptV1` deliberately lacks a worktree field for compatibility;
on successful verification the port copies the sealed expected binding into the
opaque `VerifiedReadGrantV1`. That grant's trusted base-snapshot,
authority-snapshot, worktree, authority-instance, and authority-manifest claims
are therefore not derived by cursor, URI, or
projection code. The complete receipt, grant,
cursor, and durable-rotation schemas are frozen in §21. A parser/projection
module receives only verified grants; it cannot create a receipt, widen a
selector, or choose a replacement workspace/snapshot. The root URI grammar is
likewise closed: only
`spipe://workspace/{workspace}/` denotes a workspace directory; the un-slashed
form is malformed rather than normalized.

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
workspaces, and `W-` for new worktree identities. Schema-v1 `W-` values are
decoded by record type (`workspace` or `worktree`) and never compared across
types. Schema v2 writes only `WS-`/`W-` and records a tracked
`IdentityMigrationRecord(old_uid, old_record_type, new_uid, migrated_in_snapshot_uid)`.
The new UID is derived, not randomly allocated: `WS-` or `W-` plus the first
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
indexes; pages contain at most 100 entries, 200 Markdown lines, and at most
6,000 `spipe-markdown-token-v1@1` tokens. Collision suffixes use a deterministic short
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

### 7.2 Wave 5 delivery capsule and adapter order

Wave 5 is a read-only delivery capsule, not a second authority path.  It may
start only after the production `KnowledgeCompilerCommitPublisherV1` has
published a sealed inventory (W5A) and the branded canonical-read/cursor
extension has passed W5C.  The accepted pure `ProjectionKernelV1` and its
unsigned local continuation are useful internal algorithms, but are expressly
not an MCP resolver, receipt issuer, materializer authorization, or substitute
for either prerequisite.

The only admitted dependency direction is:

```text
legacy-stdio | mcp-2026-http | editor-vfs | materialize CLI
                         -> McpDeliveryFacadeV1
                         -> ResourceResolverV1
                         -> SnapshotAuthorityPortV1 + AuthorizationPortV1
                         -> ProjectionPortV1
                         -> immutable published authority view
```

`McpDeliveryFacadeV1` owns protocol-envelope conversion only.  It receives a
normalized `ReadRequestV1` and returns a normalized `ReadResponseV1`; it has no
store, filesystem, inventory-builder, signer, cursor-key, or snapshot-refresh
import.  `ResourceResolverV1` performs exactly: parse/normalize URI; open the
receipt-named sealed view; prove canonical target or directory membership; make
the expected binding; verify the read receipt; verify an inbound cursor for a
list; call the projection port once; and issue the next cursor only after a
successful list.  Any failure before render/list makes zero projection calls;
outbound cursor issue failure discards the page.  The same resolver path serves
resources, tools, materialization planning, and editor reads, so transport
adapters cannot disagree about authorization, ordering, URI acceptance, or
privacy response shape.

There are four separately gated adapters.  (1) Legacy stdio preserves existing
tools and `spipe://skill`, then exposes newly implemented resources/tools only
after initialization.  (2) Stateless MCP 2026 is added only after the same
normalized response transcript passes under HTTP authentication; it never
inherits stdio trust.  (3) Materialization obtains a separate
`SafeFilesystem.Materializer` capability after the read has been resolved and
uses only `MaterializerSafeFilesystemPort`; a successful MCP read neither
creates nor implies this capability.  (4) An editor provider implements
read/stat/readDirectory from `ReadResponseV1`, rejects write/delete/rename, and
routes any requested canonical mutation to the separately authorized refactor
plan/apply flow.  FUSE/ProjFS remains outside this capsule.

The public wire mapping is frozen as follows.  `resources/list`,
`resources/templates/list`, `resources/read`, `spipe_list`, and `spipe_read`
use the resolver; `spipe_search`, `spipe_resolve`, `spipe_trace`, and
`spipe_diagnostics` may be advertised only after their respective sealed,
authorized providers exist.  A capability is absent rather than advertised
early.  Read-admission denials map to the one bounded public
`not_found_or_unauthorized` result in every adapter.  JSON-RPC envelope errors
remain protocol errors, while invalid HTTP authentication, headers, origin,
rate/budget, or TLS policy stop before resolver invocation.  Cache policy is
derived after authorization from the normalized response: only a proved public
immutable projection can be shared; all other responses, including denial,
are private/no-store.

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

## 18. Wave 5 Read-Only Virtual-View Capsule (2026-08-26)

<!-- codex-design -->

Wave 5 is a separate read-only capsule and may be implemented independently of
the provider bridge. `KnowledgeCompiler` publishes immutable snapshots;
`WorkspaceRegistry` opens a named workspace; `ResourceResolver` turns a
validated URI into a target; and `ProjectionPort` alone lists or renders that
target. MCP transports and the CLI are adapters only: they cannot parse a
repository, mutate canonical files, or cause an index/provider refresh during a
request. A snapshot ID is carried through every page, resource, tool result,
and cache identity.

`ProjectionService` owns virtual projection and has two one-way outputs:
protocol read adapters and the optional materializer adapter. The former emits
the deterministic resource/tool envelope. The latter is the sole holder of
`SafeFilesystem.Materializer`, converts it once into a projection- and
snapshot-bound `MaterializerRootGrant`, and calls only
`MaterializerSafeFilesystemPort`. Neither native/worker filesystem providers
nor a trusted helper receive authorization authority. RefactorService is a
separate writer capsule with no materializer capability.

The initial composition deliberately includes legacy stdio and protocol-neutral
resource/tool services before stateless HTTP, notifications, editor VFS, or OS
mount adapters. A failed optional materializer admission leaves read-only MCP
views available; a URI, snapshot, authorization, or projection ambiguity fails
closed. Public cacheability is allowed only for wholly public snapshot output;
private/mixed output remains private/no-store and authorization precedes any
conditional-cache decision.

The capsule is admitted only when the focused protocol, URI security,
projection determinism, cache-visibility, and materializer fault/race evidence
listed in the Wave 5 detail contract passes. It is not evidence that the
unresolved provider protocol or any write/refactor capability is admitted.

## 19. Wave 5 URI-foundation non-admission boundary (2026-08-26)

<!-- codex-design -->

The URI-foundation candidate exhausted three independent review/fix cycles and
is uncommitted and not admitted. Wave 5 URI execution remains pending. A new
implementation starts from this architecture, not from the rejected code.

`ResourceResolver` canonicalizes a legacy alias only to a candidate, proves
that candidate's target membership, and only then authorizes. It calls
only `AuthorizationPort.verifyCanonicalReadReceiptV1`, which allowlists the
version/key, verifies the signed `D-` payload (`spipe-uri-read-v1\0` plus
canonical JSON), requires `decision=allow`, a live clock window, and the
current revocation epoch, then returns the trusted read grant. A non-paginated
read calls `ProjectionPortV1.render` with that grant. A directory list verifies
an inbound cursor against that same grant before `ProjectionPortV1.list`, then
issues an outbound cursor from the returned next position. Any difference
causes fresh authorization or a closed failure. Thus `spipe://skill` cannot be
read under an alias-only grant.

`CanonicalReadReceiptV1` has exactly `{receiptVersion, authorityKeyId,
authorityKeyEpoch, normalizedAliasUriOrNull, canonicalUri, workspaceUid,
projectUidOrNull, targetKind, targetUid, baseSnapshotUid, authoritySnapshotUid,
revisionId, viewKind,
normalizedLogicalPath, selectorDigest, effectiveScopeDigest, orderingVersion,
pageLimitOrNull, policyVersion, decision, issuedAtMs, expiresAtMs, receiptUid,
issuerKeyId, revocationEpoch, signature}`. `CursorReceiptV1` is exactly the
complete schema in §21: it retains canonical alias/URI/target binding, includes
the verified worktree, and uses validated `pagePosition` (never `lastSortKey`).
Both use only the sole verifier method names frozen in §3.1; no
`verifyCanonicalTargetReceiptV1` alias exists.

Before authorization and rendering, the resolver directly verifies that the
snapshot exists, is immutable, belongs to the selected workspace/project, has
the stated revision, and contains the canonical target kind/UID. URI components
and query values are selectors subject to validation, never authority claims.

Admission evidence must run all URI families—workspace root/view, project
artifact/section, trace, diagnostics, and legacy alias; search is a tool
input—through the hostile matrix: malformed/overlong and unsupported URI;
fragment/empty identity; empty/duplicate/unknown bounded query fields;
percent/double-decode; traversal, slash/backslash, encoded separator/dot,
drive/UNC, Windows device/reparse, ADS colon, trailing dot/space;
control/malformed Unicode, NFC/NFD collision, mixed-case identity; cursor
mismatch; receipt forgery/expiry/signature/revocation failure and every alias, scope,
policy, snapshot, revision, kind, or UID mismatch; plus indistinguishable
hidden/absent targets. Every rejection is fail-closed and path-redacting.

The same table includes a positive canonical list/read/render assertion for
workspace root/view, artifact, section, trace, diagnostics, legacy alias after
canonical reauthorization, and `spipe_search`. Legacy success is evidence only
when the rendered target is the freshly authorized canonical target.

## 20. SnapshotAuthority virtual capsule (2026-08-26)

<!-- codex-architecture -->

Wave 5 requires a new parent-owned authority capsule before a URI resolver can
be admitted. Existing snapshot storage verifies snapshot metadata but is not a
target-membership authority: it has no immutable target inventory and does not
bind the workspace/worktree selection to the read. Giving URI or projection
code raw store access would permit assertion-based target resolution.

`KnowledgeCompiler` is the only writer of a manifest's target inventory. The
new `SnapshotAuthorityService` owns snapshot admission and receives the
registry, immutable store, and private immutable target-inventory store. It publishes
the branded `SnapshotAuthorityPortV1`; siblings receive opaque
`SnapshotAuthorityViewV1`, never a filesystem location or mutable manifest.
`ProjectionService` owns the separately branded `ProjectionPortV1` and only
renders targets returned by that view. MCP/CLI adapters consume both through
`ResourceResolver`; they cannot query stores directly.

```text
ResourceResolver
  -> WorkspaceRegistry.resolveExact(workspaceUid)
  -> SnapshotAuthorityPortV1.openBoundSnapshot(binding)
  -> SnapshotAuthorityPortV1.resolveCanonicalAlias(...) -> resolveCanonicalTarget(...)
     (or resolveCanonicalTarget(...) directly for canonical URIs)
  -> SnapshotAuthorityPortV1.createExpectedReadBindingV1(authorityView,
       canonicalTargetOrDirectory, normalizedRequest)
       -> ExpectedReadBindingV1
  -> AuthorizationPortV1.verifyCanonicalReadReceiptV1(..., ExpectedReadBindingV1, ...)
       -> verifiedReadGrant
  -> direct: ProjectionPortV1.render(authorityView, canonicalTarget, verifiedReadGrant)
     list: AuthorizationPortV1.verifyCursorReceiptV1(..., verifiedReadGrant, ...)
           -> verifiedCursorGrant
           -> ProjectionPortV1.list(authorityView, directoryTarget, verifiedReadGrant,
                                    verifiedCursorGrantOrNull)
           -> AuthorizationPortV1.issueCursorReceiptV1(verifiedReadGrant,
                                                       {pagePosition: nextPosition, requestedExpiresAtMs}, ...)
```

The binding is exactly `{workspaceUid, projectUidOrNull, worktreeUid,
baseSnapshotUid, authoritySnapshotUid, revisionId, registryRevisionId}`.
`openBoundSnapshot` verifies all seven fields against
the registry and immutable manifest, validates the manifest digest, and
returns an opaque view. `resolveCanonicalTarget` then proves
`{targetKind,targetUid}` membership in its indexed artifact/section/aggregate
inventory. `listDirectoryTarget` proves an allowed virtual directory mapping
from normalized view/path/selector data. Each result carries the manifest
digest and binding for ProjectionPort's defensive equality check. A missing or
ambiguous mapping is fail-closed; no source-tree scan, default workspace, or
project-only lookup is permitted on the request path.

This is a virtual capsule boundary: the inventory format is private to the
authority service, while the port contracts are stable common interfaces. Its
delivery is **Wave 5a**. Wave 5 URI/MCP/materializer code remains non-admitted
until Wave 5a proves branded-port rejection, workspace/worktree isolation,
revision/snapshot/manifest binding, target-kind/UID membership, and clean
incremental-versus-rebuild inventory parity.

### 20.1 Sealed inventory and pre-authorization target proof

The authority view has a non-cyclic content-addressed seal.
`TargetInventoryManifestV1` bytes bind the pre-existing `baseSnapshotUid`,
scope, workspace/project-or-null/worktree/revision, sorted target entries,
sealed alias index, projection root, and inventory root. A separate
`AuthorityManifestV1` content-addressed `snapshotUid` commits the base snapshot
UID plus inventory root and the same scope tuple. Receipts bind this authority
snapshot UID; base snapshots remain unchanged input identity. Authority
recomputes inventory then authority-manifest bytes/IDs before exposing a view.
Missing, swapped, or tampered inventory is therefore a denial, not a
recoverable index miss.

Workspace aggregates are a separate manifest scope: `projectUidOrNull=null`
is valid only for `workspace_aggregate`, which commits the sorted contributing
project snapshot roots. A project scope requires its non-null project UID.
This bridges existing project-owned snapshots without letting a URI assert a
null-project read.

The precise call order is: parse; exact registry workspace/worktree lookup;
open the receipt-named authority snapshot/revision as an *untrusted candidate*
and verify its sealed inventory; a legacy alias yields only a canonical
candidate, then `resolveCanonicalTarget` proves that candidate wholly inside
the view (canonical URIs prove their target directly); derive the closed
`ExpectedReadBindingV1` from the proved view/target/request, including
`authorityInstanceUid` and `authorityManifestDigest`; verify the canonical-read
receipt;
for a list, verify the inbound cursor against the resulting read grant, list,
and issue the next cursor; for a direct read, render with the read grant. Thus
alias lookup is neither proof nor authorization, and
receipt verification cannot precede target proof. `worktreeUid` is intentionally
absent from the legacy read receipt but is a trusted claim in the verified read
grant and a signed field of the cursor receipt, as §21.1 defines. No receipt,
alias, URI, or projection adapter can fabricate a target before that proof.

## 21. Cursor-receipt authority extension prerequisite (2026-08-26)

<!-- codex-architecture -->

The concrete `AuthorizationPortV1` currently verifies only distinct Trust and
Edge receipt families (`verifyTrustReceipt` and `verifyEdgeAcceptanceReceipt`).
It cannot issue or verify a fully bound `CursorReceiptV1`; §3.1 is target
architecture, not current capability. Wave 5 URI v3 is non-admitted until the
following extension exists and is independently accepted. A handler must never
sign a cursor or adapt a Trust/Edge receipt into one.

Extend the existing branded composition-root port, never a parallel signer:

`CanonicalReadReceiptV1` remains exactly `{receiptVersion, authorityKeyId,
authorityKeyEpoch, normalizedAliasUriOrNull, canonicalUri, workspaceUid,
projectUidOrNull, targetKind, targetUid, baseSnapshotUid, authoritySnapshotUid,
revisionId, viewKind,
normalizedLogicalPath, selectorDigest, effectiveScopeDigest, orderingVersion,
pageLimitOrNull, policyVersion, decision, issuedAtMs, expiresAtMs, receiptUid,
issuerKeyId, revocationEpoch, signature}`. Its only verification result is the
opaque, branded `VerifiedReadGrantV1`. Its canonical claims are exactly the
verified receipt binding **plus** `{worktreeUid, authorityInstanceUid,
authorityManifestDigest}` copied from the sealed `ExpectedReadBindingV1` passed
to verification. Its complete closed tuple is the §3.1 authority key/epoch,
authority instance UID, authority manifest digest, normalized alias URI-or-null,
canonical URI, workspace/project/worktree UIDs, target kind/UID, snapshot/revision,
view kind, normalized logical path, selector/effective-scope digests, ordering,
page limit, and policy version. Its base/authority snapshot claims are retained
only after their exact receipt-to-binding equality check. `ExpectedReadBindingV1`
is created only from the proven
`SnapshotAuthorityViewV1`, canonical target/directory, and normalized request;
it is not an adapter-owned object. Thus the grant's `worktreeUid` is trusted
authority input even though it is intentionally not serialized in the legacy
read receipt.

`CursorReceiptV1` is exactly `{receiptVersion, receiptKind, authorityKeyId,
authorityKeyEpoch, authorityInstanceUid, authorityManifestDigest,
normalizedAliasUriOrNull, canonicalUri, workspaceUid, projectUidOrNull,
worktreeUid, targetKind, targetUid, baseSnapshotUid, authoritySnapshotUid, revisionId,
viewKind, normalizedLogicalPath, selectorDigest, effectiveScopeDigest,
orderingVersion, pageLimit, pagePosition, policyVersion, issuedAtMs,
expiresAtMs, receiptUid, issuerKeyId, algorithm, revocationEpoch, signature}`;
`receiptVersion="v1"` and `receiptKind="cursor"` are fixed. `pagePosition` is
a canonical JSON array of one to eight scalar sort-key values (NFC text or
bounded safe integers); objects, paths, controls, NaN, and ambiguous numeric
forms are rejected. `issueCursorReceiptV1` derives every non-position binding
field from `VerifiedReadGrantV1`; callers cannot supply a cursor binding. It
sets `issuedAtMs=clockNowMs` and accepts an integer expiry only when
`issuedAtMs < requestedExpiresAtMs <= min(readGrant.expiresAtMs,
issuedAtMs + policy.maxTtlMs)` without overflow.

Receipt fields are exactly `{receiptVersion,receiptKind,authorityKeyId,
authorityKeyEpoch,normalizedAliasUriOrNull,canonicalUri,workspaceUid,
projectUidOrNull,worktreeUid,targetKind,targetUid,snapshotUid,revisionId,
viewKind,normalizedLogicalPath,selectorDigest,effectiveScopeDigest,
orderingVersion,pageLimit,pagePosition,policyVersion,issuedAtMs,expiresAtMs,
receiptUid,issuerKeyId,algorithm,revocationEpoch,signature}`, with
`v1`/`cursor` fixed. `pagePosition` is a canonical JSON array of 1..8 scalar
sort-key values (NFC text or bounded safe integers); no object, path separator,
control character, NaN, or ambiguous numeric representation is valid.
Identity-preimage fields are every listed field except `receiptUid` and
`signature`; `receiptUid` is lowercase SHA-256 of UTF-8
`spipe-cursor-receipt-id-v1\0` followed by its canonical JSON. The signing
payload is every field except `signature`, including that derived receipt UID;
signing bytes are UTF-8 `spipe-cursor-receipt-v1\0` followed by canonical JSON
and `signature` is unpadded base64url. Canonical JSON uses lexicographic field
ordering, NFC strings, base-10 integers, and no omitted/null-equivalent fields.
This domain separation prevents Trust, Edge, and canonical-read signatures from
being accepted as cursors.

The sole `ProjectionPortV1` ABI is:

```text
ProjectionPortV1.render(authorityView, canonicalTarget, verifiedReadGrant)
  -> Result<ProjectionDocumentV1, ProjectionError>
ProjectionPortV1.list(authorityView, directoryTarget, verifiedReadGrant, verifiedCursorGrantOrNull)
  -> Result<ProjectionPageV1, ProjectionError>
```

It accepts only mutually matched opaque branded values from the same authority
instance and repeats binding/manifest equality checks. The resolver verifies an
inbound cursor before `list`; after a deterministic page returns its next
position, the authorization port issues the outbound cursor. End-of-list emits
none. On outbound issue failure the page is discarded. No URI, projection, or
materializer adapter may reconstruct a grant, infer a target, refresh a
snapshot, or call a raw store.

### 21.2 Durable cursor key policy and rotation

`CursorReceiptKeyPolicyV1` is the one durable canonical record:
`{policyVersion, currentReceiptRevocationEpoch, currentAuthorityKeyId,
keyRecords, rotationRecords}`. `keyRecords` are canonically ordered by
`authorityKeyEpoch` then key ID and contain exactly `{authorityKeyId, algorithm,
authorityKeyEpoch, issuerKeyId, publicVerificationKey, status, activateAtMs,
graceUntilMsOrNull, revokedAtMsOrNull, revocationEpochAtRevocationOrNull}`.
`status` is one of `pending`, `current`, `grace`, or `revoked`.
`rotationRecords` are canonically ordered by `rotationUid` and contain the
immutable accepted request and committed policy version; a duplicate
`rotationUid` with different bytes fails, while an identical replay returns the
already recorded policy.

The sole logical `CursorReceiptKeyPolicyV1` is persisted as one transactional,
append-only record family: initial `policy`, then `key`, `issuer`, `rotation`,
and `revocation` operations. Every operation carries its monotonic policy
version and immutable operation UID and folds to exactly the canonical record
above; this is not a second policy schema. Initial policy-directory creation
and every operation write, rename, and required parent/file fsync complete
before acknowledgement. Recovery accepts only the longest contiguous
consistent chain; equal UID/bytes replay returns the prior result while altered
bytes or stale version fail closed.

`rotateCursorReceiptKeyV1` atomically appends one `pending` record after a
compare-and-swap of `policyVersion`; its request is exactly `{rotationUid,
expectedPolicyVersion, newAuthorityKeyId, newAlgorithm, newAuthorityKeyEpoch,
newIssuerKeyId, newPublicVerificationKey, activateAtMs, priorGraceUntilMs,
revocationEpochAtPriorRevocation}`. Epochs and the revocation epoch are
strictly monotonic, one key ID maps to one algorithm, and
`clockNowMs <= activateAtMs < priorGraceUntilMs` is required. Only the
composition-root administrator invokes rotation or due transitions.

`applyDueCursorReceiptKeyTransitionsV1` is the only state-transition writer.
At `activateAtMs`, it atomically changes the pending record to `current` and
the former current record to verification-only `grace`; at `priorGraceUntilMs`,
it changes that grace record to `revoked`, records its revocation time and
epoch, and advances `currentReceiptRevocationEpoch` to the recorded monotonic
value. It durably commits each transition before use, is restart-idempotent,
and fails closed if time and durable state disagree. A pending key signs or
verifies nothing; current signs and verifies; grace verifies only; revoked
neither signs nor verifies. Verification requires a permitted record and the
receipt's exact current revocation epoch, so the durable revocation transition
invalidates pre-revocation receipts without changing their bindings. Private
signing handles are non-exportable, purpose/environment-scoped `KeyProvider`
material; only public verification policy is portable. Restart reloads the
policy and provider, and issuance fails closed without the current private
handle.

The required call order is sealed authority view and target proof; creation of
the closed `ExpectedReadBindingV1`, including `authorityInstanceUid` and
`authorityManifestDigest`; canonical-read verification; inbound cursor
verification against that read grant; ProjectionPort call; then outbound issue.
Every pre-projection failure has zero ProjectionPort calls and the bounded
public `not_found_or_unauthorized` response. A post-list issue failure discards
the page and uses that same response; telemetry may retain only a closed reason
such as `stale_cursor`.

### 21.3 Production authority/store admission correction

Every authority binding uses `W-<opaque-base32>` worktree UIDs only. The
composition root owns branded `WorkspaceRegistryV1`, `SnapshotStoreV1`, and
`TargetInventoryStoreV1`, exposing exactly
`resolveExactWorkspaceWorktreeV1`, `openExactSnapshotV1`,
`publishAuthorityInventoryV1`, and `openPublishedAuthorityInventoryV1`.
Their immutable records bind registry revision, snapshot revision, base
snapshot UID, inventory root, authority snapshot UID, and manifest digest.
`openBoundSnapshot` reads registry -> snapshot -> published inventory and then
re-reads both exact revisions before returning a view; changed revisions deny.

Only KnowledgeCompiler's production snapshot-commit transaction publishes
inventories. It selects all and only complete project roots for the exact
registry revision, atomically makes the project and aggregate inventories
reader-visible, then publishes authority manifests. Its publisher argument is
a branded, non-forgeable `AuthorityInventoryPublishPermitV1` minted only by
that transaction; strings, structural substitutes, and caller-selected
aggregate roots deny. `listDirectoryTarget`
permits request limits `1..100`, with <=100 entries, <=200 Markdown lines, and
<=6,000 `spipe-markdown-token-v1@1` tokens; continuation is authenticated and no unbounded
directory projection exists. Authorization's child policy store fsyncs the
initial directory, uses monotonic CAS policy versions and immutable operation
UIDs for policy/key/issuer/rotation/revocation records, and recovers only contiguous durable
state. Mock stores, old `WT-*` fixtures, or in-memory fault-free evidence are
non-admitted; production clean/incremental parity, revision revalidation, and
create/write/fsync/rename/CAS crash evidence are required.

### 21.4 Sealed publication and durable-ledger invariants

`openPublishedAuthorityInventoryV1` recomputes canonical manifest/inventory
digests and proves all fields against the loaded live registry and exact
snapshot, then rereads the same registry and snapshot revisions after inventory
open. Substituted bytes, copied registry records, or revision changes deny
before target lookup.

`AuthorityInventoryPublishPermitV1` is a closure brand owned only by the
KnowledgeCompiler commit root, never data accepted through an adapter. The only
publish ABI is `publishAuthorityInventoryV1({permit, build})`, where `permit`
is minted within the transaction that fixes `registryRevisionId`. That
transaction selects and publishes all-and-only registry-complete,
schema-complete ordered roots, aggregate root, and authority manifest. Readers
reject missing, extra, reordered, substituted, or incomplete roots.

Each directory record commits ordered unique children, ordering version, page
bound, and `tokenBudget`. After `AuthorityManifestV1` and
`TargetInventoryManifestV1` verification, `continuationDomain` is derived but
is never a committed entry, root, digest input, or new grant/cursor field: it
is SHA-256 of canonical `{authorityManifestDigest,targetUid,orderingVersion,
maxPageLimit,tokenBudget}`. Existing signed manifest/target/ordering/limit
claims must rederive the same domain at cursor issuance and verification. Thus
no manifest or inventory digest commits a value depending on itself.
`tokenBudget` fixes `spipe-markdown-token-v1@1`, Unicode 15.1.0, at 6,000
tokens: reject invalid UTF-8, normalize CRLF/bare CR to LF, then split scalar
runs on ASCII `U+0009..U+000D,U+0020`, Unicode-15.1 White_Space
`U+0085,U+00A0,U+1680,U+2000..U+200A,U+2028,U+2029,U+202F,U+205F,U+3000`, and
ASCII punctuation `U+0021..U+002F,U+003A..U+0040,U+005B..U+0060,U+007B..U+007E`.
Listing cannot add/reorder/widen or accept a continuation outside that domain.
Policy persistence is atomic replacement plus file and parent-directory fsync
under cross-process monotonic CAS. Loading validates schemas and only a
contiguous durable operation sequence; equal operation UID/payload replays,
altered payloads and stale CAS fail.

### 21.5 KnowledgeCompiler commit publisher: prerequisite ownership

The reader ports above do not create the production publication they trust.
Current immutable metadata and graph snapshot stores lack one transaction that
materializes complete artifact/section/directory/project/aggregate inventories.
`SnapshotAuthorityPortV1` is therefore non-admitted until parent-owned
`KnowledgeCompilerCommitPublisherV1` exists.

Construct it only at the composition root from branded `WorkspaceRegistryV1`,
`SnapshotStoreV1`, `TargetInventoryStoreV1`, and
`AuthorityPublicationJournalV1`. Its only input is closed
`CommitInputV1 {commitId, workspaceUid, projectUidOrNull, worktreeUid,
revisionId, expectedRegistryRevisionId, expectedBaseSnapshotUidOrNull,
expectedPublicationUidOrNull, inputDeltas}`. Expected IDs are null only for an
initial publication; otherwise the publisher opens that exact prior tuple. The one
transaction normalizes deltas; materializes an immutable base snapshot; fixes
the exact registry revision; materializes sealed project target/section/
directory inventories; derives the registry-complete aggregate; seals the
paired manifests; mints a closure `AuthorityInventoryPublishPermitV1`; then
publishes both scopes through durable revision CAS.

```text
KnowledgeCompilerCommitPublisherV1.commit(CommitInputV1) -> PublishedAuthorityCommitV1
TargetInventoryMaterializerV1.materialize(baseSnapshot, registryRevision, deltas)
  -> ProductionInventoryBuildV1
PublisherPermitIssuerV1.mintForCommit(transaction) -> AuthorityInventoryPublishPermitV1
TargetInventoryStoreV1.publishAuthorityInventoryV1({permit, build})
  -> PublishedAuthorityInventoryV1
AuthorityPublicationJournalV1.recoverAuthorityPublicationV1() -> RecoveryResultV1
```

`ProductionInventoryBuildV1` is private until publication. Its contributor list is
ordered, schema-complete, and all-and-only registry-selected; all content and
directory data precedes sealing. The closure permit cannot be serialized or
provided by adapters. The journal stages immutable objects and the complete
`AuthorityPublicationRecordV1`, fsyncs every staged file and parent directory,
then invokes the sole atomic durable current-pointer revision-CAS. That CAS
does not expose the new head until its pointer write/fsync boundary completes;
`openPublishedAuthorityInventoryV1` observes old or new complete records only.
The pointer contains its publication UID, exact registry/base tuple, ordered
project roots, aggregate root, paired authority snapshot UIDs, and both manifest
digests. Journal-owned recovery validates this state before acknowledgement.
Equal canonical commit replay
is idempotent; changed replay/stale revision fail; recovery exposes old complete
or new complete state only. W5A-18/19/21/22 require real all-kind parity,
forged-permit/contributor/substitution negatives and crash/restart/CAS proof;
authority/projection/cursor claims remain non-admitted before that evidence.

### 21.6 Publisher admission invariants

The rejected publisher is `NON-ADMITTED`; the following are architecture
invariants, not implementation suggestions. `TargetInventoryStoreV1` owns the
non-forgeable publication boundary. It recognizes only the closure brand minted
by `PublisherPermitIssuerV1` inside the composition-root transaction; neither a
public `AuthorityPublicationJournalV1`, `instanceof`, object shape, nor a
caller-selected project/aggregate root can confer authority.

`CommitInputV1` is reduced once to a versioned canonical replay envelope hash
covering `commitId`, exact workspace/project/worktree/revision tuple, expected
registry/base/publication IDs, and normalized deltas. The journal stores this
hash in `AuthorityPublicationRecordV1`; same hash returns the exact durable
result, while changed bytes deny before any write. The record contains the exact
workspace/project/worktree/revision/base-and-authority-snapshot tuple, ordered
project roots, aggregate root, manifest digests, and content hashes for every
journal-owned inventory/manifest object.

`AuthorityPublicationJournalV1` is the sole durable state-machine and recovery
owner: `staging`, `objects_durable`, `record_durable`, `current_cas`, and
`acknowledged`. It writes immutable content-addressed objects and record before
one atomic rename/CAS current pointer, fsyncing files and parent directories;
it recovers stale writer locks and process interruption deterministically.
`openPublishedAuthorityInventoryV1` and recovery deep-verify record schema,
all object hashes, both manifests, project/aggregate roots, exact binding, and
sealed page roots before returning. Once a head exists, reads return only its
complete predecessor or its complete successor—never `null`, staging, or a
partially checked record.

### 21.7 Wave 5 sealed-boundary re-admission order

`KnowledgeCompilerCommitPublisherV1` P2 is the first unresolved authority
boundary. Its closure permit and canonical replay envelope are necessary but
not sufficient: the current candidate is non-admitted because first-use nested
ledger creation can race with `EEXIST`. `AuthorityPublicationJournalV1` must
therefore create/fsync every new ancestor, publish a durable owner receipt,
compare/revalidate the observed stale owner before unlink, and demonstrate
competing-process and SIGKILL recovery. An in-process lock, path-blind unlink,
or test-only scheduler is forbidden evidence.

Only P2's independently reviewed production oracle may feed the second
boundary: `SnapshotAuthorityPortV1.openBoundSnapshot(binding)` creates an opaque
`SnapshotAuthorityViewV1` and closed `ExpectedReadBindingV1` from the exact
published dual-snapshot tuple. It uses real registry/snapshot owners and the
branded `TargetInventoryStoreV1.openPublishedAuthorityInventoryV1` boundary,
deep-verifies roots and manifests, and rejects swapped worktree,
revision, snapshot, instance, manifest, target, or brand before authorization
or `ProjectionPortV1`. A raw manifest, cache, caller map, or structural object
cannot implement this port.

The third boundary is URI/projection: the resolver returns a canonical target
*candidate* only; after sealed membership and real `AuthorizationPortV1`
verification, the composition root compares the entire frozen
`CanonicalReadReceiptV1`/`ExpectedReadBindingV1` before ProjectionPort. Legacy
aliases, including `spipe://skill`, never confer authority. The rejected URI
candidate is not reusable; raw path resolution, local signing, duck-typed
grants, and alias-only output are forbidden.

Cursor, MCP, and materializer adapters are fourth and read-only. They consume
only the admitted closed binding, preserve the sealed bounded directory domain,
and make zero projection calls before admission. Each boundary needs real
production tests, exact-scope review, and an independent highest-capability
PASS; failure leaves all successors `NON-ADMITTED`.

This is an additive boundary order, not a replacement of §21's normative
authority/cursor ABI, raw snapshot APIs, or the exact
`spipe-markdown-token-v1@1` <=6,000 token gate. Rejected cursor work is
forensic evidence only and cannot weaken or delete those contracts.
