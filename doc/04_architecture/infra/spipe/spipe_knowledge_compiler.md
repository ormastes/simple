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
the `ProjectionService` materializer adapter may hold it. The exact
`MaterializerSafeFilesystemPort` API is:

```text
open_view_root(capability) -> SafeViewRoot
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
address a generated-view root or vice versa.

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

### 4.4 Trace authority

Authority and acceptance are independent fields.

| Origin | May be accepted automatically? | Advisory gate | Standard gate | Strict/mission-critical gate |
|---|---:|---:|---:|---:|
| `explicit` | yes, after schema/target validation | yes | yes | yes |
| `generated` | yes, from a named deterministic rule | yes | yes | yes |
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
