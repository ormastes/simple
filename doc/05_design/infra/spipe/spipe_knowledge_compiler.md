<!-- codex-design -->
# SPipe Knowledge Compiler — Integrating Detail Design

**Status:** Implementation-ready integrating design  
**Date:** 2026-08-25  
**Requirements:** `doc/02_requirements/feature/spipe_knowledge_compiler.md`  
**NFRs:** `doc/02_requirements/nfr/spipe_knowledge_compiler.md`  
**Architecture:** `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md`

## 1. Purpose and design boundaries

This document turns the accepted architecture into implementable records,
state machines, service interactions, persistence rules, recovery behavior,
and dependency-wave checklists. It is the integration contract for the SPipe
core, trace/refactor/rebalance/promotion services, and optional Simple
providers.

Two focused designs are normative at their boundaries and are referenced rather
than copied here:

- `spipe_knowledge_compiler_mcp_views.md` owns URI grammar, projection paging,
  MCP resource/tool envelopes, cache hints, legacy/2026 negotiation, and the
  materializer contract.
- `spipe_knowledge_compiler_search_providers.md` owns tokenization, fixed-point
  BM25, RRF/search explanations, provider wire protocol, golden parity, source
  symbols, duplicate-analysis extraction, and the three database adapters.

The lifecycle-first canonical tree remains physical truth. This design creates
no second writable document tree. FUSE/ProjFS remains behind a read-only
`ProjectionAdapter` decision gate and is not an initial deliverable.

## 2. Package and ownership map

```text
Spipe/src/
  application/knowledge_compiler.js     parent orchestration/publication
  model/{identity,artifact,section,edge,diagnostic,snapshot}.js
  parser/{markdown,sdn,sspec,source_metadata}.js
  workspace/{registry,git,worktree,linked_project}.js
  storage/{object_store,manifest_store,alias_store,journal_store}.js
  graph/{store,delta,query,trace_policy}.js
  index/{coordinator,exact,provider_adapter}.js
  view/{projection,materialize}.js       focused MCP/view design
  diagnostics/{identity,links,trace,tree,security}.js
  refactor/{planner,executor,recovery}.js
  rebalance/{graph_builder,community,partition,objective,proposal}.js
  promote/{candidate,score,validation,publish}.js
  skill/{compiler,adapter,verify}.js
  observability/{events,metrics,debug_report}.js
```

`KnowledgeCompiler` alone publishes snapshots. Parsers and analyzers return
immutable deltas. `RefactorExecutor` alone changes canonical files.
`RebalanceService` and `PromotionService` return proposals; they cannot invoke
filesystem writes or publication directly. `AuthorizationPort` wraps all
external reads and mutations. This is an MDSOC virtual capsule: security,
metrics, budgets, and audit receipts are transforms around stable ports, not
logic duplicated in adapters.

Baseline JavaScript remains dependency-free. Simple code lives in the paths
defined by the search-provider design and is reached only through versioned
ports. Existing `cli/spipe.js` and `mcp/server.js` become compatibility
dispatchers after behavior snapshots lock their current contracts.

Implementation dependency order is security-significant: threat model and
trust classification -> identity/schema -> containment-safe storage ->
authorization -> immutable snapshots -> read-only local queries -> MCP stdio ->
authenticated HTTP -> mutation planning -> durable mutation apply -> optional
providers/promotion. HTTP or canonical mutation must not be enabled before the
preceding controls and negative tests pass.

## 3. Core data model

### 3.1 Scalar identities

Opaque IDs use a typed prefix plus 128-bit sortable random payload. Parsers
never synthesize an identity from a path. `SnapshotId` is exactly
`spks1-<lowercase sha256>` over canonical SDN
`snapshot_v1(project_uid, worktree_uid, revision_id, base_generation_hash,
overlay_generation_hash, schema_version, parser_version, analyzer_version,
provider_contract_version, policy_hash)`. Canonical SDN uses the schema-defined
field order, UTF-8, LF, normalized scalar encodings, and no insignificant
whitespace. A clean worktree uses exactly 64 lowercase zero hex characters for
`overlay_generation_hash`; dirty state hashes the normalized overlay manifest.
`revision_id` is always the fully resolved committed/base revision (never a
floating name and never a synthetic dirty revision). For non-VCS content the
registry resolves an immutable base revision before compilation. All dirty
state exists only in `overlay_generation_hash`. Equivalent content in different
worktrees intentionally has different snapshot identity because worktree
isolation is part of the tuple.

| Type | Rule |
|---|---|
| `WorkspaceId`, `ProjectId`, `WorktreeId` | registry-assigned, immutable |
| `ArtifactUid`, `SectionUid`, `EdgeUid` | immutable, never reused |
| `SemanticKey` | normalized dotted name, renameable, alias-retained |
| `RevisionId` | VCS commit or explicit dirty-overlay revision |
| `ContentHash` | SHA-256 over canonical bytes |
| `SchemaVersion` | integer major/minor; incompatible major fails closed |

### 3.1.1 Canonical interface vocabulary

There is one public record name per concept:

- `RefactorPlan` is the sole refactor plan type; `TransactionPlan` is forbidden.
- `DiagnosticRecord` is the sole diagnostic data type; `Diagnostic` is only a
  prose category, never an interface alias.
- `KnowledgeDelta` is the parent publication envelope and contains the sorted
  `ArtifactDelta`, `GraphDelta`, and `IndexDelta` payloads plus alias,
  projection-invalidation, and `DiagnosticRecord` changes.

Internal service boundaries use `*Port` (`LexicalSearchPort`,
`SymbolIndexPort`, `ProjectionPort`, `AuthorizationPort`). External/runtime
implementations use `*Provider` (`SearchProvider`, `SourceSymbolProvider`,
`ProjectionProvider`) and are adapted to exactly one corresponding internal
port. A provider is never injected directly into domain services, and `Port`
and `Provider` suffixes are not interchangeable in schemas, wire messages, or
tests.

During observe-only migration, an unmarked document receives a **provisional
identity** `P-<project-uid>-<content-hash>`, scoped to one snapshot and clearly
flagged `identity_status=provisional`. It enables read/search but cannot be an
accepted strict trace target, mutation target, durable alias target, or
cross-revision identity. A proposed UID injection upgrades it through an
explicit canonical edit; path similarity never upgrades it silently.

Aggregate outputs also have identity without impersonating artifacts.
`ProjectionUid` is exactly lowercase SHA-256 over canonical SDN
`projection_v1(workspace_uid, snapshot_id, view_kind,
normalized_logical_path, normalized_parameters_hash,
effective_auth_scope_hash, page_start_key)`. Generated directories, matrices,
diagnostic reports, search resources, and pages use this formula; aggregate
snapshot reports may additionally use a typed synthetic-node kind but not a
second projection identity formula. Projection UIDs are never artifact UIDs
and cannot receive canonical-file mutation operations.

### 3.2 Artifact and section records

```sdn
artifact:
  uid: A-...
  key: design.search.bm25_core
  project_uid: P-...
  revision: 3b676a1...
  kind: design
  title: Shared BM25 Search Core
  canonical_path: doc/05_design/lib/search/bm25_core.md
  content_hash: sha256:...
  features: [search, project_knowledge]
  components: [std.common.search]
  layers: [index, ranking]
  visibility: project
  trust: reviewed
  status: approved
  aliases: [design.db.bm25]
  parser: {id: markdown, version: 1}

section:
  uid: S-...
  artifact_uid: A-...
  key: design.search.incremental_maintenance
  heading: Incremental Index Maintenance
  ordinal: 7
  source_span: {start_byte: 1840, end_byte: 2611}
  content_hash: sha256:...
  aliases: [incremental-index-maintenance]
```

Arrays serialize in normalized lexical order except source-order fields.
Canonical paths are normalized project-relative POSIX paths even on Windows;
native paths exist only inside the workspace adapter. A managed target section
without a marker is `SPK104` in advisory migration and an error in strict mode.
Duplicate UIDs are always fatal.

### 3.3 Graph records

```sdn
edge:
  uid: E-...
  type: verifies
  from_uid: T-...
  to_uid: R-...
  origin: explicit
  status: accepted
  confidence_milli: 1000
  created_by: principal:alice
  created_at_revision: 3b676a1...
  evidence_uids: [A-...]
  generator: nil
```

Stored direction follows the active-verb table in the architecture. An inverse
query is computed and never materialized as another edge. The store is a
**directed typed multigraph**: distinct provenance/evidence edges between the
same endpoints are preserved. Only the lifecycle progression subgraph is
required to be acyclic; general `links_to`, `depends_on`, `extends`, and
classification relationships may contain cycles. Lifecycle-cycle detection
returns a diagnostic and blocks strict publication. `generated` edges
also store generator ID/version/rule/input snapshot. Inferred edges start as
`proposed`; accepting one records an explicit review event without rewriting
its origin.

### 3.4 Snapshot and delta

```sdn
snapshot_manifest:
  schema: 1
  snapshot_uid: spks1-0123456789abcdef...
  project_revisions: [{project_uid: P-..., revision: ...}]
  base_segments: [sha256:...]
  overlay_segment: sha256:...
  alias_root: sha256:...
  graph_root: sha256:...
  lexical_root: sha256:...
  projection_root: sha256:...
  diagnostics_root: sha256:...
  config_hash: sha256:...
  parser_set_hash: sha256:...
```

`KnowledgeDelta` contains sorted `ArtifactDelta` artifact/section changes,
`GraphDelta` edge changes, and `IndexDelta` lexical changes, plus alias changes,
projection invalidation keys, and `DiagnosticRecord` changes. It names its base
snapshot and all input hashes. Parent
publication rejects a delta whose base, schema, or project revision differs
from the pinned generation.

### 3.5 Diagnostics and results

Every `DiagnosticRecord` has `code`, `severity`, `message_key`, structured
arguments, project/revision/snapshot, optional artifact/span, related UIDs,
remediation, and cause chain. User prose is rendered at the boundary; internal
logic never branches on message text.

Stable error families are:

- `SPK0xx` identity/schema/parse;
- `SPK1xx` links/sections/project resolution;
- `SPK2xx` trace/staleness;
- `SPK3xx` classification;
- `SPK4xx` projection/search/provider;
- `SPK5xx` promotion;
- `SPK6xx` balance;
- `SPK7xx` authorization/path/trust;
- `SPK8xx` transaction/recovery/durability;
- `SPK9xx` protocol/budget/internal invariant.

Public APIs return `Result<T, KnowledgeError>`. Partial search/view results name
every omitted optional capability and can never carry a strict-PASS receipt.

## 4. Storage, locking, and retention

Tracked configuration and identity registries remain under `.spipe/`. Derived
state is ignored. Operational journals are durable but worktree-local:

```text
.spipe/config.sdn
.spipe/projects.sdn
.spipe/artifact_aliases.sdn
.spipe/tag_registry.sdn

.spipecache/objects/sha256/<prefix>/<hash>
.spipecache/shared/<repo-id>/snapshots/<snapshot-id>.sdn
.spipecache/worktrees/<worktree-id>/
  current.sdn
  overlays/<hash>.sdn
  indexes/
  projections/
  locks/writer.lock
  journals/<transaction-id>/{journal.sdn,stage/,receipt.sdn}
  recovery.sdn
.spipe/view/                         generated per-worktree view
```

The Git common-dir identity keys shared immutable objects; canonical Git-dir
identity keys the worktree. Paths alone do not key either. Only one writer may
prepare/publish in a worktree. Readers pin a manifest and need no global lock.
The writer lock contains process identity, boot/session nonce, start time, and
transaction ID; stale-lock takeover requires proof that the owner is absent and
records an audit event.

Committed receipts are retained for 90 days or the latest 100 transactions,
whichever retains more. Rolled-back and recovery-required journals are retained
until explicit acknowledgement plus 90 days. Staged original bytes are removed
only after a committed receipt and recoverable canonical snapshot exist.
Critical policy may extend retention and requires filesystem sync barriers.
Garbage collection walks retained manifests/journals before deleting
content-addressed objects and never runs on a request hot path.

Manifests, cursors, apply tokens, and cache entries bind snapshot ID, principal
or authorization-scope digest, policy version, schema version, and analyzer/
provider version as applicable. Cursors are authenticated opaque envelopes
containing view/query digest, last sort key, page limit, expiry, and these
bindings. A mismatch fails as stale/unauthorized; it never restarts against a
different generation. Authorization filters candidates **before** ranking,
projection aggregation, cache lookup/publication, counts, explanations, or
facets, preventing existence and rank side channels.

## 5. Compilation and incremental update flow

### 5.1 Clean build

1. Resolve and realpath the workspace registry; validate trust and revision.
2. Enumerate canonical roots in bytewise path order, excluding derived/vendor
   paths by policy.
3. Hash bytes and reuse matching parser objects by parser/schema version.
4. Parse changed Markdown, SDN, SSpec, and source metadata concurrently into
   isolated deltas.
5. Resolve UIDs/aliases and reject duplicate or ambiguous identity.
6. Validate typed edge endpoints and authority; retain unresolved references as
   diagnostics, never name-based guesses.
7. Build exact/lexical/graph indexes and affected projection pages.
8. Run deterministic diagnostics and compute the manifest root hash.
9. Atomically publish `current.sdn`; emit one publication event.

Opening canonical inputs uses descriptor-relative, no-follow operations (or the
platform-equivalent handle API), validates each parent and final file identity,
then hashes bytes from the validated handle. A prior `realpath` check alone is
insufficient. Mutation performs the same handle-based containment and verifies
file identity immediately before replace to close symlink-swap/TOCTOU races.

### 5.2 Incremental event

File events are hints, coalesced by canonical path and followed by a bounded
stat/hash read. Rename correlation uses UID, exact hash, Git evidence, bounded
fingerprints, then suggestions; ambiguity stops at a diagnostic. For each
changed artifact the compiler recalculates only its parse object, sections,
outgoing edges, incoming diagnostic effects, lexical postings, dependent trace
checks, and directories containing its classifications. Registry, parser,
schema, analyzer, or authorization-policy version changes invalidate their
declared dependency segment.

Publication is compare-and-swap against the base generation. A conflict causes
one rebase of the delta onto the latest snapshot; a second conflict returns
`SPK901 snapshot_conflict` rather than looping. A property-test oracle performs
a clean rebuild and compares graph roots, indexes, diagnostics, and projections
for every supported mutation sequence.

### 5.3 Request flow

`list`, `read`, `resolve`, `search`, and `trace` resolve workspace context,
authorize, pin one immutable snapshot, execute bounded reads, and release the
pin. They never scan the tree, reread unchanged source, write canonical state,
sleep/retry, or start a subprocess per request. Projection and search specifics
are delegated to their focused designs.

`resolve` and `search` have distinct exact behavior. `resolve` short-circuits on
one authorized exact UID, semantic key, or alias and fails on ambiguity without
running retrieval. `search` pins an authorized exact match at rank 1, then
removes that UID from candidate lists and uses RRF plus bounded adjustments for
the remainder; BM25, graph centrality, semantics, recency, or provider scores
cannot displace the pin. Providers return normalized candidate lists and
evidence only; SPipe owns filtering, exact pinning, RRF, bounded adjustments,
and final UID tie-breaking. A provider can add candidates but cannot set final
rank or bypass pre-filter authorization.

## 6. Trace policy and lifecycle state

### 6.1 Edge authority matrix

Only `status=accepted` is evidence. The minimum accepted origin is:

| Lifecycle obligation | Advisory | Standard | Strict | Mission-critical |
|---|---|---|---|---|
| rationale/evidence -> requirement | any accepted or candidate shown | explicit/generated accepted | explicit/generated accepted | same + trusted immutable evidence |
| design satisfies requirement | candidate may warn only | explicit/generated accepted | explicit/generated accepted | same + approved design revision |
| scenario specifies requirement | candidate may warn only | explicit/generated accepted | explicit/generated accepted | same + signed spec revision |
| source implements requirement/spec | structural candidate allowed | accepted explicit/generated or compiler annotation | explicit/generated accepted | same + trusted compiler snapshot |
| test verifies requirement/spec | candidate may warn only | explicit/generated accepted | explicit/generated accepted | same + immutable signed result |
| run produces passing result | latest result displayed | non-stale accepted result | non-stale accepted result | signed, immutable, policy-approved environment |

Inferred evidence may improve discovery in all profiles but cannot satisfy an
obligation. Advisory reports candidates distinctly; it does not relabel them
accepted. Mission-critical checks also validate signer, test environment,
revision closure, and evidence retention.

### 6.2 Requirement state machine

```text
proposed -> accepted -> designed -> specified -> implemented -> verified
                    \-> superseded
any post-accepted state --dependency change--> stale
stale --new accepted evidence--> prior lifecycle state or verified
```

Transitions are derived from accepted graph evidence; documents do not set a
false later state manually. A source/spec/config hash newer than its result
marks the verification subgraph stale. `TRC231`/`TRC232` are emitted as
compatibility diagnostics from the UID graph and mirrored-path projection.

## 7. Transactional refactoring and recovery

### 7.1 Journal schema

```sdn
transaction:
  uid: TX-...
  worktree_uid: WT-...
  principal: principal:alice
  capability: refactor.apply
  base_snapshot: spks1-0123456789abcdef...
  state: prepared
  durability: normal
  operation: artifact_move
  preconditions: [{path: ..., hash: sha256:..., revision: ...}]
  mutations:
    - {kind: replace, old_path: ..., new_path: ..., before_object: sha256:...,
       after_object: sha256:..., applied: false}
  alias_delta: sha256:...
  expected_snapshot: sha256:...
  validation_profile: strict
```

### 7.2 State transitions

`Planned` is pure and can be discarded. `Prepared` is durable and owns the
writer lock. The executor transitions through `Applying`, `Validating`, and
`Committed`; failure enters `RollingBack` then `RolledBack`. Startup seeing
`Prepared`, `Applying`, or `Validating` enters `RecoveryRequired` before any new
write.

The journal contains durable before-images (or immutable object references
whose reachability is pinned), ordered operation sequence numbers, idempotency
keys, executor/schema versions, lock lease nonce, and a hash chain over every
transition. Replaying an already recorded operation is a no-op only when its
after-hash matches; otherwise recovery fails closed. Journal state and staged
bytes are flushed before `Prepared`; changed files, parent directories, the
manifest, and receipt are flushed in that order before lock release. A process
cannot steal or replay a transaction from another worktree/principal.

Each mutation also records pre/post type, mode, owner/group, ACL, extended
attributes, and platform flags. Policy states which metadata must be preserved,
normalized, or rejected; strict/critical mode rejects an operation when the
platform cannot read, stage, restore, and verify required metadata. Setuid,
security-label, quarantine, and unknown privileged attributes never transfer
implicitly. Rollback uses compare-before-restore: it replaces a current object
only if its identity, bytes, and governed metadata match the recorded applied
state. Concurrent or unknown changes stop recovery for operator resolution
instead of being overwritten.

Before each mutation, source hash/revision and resolved containment are checked
again. Atomic same-filesystem rename/replace is required. A cross-device
canonical move is rejected in normal, strict, and critical refactor modes; it
cannot be represented as an atomic refactor. Copy + metadata verify + explicit
cutover is available only as a separately named, separately approved migration
workflow with downtime/dual-location policy, its own rollback plan, and no
claim of atomicity. Validation reparses the proposed snapshot, checks
collisions/aliases/links and selected trace profile, and publishes only on
success.

Recovery code reads old journal majors through explicit migration adapters.
An unknown or partially migrated journal version is never rewritten in place:
it remains `RecoveryRequired`, preserves before-images, and requires a
compatible recovery binary or authorized export/import. Application upgrade is
blocked while an active journal cannot be recovered. Snapshot/schema migration
creates a new generation beside the old one and atomically switches only after
parity validation; downgrade never consumes newer mutable state optimistically.

Journal migrations are pure old-record -> new-record transforms with golden
fixtures, preserved original bytes, version/checksum validation, and an
idempotent migration receipt. Recovery tests crash after every durability
boundary: lock acquisition, token consumption, before-image write/fsync,
`Prepared`, each rename/replace, file and directory fsync, `Applying`, snapshot
validation, manifest switch, `Committed`, receipt fsync, and lock release. They
also cover partial writes, disk-full, permission loss, revocation epoch change,
concurrent edits, process kill, reboot simulation, and every rollback boundary.
Every case must yield the exact old state, exact new state, or preserved
fail-closed `RecoveryRequired` evidence—never a mixed state reported healthy.

Recovery compares each path against recorded before/after hashes:

- all-before: resume applying or roll back safely;
- prefix-after plus remainder-before: resume or reverse the applied prefix;
- all-after: validate then commit, or roll back;
- any unknown hash: fail closed as `SPK803 recovery_required` and preserve all
  evidence for operator choice.

Rollback restores bytes, permissions, paths, aliases, graph/index manifest,
and verifies exact pre-transaction hashes. It never infers desired state.

## 8. Authorization and trust

Authorization evaluates a deny-wins intersection:

```text
principal capability
  x workspace/project/revision
  x artifact visibility and field mask
  x operation
  x trust and provider policy
  x snapshot/worktree context
```

Capabilities are distinct: `knowledge.read`, `knowledge.search`,
`trace.read`, `refactor.plan`, `refactor.apply`, `tree.propose`,
`tree.apply`, `promotion.propose`, `promotion.waive`, `promotion.publish`,
`skill.generate`, and `admin.recover`. An apply token binds principal, exact plan hash, snapshot,
scope, expiry, authorization-policy epoch, and capability; it cannot authorize
a modified plan. Apply rechecks the current authorization epoch and complete
deny-wins decision immediately before the first mutation and before commit.
Tokens are single-use: a durable consumption receipt binds token ID and plan
hash before mutation. A retry with the same token and plan returns the existing
idempotent receipt; reuse with another plan or after revocation fails closed.

All external URIs decode once, reject encoded traversal/device/absolute paths,
then resolve through registered project identity. Filesystem targets are
realpathed (including symlink/junction parents) and must remain within the
authorized root before content disclosure or mutation. Missing linked projects
fail by project UID/revision and never fall back to a local name.

Retrieved repository prose is untrusted data. Only artifacts in an approved
rule/skill scope may affect agent policy. Cache, explanation, log, embedding,
and materialized-view keys include visibility/authorization scope. Remote
semantic providers require an explicit allowlist; local-only and excluded
content is filtered before serialization.

Prompt-facing values use typed `content`, `metadata`, and `policy` channels.
Repository-controlled bytes can populate only escaped/length-bounded `content`
fields; they cannot set roles, tool names, capabilities, approval tokens,
visibility, trust, provider routing, cache scope, or policy fields. Renderers
escape the target protocol and label source UID/trust. Tests inject instruction
lookalikes, delimiter/encoding tricks, forged capability keys, hostile Markdown/
SDN, and retrieved tool-call text and prove that none changes authorization,
prompt role, tool availability, cache scope, or promotion state.

The HTTP adapter is disabled by default. When enabled it binds loopback unless
an explicit trusted-listener policy names another interface, requires
authenticated principals and TLS outside loopback, validates Host/Origin, uses
an allowlist CORS policy (no credentialed wildcard), rejects session identity
from query parameters, and applies per-principal/workspace rate, concurrency,
request-byte, response-byte, page, query-cost, wall-time, and memory budgets.
Streaming stops on cancellation or budget exhaustion. Stateless does not mean
unauthenticated: every request independently establishes its authorized
workspace/snapshot scope and audit identity.

Trust labels propagate through prompt-facing resources, caches, providers,
promotion, and generated skills. Untrusted content cannot become instructions,
public cache material, remote-provider input, promotion evidence, or generated
skill policy merely because it ranked highly. Promotion requires the trust of
each source and reviewer to meet the destination policy; downgrading visibility
or raising trust is a separately authorized, audited decision.

## 9. Rebalancing design

`TreeAudit` computes depth, fanout, direct-count, entropy, trace splits, and
protected-path metrics. `GraphBuilder` collapses must-link groups, adds sparse
weighted explicit/trace/cohesion/co-change/lexical/optional-semantic edges, and
enforces cannot-link project/trust/lifecycle constraints.

The deterministic pipeline is:

1. sort nodes/edges by UID and quantize every weight to integer milli-units;
2. find connected Leiden communities using a seed derived from snapshot and
   configuration hashes;
3. subdivide oversized communities with balanced multilevel k-way partition;
4. merge undersized groups by least objective increase;
5. perform bounded local moves/swaps in UID order;
6. retain stable cluster UIDs by maximum-overlap matching with deterministic
   tie-breaks;
7. label from controlled taxonomy and representative terms;
8. enforce hysteresis, cooldown, confidence, and minimum improvement;
9. emit a signed/hash-bound proposal, never canonical writes.

`RebalanceService` has one deterministic owner per snapshot/scope/config and
rejects competing publication. Randomized algorithms receive only the recorded
seed; weights/objective arithmetic use fixed-width integer milli-units, stable
overflow checks, UID tie-breaking, and no platform floating-point decisions.
Configuration sets maximum nodes, edges per node, total edges, partitions,
iterations, local moves, memory bytes, and wall time. Candidate construction is
sparse and deterministic. If Leiden/partition capability is absent or a budget
is reached, the service returns an explained audit-only/partial proposal using
deterministic connected components and greedy bounded grouping; it never calls
the partial result an approved physical plan. Inputs beyond hard bounds fail
with `budget_exceeded` and leave the prior virtual tree unchanged.

Objective terms and proposal fields follow the architecture/research. Default
thresholds begin at 15% improvement, confidence 0.85, two stable snapshots,
and no strict trace or protected-path violation, but Wave 0 calibrates and
records the released values in `.spipe/config.sdn`. Virtual projections may
accept deterministic proposals automatically. Physical application requires
`tree.apply` and executes only as a `RefactorPlan` with rollback mapping.

## 10. Common-knowledge promotion and skill compilation

Candidate generation is sparse: normalized exact hash, shingle bucket,
MinHash/SimHash, BM25, structural/trace-role evidence, then optional semantic
and LLM review. Every candidate stores contributing scores, source project UIDs
and revisions, excerpts by content hash, visibility/trust, conflicts,
specificity penalty, proposed scope, and validation obligations.

Before review or publication, deterministic secret, credential, private-key,
high-entropy token, personal-data-policy, license/SPDX, copyright, and provenance
scanners run on source and generalized output. A secret or prohibited-license
finding blocks publication and remote semantic/LLM transfer. False-positive or
policy-exception waiver requires a separate `promotion.waive` capability and a
signed receipt naming finding fingerprint, scope, rationale, approver, expiry,
and destination policy; waivers cannot suppress newly changed content. The
audit record retains scanner IDs/versions/rule digests, findings, redactions,
waivers, reviewers, validation results, exact source/output hashes, and publish/
rollback receipts without logging secret bytes.

`proposed -> reviewed -> validating -> approved -> published` is the only
publish path; rejection is terminal but may be superseded by a new candidate.
Normal common promotion requires two independently configured projects. An
expert exception records principal, capability, rationale, and review receipt.
Publication produces `promoted_from` provenance and project `extends` edges;
local overrides preserve project constraints. Any consuming-project validation
failure returns the proposal to reviewed state and does not publish.

The skill compiler reads canonical `skill_src`, resolves approved common and
project extensions, and emits harness adapters in deterministic UID order.
Every output header contains source UID, generator version, input snapshot,
`trust_scope`, and content hash. `skill check` regenerates in memory and byte-compares; stale or
hand-diverged output fails verification. Generated outputs are never edited as
canonical sources.

The tracked compiler manifest is concrete and exhaustive:

```sdn
skill_compiler:
  schema: 1
  generator: {id: spipe.skill.compiler, version: 1}
  source_roots: [skill_src/common, skill_src/phases, skill_src/domains,
                 skill_src/tools]
  targets:
    - {harness: claude, root: .claude, kinds: [skills, agents]}
    - {harness: codex, root: .codex, kinds: [skills, commands]}
    - {harness: gemini, root: .gemini, kinds: [commands]}
    - {harness: agents, root: .agents, kinds: [skills]}
  outputs:
    - source_uid: K-...
      adapter: codex_skill_v1
      target: .codex/skills/example/SKILL.md
      semantic_fixture: test/fixture/skill/example.canonical.sdn
      trust_scope: approved_project_policy
      content_hash: sha256:...
```

Every generated path under `.claude/`, `.codex/`, `.gemini/`, and `.agents/`
must appear exactly once; the compiler rejects undeclared outputs, collisions,
path escape, and missing harness targets. Each adapter has a semantic fixture
that normalizes the generated surface back to canonical instruction, tool,
phase, and constraint records. Tests compare normalized semantics—not merely
bytes—across all declared targets, while target-specific golden fixtures cover
syntax and metadata. `skill check` verifies manifest completeness, recomputes
source/input/output hashes, regenerates every target in memory, byte-compares
target output, runs every semantic-equivalence fixture, and reports stale,
missing, extra, hand-edited, or semantically divergent files as release-blocking
diagnostics. A target may be marked unsupported only by an explicit manifest
policy and acceptance-criteria revision, never by silent omission.

## 11. Observability and budgets

Structured events carry operation ID, snapshot, project/worktree, duration,
outcome/error code, counts, cache class, provider/capability, and authorization
scope hash—never document content, credentials, or private query text.

Required histograms/counters include startup stages; snapshot pin lifetime;
parsed/reused artifacts; delta size/publication conflict; exact/BM25/graph/
semantic candidate counts; provider handshake/call/timeout/fallback; cache
hit/miss/eviction by safe scope; projection page size; authorization denial;
journal transition/recovery; stale trace count; rebalance cost/moves; promotion
conflicts; and materialized files written/skipped.

`spipe debug-report` emits configuration/provider/schema digests, generation,
safe counters, active diagnostics, and recovery state without content. It uses
the same bounded output/cursor contract as views.

The architecture's absolute figures—warm startup 250 ms P95, exact read/resolve
20 ms, 50k-artifact lexical search 100 ms, list page 50 ms, and one-document
update 100 ms—are **qualification candidates**, not release budgets, until Wave
0 locks the benchmark profile and records the resulting approved targets.
NFR-SPKC-014's “at least 20x cheaper” metric
is **warm elapsed wall-clock duration**: on the same quiescent machine and
fixture, after identical warmup, compare **median** elapsed time for one
supported single-document incremental update with median elapsed time for a
clean full rebuild of the resulting canonical state;
`full_rebuild_median / incremental_update_median >= 20.0`. Both samples use the
same process/provider mode, filesystem-cache policy, corpus revision, and at
least the Wave-0 recorded sample count; correctness parity must pass before
timing counts. P95 elapsed time, CPU time, and maximum RSS are recorded as
diagnostics and regression context, but do not substitute for or alter the
normative median ratio. Wave 0 records hardware, corpus, command, sample count,
warmup, median/P95/CPU/max RSS, and raw evidence path. Targets may change only
by an explicit requirement/design revision, never silently during
implementation.

## 12. Migration and compatibility

1. **Observe:** snapshot current CLI/MCP/link/doctor bytes and inventory without
   canonical writes.
2. **Identity:** add artifact UIDs to high-value documents; warn on unmarked
   ordinary sections and require markers only when managed/trace-critical.
3. **Graph/search:** build read-only deterministic graph, diagnostics, exact and
   JS BM25 fallback.
4. **Views:** expose MCP resources/tools and `.spipe/view/`; retain canonical
   paths and legacy stdio.
5. **Trace:** import requirement IDs, `@cover`, SSpec/manual mirrors, and
   TRC231/TRC232 into UID-backed edges.
6. **Refactor:** enable plan/apply, CI gates, recovery, and alias-backed link
   migration before any physical move.
7. **Optimize:** introduce Simple providers and DB adapters only after golden
   protocol parity.
8. **Organize/promote:** calibrate virtual rebalancing, then small approved
   physical proposals and reviewed knowledge promotion.

Each stage is reversible, has a clean-build/incremental parity fixture, and
does not require moving the canonical tree. Old commands call new services with
compatibility serializers. Unknown MCP versions and provider semantic versions
fail explicitly. OS mounts advance only if named clients cannot meet their
acceptance criteria with MCP, materialization, or editor views and a security/
maintenance review accepts the adapter.

## 13. Dependency-wave implementation checklists

### Wave 0 — Baseline and contracts

- [ ] Lock current CLI, setup/link, doctor, MCP, trace, and generated-manual
  behavior fixtures.
- [ ] Publish schema/port/error vocabularies and representative corpora.
- [ ] Record hardware, startup, scan, search, duplicate, and RSS baselines.
- [ ] Verify linked-project and divergent-worktree fixtures exist.
- **Gate:** ownership and compatibility evidence is reviewed; no product code
  fans out before shared interface names freeze.

### Wave 1 — Dependency-free modular core

- [ ] Extract dispatcher, configuration, workspace, serializers, and protocol
  adapters without behavior change.
- [ ] Implement deterministic SDN/JSON result and error serialization.
- [ ] Keep Node baseline dependency-free.
- **Gate:** byte-compatible fixtures pass and monolith entry files only route.

### Wave 2 — Identity, parsing, storage, workspace

- [ ] Implement schemas, parsers, UID marker proposal, registry, object store,
  manifests, worktree isolation, locks, and inventory diagnostics.
- [ ] Add clean/incremental property fixtures for add/update/delete/move.
- **Gate:** deterministic round trip, no path-derived identity, no dirty-state
  leakage, and duplicate/ambiguous identity fail correctly.

### Wave 3 — Graph, trace foundation, diagnostics

- [ ] Implement typed edges, reverse query index, authority/status, link and
  trace diagnostics, trace matrix, and TRC compatibility projection.
- [ ] Make snapshot publication atomic and request pinning generation-safe.
- **Gate:** graph root equals clean rebuild; inferred edges cannot satisfy
  strict checks.

### Wave 4 — Search/provider foundation

- [ ] Implement exact/alias and fallback BM25; freeze provider handshake and
  golden corpus; migrate common Simple surfaces per focused design.
- [ ] Migrate DBFS scoring to the canonical common scorer while preserving old
  DBFS entry points as compatibility facades; prove old-call-shape behavior and
  new score/order parity on shared fixtures before removing any legacy path.
- [ ] Add explanation and exhaustive top-k parity tests.
- **Gate:** JS/Simple ordering, score, deletion, phrase, and explanation parity;
  provider failure degrades explicitly.

### Wave 5 — Views and MCP

- [ ] Implement URI resolver, all required projections, bounded pages,
  resources/tools, legacy stdio, negotiated MCP 2026, cache scope, and
  materialization.
- **Gate:** every virtual file resolves one UID; write attempts fail closed;
  authorized clients see equivalent deterministic content.

### Wave 6 — Refactoring

- [ ] Implement plan/apply tokens, journal, same-filesystem staging, executor,
  validation, startup recovery, rollback, raw-change suggestions, and CI hooks.
- **Gate:** fault injection at every state proves old/new valid state or
  preserved fail-closed recovery; UID/trace/aliases survive rename/move.

### Wave 7 — Full trace and phase contracts

- [ ] Add source-symbol provider, SSpec/test/run/result nodes, lifecycle states,
  stale closure, policy profiles, phase UID exchange, and candidate review.
- **Gate:** selected research-to-result chains pass; strict ignores inferred
  evidence; linked projects/worktrees diagnose safely.

### Wave 8 — Rebalancing

- [ ] Implement audit, sparse graph, connected communities, balanced partition,
  local refinement, stable IDs/labels, proposal and refactor conversion.
- **Gate:** hard constraints hold, unchanged input is byte-identical/no-churn,
  communities are connected, and physical change needs approval.

### Wave 9 — Promotion and skill compiler

- [ ] Implement fingerprints/candidate cascade, conflict review, validation,
  provenance/extends/overrides, canonical skill source, adapters, and freshness
  verification.
- **Gate:** no unauthorized publication, all consumers validate, generated
  harness surfaces are byte-current, and project constraints remain.

### Wave 10 — Database/server and optional semantics

- [ ] Complete textual, embedded/DBFS, and server adapters; WAND/Block-Max WAND,
  tenancy/capability/cancellation, optional ANN and safe semantic policy.
- **Gate:** snapshot/transaction/auth semantics hold per tier, optimized top-k
  equals exhaustive, and semantic outage retains exact/BM25/graph behavior.

### Wave 11 — Optional OS mount decision

- [ ] Collect named-client failure evidence and compare MCP/materialized/editor
  alternatives; design read-only containment/invalidation if justified.
- **Gate:** no implementation without an approved ADR, security review,
  maintenance owner, and acceptance tests.

## 14. Verification and delivery contract

Executable system scenarios and their manual presentation are owned by the
system-test plan. The integrating design requires the shared helper names from
the feature state: `setup_spipe_knowledge_fixture`,
`check_spipe_knowledge_compiler`, `check_spipe_provider_parity`,
`check_spipe_refactor_recovery`, and `check_spipe_virtual_view_safety`.
Primary manual steps remain: “Index canonical knowledge artifacts”, “Browse
virtual knowledge views”, “Search and trace artifacts”, “Apply a transactional
refactor”, and “Audit tree balance and promotion candidates”. Any unfinished
oracle must fail explicitly; no placeholder assertion can satisfy trace.

Each wave commits only its owned files after focused checks. Final verification
also runs applicable runtime-facade audits, Simple compiler/lib/MCP/LSP checks,
MCP integration and native/package smoke gates, confirms there are zero `.spl`
specs under `doc/06_spec`, and performs at most three distinct verify/fix
cycles. A higher-capability reviewer audits sidecar exclusions, security,
manual quality, and every AC before release/sync.

## 15. Requirement and NFR trace

| Design area | Feature requirements | NFRs | Primary evidence |
|---|---|---|---|
| Canonical records, parsing, snapshots | 001–005 | 001–003, 009–010, 022–023 | schema golden files; clean/incremental property tests |
| Virtual views and MCP | 006–010, 026–027, 030 | 004–006, 011, 016, 019 | protocol fixtures; bounded view/manual scenarios |
| Search/providers/databases/symbols | 011–016 | 002–003, 006–007, 012–016, 022 | golden provider corpus; DB tier and performance evidence |
| Trace policy and diagnostics | 003, 017–018, 028 | 001–003, 010, 020–021 | profile matrix; stale/link/TRC scenarios |
| Transaction/refactor/recovery | 002, 019–020, 029 | 004–005, 008–010, 021, 023, 025 | phase fault injection; exact rollback hash equality |
| Rebalancing | 006, 021–022, 029 | 001–002, 017, 021, 023, 025 | constraint properties; deterministic no-churn snapshots |
| Promotion and skill compilation | 023–025, 028–029 | 001, 006–007, 018, 020–025 | provenance/conflict/consumer validation; byte freshness |
| Compatibility, migration, delivery | 026–030 | 003, 016, 019–025 | baseline compatibility, stage rollback, final AC audit |

All REQ-SPKC-001–030 and NFR-SPKC-001–025 have a design owner and named
evidence above. Focused designs refine their rows but may not weaken these
integration invariants. If an implementation discovery changes a contract,
requirements and architecture are revised before code adopts the change.
