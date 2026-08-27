<!-- codex-design -->
# SPipe Knowledge Compiler — Integrating Detail Design

**UI design:** N/A. This feature exposes CLI, MCP, library, and generated
read-only filesystem surfaces; it has no independent TUI or GUI in scope.
Protocol interaction and virtual-directory presentation are specified in the
MCP-view detail design rather than separate `_tui`/`_gui` artifacts.

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
- `spipe_knowledge_compiler_cooperative_streaming.md` owns raw-byte framing,
  iterative canonical JSON/emission, incremental SHA, streaming UCD analysis,
  request budget/checkpoint/cancel admission, the single-owner provider
  reactor, cross-platform process statistics, and its migration gates.

At their integration boundary, protocol-1.0 semantic deadlines are the
inclusive 1..30,000 millisecond interval measured from the first accepted
frame-header byte. `invalid_utf8` and `frame_too_large` remain payload-free
local `TransportDiagnosticV1` classes and silently close before binding; they
are not `ProviderErrorV1` codes and cannot be routed through a named operation.
The search-provider detail owns bound response/error schemas while the focused
streaming design owns byte-stream diagnosis and deadline enforcement.

The lifecycle-first canonical tree remains physical truth. This design creates
no second writable document tree. FUSE/ProjFS remains behind a read-only
`ProjectionProvider` decision gate and is not an initial deliverable.

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
immutable deltas. `RefactorService` alone holds the refactor filesystem
capability and authorizes canonical-file mutations.
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
| `RevisionId` | fully resolved committed/base revision, or registry-resolved immutable base for non-VCS; never a dirty-overlay revision—every dirty byte contributes only to `overlay_generation_hash` |
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

The frozen search/symbol/projection vocabulary is closed. Internal boundaries
are only `LexicalSearchPort`, `SemanticSearchPort`, `SymbolIndexPort`, and
`ProjectionPort`. External/runtime implementations are only `SearchProvider`,
`SourceSymbolProvider`, and `ProjectionProvider`. `SearchProvider` capabilities
adapt to `LexicalSearchPort` and, when declared, `SemanticSearchPort`;
`SourceSymbolProvider` adapts to `SymbolIndexPort`; `ProjectionProvider` adapts
to `ProjectionPort`. Names such as `SearchProviderPort`, `JsSearchProvider`,
`LexicalIndexPort`, `SemanticProvider`, and `ProjectionAdapter` are forbidden
aliases. The dependency-free JavaScript implementation is a `SearchProvider`
with implementation ID `spipe_js`, hosted behind
`InProcessSearchProviderAdapter`. `KnowledgeCompiler` receives only the
adapter-produced `LexicalSearchPort` and optional `SemanticSearchPort`; it never
receives or discovers a `SearchProvider`. External providers likewise terminate
at their adapter before domain injection. `Port`/`Provider` suffixes are not
interchangeable in schemas, wire messages, or tests. Other domain
ports such as `AuthorizationPort` retain their architecture-defined names.

During observe-only migration, an unmarked document receives a **provisional
identity** `P-<project-uid>-<content-hash>`, scoped to one snapshot and clearly
flagged `identity_status=provisional`. It enables read/search but cannot be an
accepted strict trace target, mutation target, durable alias target, or
cross-revision identity. A proposed UID injection upgrades it through an
explicit canonical edit; path similarity never upgrades it silently.

Aggregate outputs also have identity without impersonating artifacts.
`ProjectionUid` presents as `spkp1-<lowercase sha256>`, where the digest is over canonical SDN
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

Wave 3 canonical records are closed schemas; unknown fields fail validation:

```text
GraphNode = {uid:Uid, node_kind:NodeKind, project_uid:ProjectUid|null,
             revision_id:NonEmptyString|null, record_type:RecordType,
             record_hash:Sha256, visibility:Visibility,
             trust_scope:TrustScope, status:NodeStatus}
RequirementRecord = {type:"requirement"|"non_functional_requirement",
 uid:RequirementUid|NfrUid, kind:"requirement"|"nfr", key:SemanticKey,
 display_id:DisplayId, project_uid:ProjectUid, revision_id:NonEmptyString,
 artifact_uid:ArtifactUid, section_uid:SectionUid, title:NonEmptyString,
 status:RequirementStatus, content_hash:Sha256, aliases:list<SemanticKey>}
SSpecScenarioRecord = {type:"sspec_scenario", uid:ScenarioUid,
 key:SemanticKey, project_uid:ProjectUid, revision_id:NonEmptyString,
 artifact_uid:ArtifactUid, title:NonEmptyString, ordinal:u32,
 source_location:SourceLocation, content_hash:Sha256,
 requirement_uids:list<RequirementUid|NfrUid>, status:ScenarioStatus}
SourceSymbolRecord = {type:"source_symbol", uid:SourceSymbolUid,
 project_uid:ProjectUid, revision_id:NonEmptyString,
 canonical_path:CanonicalRelativePath, symbol_kind:SymbolKind,
 name:NonEmptyString, qualified_name:NonEmptyString, signature_hash:Sha256|null,
 source_location:SourceLocation, content_hash:Sha256,
 annotation_uids:list<RequirementUid|NfrUid|ScenarioUid>, status:SymbolStatus}
TestRecord = {type:"test", uid:TestUid,
 test_kind:"unit"|"integration"|"system", project_uid:ProjectUid,
 revision_id:NonEmptyString, artifact_uid:ArtifactUid,
 scenario_uid:ScenarioUid|null, title:NonEmptyString, source_location:SourceLocation,
 content_hash:Sha256, verifies_uids:list<Uid>, status:TestStatus}
ClassificationRecord = {type:"classification", uid:ClassificationUid,
 classification_kind:"feature"|"component"|"layer"|"tag",
 key:SemanticKey, workspace_uid:WorkspaceUid,
 project_uid:ProjectUid|null, source_hash:Sha256, status:"active"}
IdentityMigrationRecord = {type:"identity_migration", old_uid:LegacyWUid,
 old_record_type:"workspace"|"worktree", new_uid:WorkspaceUid|WorktreeUid,
 migrated_in_snapshot_uid:SnapshotUid}
```

All fields are required unless `|null` is shown; arrays default to `[]` and no
other defaults exist. Strings are UTF-8 NFC; hashes are lowercase `sha256:`
plus 64 hex digits. Derived UID types require their exact prefix and 26
uppercase Crockford base32 payload characters under the architecture encoding;
Wave 3 adds `AL`, `M`, `RQ`, `NFR`, `SS`, `SY`, `WS`, `WT`, `F`, `C`, `L`,
`TG`, and `T` to the
identity prefix registry. `SourceSpan={start_byte:u64,end_byte:u64}` and
`SourceLocation={source_artifact_uid:ArtifactUid,source_hash:Sha256,
span:SourceSpan}`. Wave 3 retains the Wave 2 parser-byte contract: without
character normalization, replace every CRLF byte pair with LF and then every
remaining CR byte with LF. `source_hash` is the containing ArtifactRecord
`content_hash`, SHA-256 of that normalized UTF-8 byte stream. Spans index those
normalized bytes, not checkout/raw-object bytes; offsets are zero-based and
half-open and boundaries lie on UTF-8 code-point boundaries. Raw-to-normalized
offset maps are derived display data and never enter graph hashes.
`start_byte <= end_byte`; `ordinal` is `0..4294967295`. Semantic keys match
`[a-z0-9]+(?:[._-][a-z0-9]+)*`; lists are duplicate-free and bytewise sorted.
`RequirementStatus={proposed,accepted,designed,specified,implemented,verified,
superseded,stale,deprecated}`,
`ScenarioStatus={candidate,proposed,accepted,deprecated}`, and
`SymbolStatus={candidate,accepted,deprecated}`; `TestStatus={candidate,
accepted,deprecated}`. `SymbolKind={module,type,function,method,constructor,
field,constant,trait,interface,enum,variant}`; unknown kinds fail the negotiated
provider schema version.
For requirements, `type=requirement` requires `kind=requirement` and `RQ-`,
while `type=non_functional_requirement` requires `kind=nfr` and `NFR-`.
For migrations, `old_record_type=workspace` requires `WS-`; `worktree`
requires `WT-`. `migrated_in_snapshot_uid` is the first published schema-v2
snapshot containing the mapping; it is audit metadata and not part of UID
derivation. Re-publication copies the retained first value. Two independent
migrations need identical UID mappings, not identical publication snapshot
IDs. `DisplayId` matches
`(?:REQ|NFR)-[A-Z0-9]+(?:-[A-Z0-9]+)+`.

Owner validation is an equality chain, not projection guidance. Requirement/NFR
`artifact_uid` resolves to an artifact with the same project/revision, and
`section_uid` resolves to a section whose `artifact_uid` is that artifact.
Scenario and Test `artifact_uid` equals `source_location.source_artifact_uid`,
and their project/revision equals that artifact. For SourceSymbol, resolving
`source_location.source_artifact_uid` yields an artifact with equal
project/revision and `canonical_path`. Any mismatch is `SPK004
source_owner_mismatch`; the record and all outgoing edges are excluded.

`Visibility={public,project,restricted,private}` and
`TrustScope={untrusted_data,reviewed_reference,executable_policy}` exactly match
Wave 2. `NodeStatus` is the union
`{candidate,proposed,accepted,deprecated,active,unavailable,draft,approved,
designed,specified,implemented,verified,superseded,stale}`. Projection copies the source status verbatim;
alias/mount projections use `active`, with no lossy mapping.
`NodeKind` is exactly the Wave 3 architecture list. Existing registry kinds use
their accepted Wave 2 closed schemas; the records above add trace kinds.

`NodeKind={Workspace,Worktree,Project,ProjectRelation,Mount,Alias,Artifact,
Section,Requirement,NonFunctionalRequirement,SSpecScenario,SourceSymbol,
UnitTest,IntegrationTest,SystemTest,Feature,Component,Layer,Tag}`.
`RecordType={workspace,worktree,project,project_relation,mount_projection,
alias_projection,artifact,section,requirement,non_functional_requirement,
sspec_scenario,source_symbol,test,classification}`. A classification record
always projects with `record_type=classification`; its `classification_kind`
selects the Feature/Component/Layer/Tag `node_kind`.

Registry projections use this closed mapping:

| Record | project/revision | visibility | trust scope | status |
|---|---|---|---|---|
| Workspace | `null/null` | `private` | least-trusted registered project; empty is `untrusted_data` | `active` |
| Worktree | registered project / worktree revision | `project` | workspace minimum | `active` |
| Project | project UID / nullable project revision | project visibility or `project` | project trust scope | project status |
| ProjectRelation | from-project / nullable relation revision | `project` | trusted/reviewed→`reviewed_reference`; untrusted→`untrusted_data` | `active` |
| Alias projection | target project/revision | target visibility | target trust scope | `active` |
| Mount projection | target project / nullable relation revision | `project` | relation mapping | `active` |
| Artifact | owning project / artifact revision | artifact visibility | artifact trust scope | artifact status |
| Section | owning artifact project/revision | owning artifact visibility | owning artifact trust scope | `candidate` if provisional, otherwise owning artifact status |
| Requirement/Scenario/Symbol/Test | owning project / record revision | owning artifact visibility | minimum artifact/source trust | record status |
| Feature/Component/Layer/Tag | classification project or null / null | `project` | minimum trust of referring artifacts, empty is `untrusted_data` | `active` |

Missing nullable values remain null and are never fabricated.
Classification prefixes are feature=`F`, component=`C`, layer=`L`, tag=`TG`.
Their UID payload is the first 26 uppercase Crockford characters of SHA-256
over UTF-8 `spipe-classification-v1\0` followed by canonical JSON
`[workspace_uid,project_uid-or-null,classification_kind,key]`; collisions are
fatal. `source_hash` hashes the sorted referring artifact UID/hash pairs, so
clean and incremental construction produce the same record.

Requirement keys are normalized lowercase semantic keys; `display_id` is the
readable uppercase label. Markdown uses this exact grammar:

```markdown
## REQ-SPKC-003 — Typed graph snapshots
<!-- spipe:section uid=S-... key=req-spkc-003 -->
<!-- spipe:requirement uid=RQ-... key=req-spkc-003 display_id=REQ-SPKC-003 status=accepted aliases=none -->

## NFR-SPKC-002 — Deterministic rebuilds
<!-- spipe:section uid=S-... key=nfr-spkc-002 -->
<!-- spipe:nfr uid=NFR-... key=nfr-spkc-002 display_id=NFR-SPKC-002 status=accepted aliases=none -->
```

An SSpec declaration has one adjacent marker block: optional `# spipe:scenario
uid=SS-... key=<lowercase-key> status=candidate|proposed|accepted
requires=RQ-...,NFR-...` first, optional `# spipe:test ...` second, then the
`it` declaration with no blank/comment lines. At least one marker is present;
each kind appears at most once. A source marker is `# spipe:symbol uid=SY-...
status=candidate|accepted|deprecated implements=RQ-...,SS-...` immediately
before its declaration. The test marker is `# spipe:test uid=T-...
kind=unit|integration|system status=candidate|accepted|deprecated
scenario=SS-...|none verifies=RQ-...,NFR-...,SS-...,SY-...`. In a dual block,
its scenario UID must equal the preceding scenario marker; in a test-only block
`scenario=none` is required;
test UIDs are author-assigned canonical identities and never path-derived.
Unmarked tests are candidates without graph identity until dry-run marker
injection is approved. Scenario/test `title` is the exact UTF-8 NFC-normalized
display string parsed from that next declaration; scenario `ordinal` is its
zero-based position among declarations in the containing artifact. The test
`scenario_uid` is the explicit marker value (`none` becomes null) and, when
present, must name the immediately enclosing marked scenario. Parsers bind
exactly the next declaration, reject unknown or
duplicate attributes and UIDs, and resolve aliases before storing targets.
Markerless or ambiguous records remain candidates, never strict evidence.

Record construction is exact:

- A requirement heading must be ATX level 2 with decoded text exactly
  `<DISPLAY_ID> — <non-empty title>` (one space, Unicode em dash, one space).
  The section marker is the next line and the requirement/NFR marker the line
  after it; the marker also carries `aliases=none|<comma-separated sorted
  SemanticKey list>`. Project, revision, and artifact come from the containing
  `ArtifactRecord`; section UID and normalized section-body `content_hash` come
  from its accepted `SectionRecord`; title is the NFC title substring after the
  delimiter. No heading-label stripping beyond this grammar is permitted.
- Scenario and Test markers bind only the next parsed SSpec `it "<title>":`
  declaration. Their `SourceLocation.span` is the half-open normalized-byte range
  from the `i` in `it` through the declaration suite, excluding the next
  sibling declaration; `content_hash` is SHA-256 of exactly that slice.
  Project/revision/artifact come from the containing artifact.
  `SourceLocation.source_hash` is always the containing ArtifactRecord's
  required normalized `content_hash`, never its nullable provenance
  `source_hash`. Missing normalized bytes or a hash mismatch makes the record a
  candidate diagnostic and cannot produce a canonical node.
- A symbol marker binds only a `SourceSymbolProvider` result whose definition
  begins at the next non-comment token. The provider supplies versioned
  `symbol_kind`, NFC `name`, fully qualified NFC `qualified_name`, and the
  half-open normalized-parser-byte definition span. The provider request carries
  `coordinate_system="spipe-normalized-utf8-bytes-v1"`, the exact normalized
  UTF-8 bytes, and their ArtifactRecord `content_hash`; the response repeats the
  coordinate system and hash. Only zero-based half-open UTF-8 byte offsets are
  supported. Raw-file bytes, UTF-16 units, Unicode scalar/code-point indexes,
  line/column pairs, or a mismatched hash/version fail with `SPK406
  provider_coordinate_contract` before record construction; adapters never
  guess or translate. `signature_hash` is SHA-256 of UTF-8
  `spipe-symbol-signature-v1\0` plus the provider's canonical signature string,
  or null only for module symbols. `canonical_path`, project, revision,
  artifact come from the containing source artifact, and source hash is that
  artifact's required `content_hash`. Text-only
  fallback may emit a candidate diagnostic but never a canonical symbol.

All marker attribute lists use ASCII comma with no whitespace, `none` for an
empty list, and bytewise ascending canonical values. Invalid grammar emits
`SPK003 marker_invalid` and no canonical record. Clean and incremental parsers
invoke this same constructor over the same artifact bytes and SectionRecords.

```text
EdgeRecord = {schema_version:2, type:"edge", uid:EdgeUid, edge_type:EdgeType,
 from_uid:Uid, to_uid:Uid, origin:EdgeOrigin, status:EdgeStatus,
 confidence_milli:u16, created_by:PrincipalId,
 created_at_revision:NonEmptyString, evidence_uids:list<Uid>,
 generator:GeneratorEvidence|null, provenance:EdgeProvenance,
 authority:EdgeAuthority|null}
EdgeProvenance = {project_uid:ProjectUid, worktree_uid:WorktreeUid,
 revision_id:NonEmptyString, input_snapshot_uid:SnapshotUid,
 source_uid:Uid|null, source_location:SourceLocation|null,
 decision_uid:DecisionUid|null}
EdgeAuthority = {kind:"explicit_review"|"trusted_generator",
 receipt_uid:DecisionUid, policy_hash:Sha256, policy_version:u32}
GeneratorEvidence = {generator_id:NonEmptyString, version:NonEmptyString,
 rule:NonEmptyString, input_snapshot_uid:SnapshotUid}
```

`EdgeType` is exactly the stored-edge list in architecture section 4.5.
`EdgeOrigin={explicit,generated,structural,lexical_inference,
semantic_inference,llm_inference}`; `EdgeStatus={accepted,proposed,rejected,
stale,superseded}` exactly preserves Wave 2; `confidence_milli` is `0..1000`.

The Wave 3 endpoint-kind table is closed (`Test` means any of the three test
kinds, `Classification` means Feature/Component/Layer/Tag, and `Any` means any
admitted Wave 3 kind):

| Edge type | From kinds | To kinds |
|---|---|---|
| contains | Workspace, Worktree, Project, Artifact, Section | Any except Workspace/Worktree |
| classifies | Artifact, Section | Classification |
| evidence_for, derives | Artifact, Section | Artifact, Section, Requirement, NonFunctionalRequirement |
| satisfies, realizes | Artifact, Section, SourceSymbol | Requirement, NonFunctionalRequirement, Artifact, Section, Component |
| schedules | Artifact, Section | Requirement, NonFunctionalRequirement, SSpecScenario, SourceSymbol, Test |
| specifies | SSpecScenario | Requirement, NonFunctionalRequirement |
| implements | SourceSymbol | Requirement, NonFunctionalRequirement, SSpecScenario, Artifact, Section |
| verifies | Test | Requirement, NonFunctionalRequirement, SSpecScenario, SourceSymbol |
| covers | Test | SourceSymbol, Artifact |
| links_to | Any | Any |
| aliases | Alias | Any except Alias |
| supersedes | Artifact, Section, Requirement, NonFunctionalRequirement | same kind as source |
| extends | Project, Artifact | Project, Artifact |
| depends_on | Project, Artifact | Project, Artifact |
| mounted_as | ProjectRelation | Mount |

`produces` and `promoted_from` reject in Wave 3 because their canonical run,
result, and promotion node schemas arrive in later waves. Invalid pairs fail
before hashing.

Wave 2 edge records are schema v1 (absence of `schema_version` is accepted only
inside a manifest whose schema is 1). Loading them constructs a v2 wrapper
without mutating the v1 snapshot. Scalar/list fields and UID are copied;
v1 generator `{id,version,rule,input_snapshot}` maps exactly to v2
`{generator_id:id,version,rule,input_snapshot_uid:input_snapshot}`;
`provenance.project_uid`, `worktree_uid`, `revision_id`, and
`input_snapshot_uid` come from the containing immutable manifest;
`source_uid` is the first bytewise-sorted evidence UID or null;
`source_location`, `decision_uid`, and `authority` are null. The migrated
wrapper hashes under schema v2 and is recorded in
`EdgeMigrationRecord={type:"edge_migration",edge_uid,source_snapshot_uid,
source_edge_hash,target_edge_hash}`. `source_edge_hash` is SHA-256 over UTF-8
`spipe-edge-v1\0` plus canonical JSON of the complete v1 wrapper;
`target_edge_hash` uses `spipe-edge-v2\0` plus the complete v2 wrapper.

Before constructing or hashing the v2 wrapper, the manifest's legacy
`worktree_uid:W-...` resolves through the unique retained
`IdentityMigrationRecord(old_record_type=worktree)` to `WT-...`. Each endpoint
with prefix `W-` resolves by its canonical v1 endpoint record type: workspace
maps through the workspace record and worktree through the worktree record.
The translated `WS-`/`WT-` value replaces the endpoint in v2; the original
remains only inside `source_edge_hash`/`original_edge`. Missing or multiple
typed mappings produce a historical record with reason
`identity_mapping_missing` or `identity_mapping_ambiguous`, never a guessed
graph edge.

Migration is total: after endpoint resolution, a v1 edge whose type/kinds are
enabled by the Wave 3 table enters the graph. `produces`, `promoted_from`, or an
edge with absent/unsupported endpoints becomes an immutable
`HistoricalEdgeRecord={schema_version:2,type:"historical_edge",source_snapshot_uid,
source_edge_hash,reason,original_edge}` in the migration segment, is queryable
only through advisory history, and is excluded from `graph_root`. Reasons are
the closed enum `{deferred_edge_type,missing_endpoint,unsupported_endpoint_kind,
identity_mapping_missing,identity_mapping_ambiguous}`.
A v1 accepted edge without authority is
advisory historical evidence only and cannot satisfy Standard, Strict, or
mission-critical gates until a new receipt-bound v2 acceptance is published.
Missing/ambiguous manifest bindings reject migration with `SPK005`.

```sdn
edge:
  uid: E-...
  type: edge
  edge_type: verifies
  from_uid: T-...
  to_uid: RQ-...
  origin: explicit
  status: accepted
  confidence_milli: 1000
  created_by: principal:alice
  created_at_revision: 3b676a1...
  evidence_uids: [A-...]
  generator: nil
  provenance: {project_uid: P-..., worktree_uid: WT-..., revision_id: 3b676a1...,
               input_snapshot_uid: spks1-..., source_uid: A-...,
               source_location: {source_artifact_uid: A-..., source_hash: sha256:...,
                 span: {start_byte: 10, end_byte: 20}}, decision_uid: D-...}
  authority: {kind: explicit_review, receipt_uid: D-...,
              policy_hash: sha256:..., policy_version: 1}
```

Stored direction follows the active-verb table in the architecture. An inverse
query is computed and never materialized as another edge. The store is a
**directed typed multigraph**: distinct provenance/evidence edges between the
same endpoints are preserved. Only the lifecycle progression subgraph is
required to be acyclic; general `links_to`, `depends_on`, `extends`, and
classification relationships may contain cycles. Lifecycle-cycle detection
returns a diagnostic and blocks strict publication. `generated` edges
also store generator ID/version/rule/input snapshot. Inferred edges remain
`proposed`; review may annotate or reject them but cannot make them compliance
evidence without creating a separate explicit edge.

An authorization receipt is a signed `D-` record verified through
`AuthorizationPort`. Its payload binds receipt UID, exact edge UID and canonical
acceptance-subject hash, endpoints, origin, accepted status, project/worktree, input snapshot,
policy hash/version, issuer key ID, capability (`trace.accept.explicit` or
`trace.accept.generated`), issued-at, expiry, and revocation epoch. Strict
evaluation verifies every binding; it never trusts stored authority prose.
The subject is `spipe-edge-accept-v1\0` plus canonical JSON of the edge with
`status`, `provenance.decision_uid`, and `authority` removed. The completed
stored-edge hash is computed only after attaching the receipt UID.

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
`GraphDelta` node and edge changes, and `IndexDelta` lexical changes, plus alias changes,
projection invalidation keys, and `DiagnosticRecord` changes. It names its base
snapshot and all input hashes. Parent
publication rejects a delta whose base, schema, or project revision differs
from the pinned generation.

Wave 3 freezes `GraphDelta.nodes` and `GraphDelta.edges` as separate,
UID-disjoint operation sets. Added values contain canonical records. Updated
values contain `before_hash` plus the complete replacement record; removed
values contain UID plus `before_hash`. The enclosing and nested base snapshot
UIDs must agree. A repeat is idempotent only when its recorded delta hash maps
to the same output root; otherwise post-publication replay is stale. A
`before_hash` hashes canonical JSON of the complete stored wrapper. The graph
root hashes exact canonical JSON `{schema:1,nodes:[...],edges:[...]}`, nodes by
UID and edges by `(from_uid,edge_type,to_uid,uid)`, with no omitted fields.
Endpoint/type/origin/provenance changes
are remove-plus-add with a new EdgeUid, not updates.

`delta_hash` is SHA-256 over `spipe-graph-delta-v1\0` plus canonical JSON of
the complete delta. Successful publication retains immutable
`{delta_hash,base_snapshot_uid,base_graph_root,output_snapshot_uid,
output_graph_root}` beside the output snapshot. Exact lookup returns
`already_applied`; same-base different hash or absent retained replay evidence
returns stale base.

Canonical graph record prefixes are `RQ`, `NFR`, `SS`, `SY`, `WS`, and `WT` as
defined by the architecture. Requirement headings use their stable SectionUid
as the owning document location and an `RQ-`/`NFR-` record as trace identity;
`REQ-*`/`NFR-*` prose identifiers are keys and aliases. Parsers emit candidates
until both identities are canonical. `R-` is never a requirement UID.

`GraphStorePort` defaults/hard limits are: depth `8/32`, visited nodes
`2,000/20,000`, returned edges `10,000/50,000`, work units
`50,000/500,000`, edge pages `100/1,000`, and trace rows `100/1,000`.
Exhaustion returns deterministic partial data, reason, counters, and an
authenticated snapshot-bound cursor. `SnapshotPin` is a store-issued branded
handle (authenticated opaque token across processes) binding store generation,
snapshot UID, graph root, authorization-scope digest, policy version,
issued/expiry time, and liveness generation. Invalid pins fail before lookup.

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

`SnapshotStore.stage(manifest, objects)` durably writes immutable objects and a
non-current manifest. `publish(expected_current_uid, next_manifest)` acquires
the per-worktree writer lock and atomically replaces `current.sdn` only when the
expected UID matches. `pin_current(scope)` returns an immutable pin containing
manifest UID, graph root, authorization-scope digest, and release handle;
`release(pin)` decrements retention. Graph queries accept only a live pin and
cannot reread `current.sdn` mid-request.

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
| rationale/evidence -> requirement | candidate or verified accepted | verified explicit/generated accepted | receipt-bound accepted | same + trusted immutable evidence |
| design satisfies requirement | candidate may warn only | verified explicit/generated accepted | receipt-bound accepted | same + approved design revision |
| scenario specifies requirement | candidate may warn only | verified explicit/generated accepted | receipt-bound accepted | same + signed spec revision |
| source implements requirement/spec | structural candidate allowed | verified annotation/explicit/generated | receipt-bound accepted | same + trusted compiler snapshot |
| test verifies requirement/spec | candidate may warn only | verified explicit/generated accepted | receipt-bound accepted | same + immutable signed result |
| run produces passing result | latest result displayed | verified non-stale accepted result | receipt-bound non-stale result | signed, immutable, policy-approved environment |

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

### 7.3 Refactor filesystem capability

`RefactorSafeFilesystemPort` is exposed only through the non-copyable capability
`SafeFilesystem.Refactor`, bound to transaction, project, worktree, pinned
snapshot, allowed canonical relative paths/operations, metadata policy, and
expiry. Only `RefactorService` may hold it; parsers, projections, providers,
rebalancing, promotion, and subordinate executors cannot retain or receive the
capability. Its exact API is:

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
write, recursive-delete, symlink-following, or cross-device mutation. Content
removal is an `atomic_move` into the transaction rollback area; cleanup follows
the commit receipt. `FileMetadata` covers type, mode, owner/group, ACL, xattrs,
platform flags, and the policy decision for each field. Compare-before-rollback
uses `read_regular(..., applied_hash)` and `capture_metadata` to verify the
recorded applied state before invoking `stage_regular`/`atomic_replace`,
`atomic_move`, `restore_metadata`, or `remove_empty_directory`; receipt and
post-operation hashes then prove restoration. A mismatch refuses rollback and
preserves recovery evidence. Success from a mutation method means only the
operation occurred; durability requires explicit `sync_file` and parent
`sync_directory` receipts recorded in the journal. Platforms lacking an exact
primitive return a typed unsupported/durability error rather than emulate
weaker semantics silently.

Materialized-view output separately uses `MaterializerSafeFilesystemPort`
through capability `SafeFilesystem.Materializer`, restricted to the registered
per-worktree generated-view root and generated-file replace/remove operations.
Possession of `SafeFilesystem.Refactor` never grants materialization access,
and possession of `SafeFilesystem.Materializer` never grants canonical read,
move, replace, metadata-restore, rollback, or refactor access. Neither port nor
capability implies the other; authorization, construction, audit, and negative
tests treat them as independent capabilities.

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

`trust_scope` is the requirements-frozen closed enum `untrusted_data`,
`reviewed_reference`, or `executable_policy`. It is derived as the minimum trust
permitted by every canonical source, extension, reviewer receipt, project
registry trust, and destination policy; generation cannot request or infer a
higher value. Only `executable_policy` may produce an active agent-policy
surface. `reviewed_reference` may generate documentation or disabled previews;
`untrusted_data` may only be rendered as escaped data and never as instructions.
Project/family/common reach is separate authorization metadata
`authorization_scope_kind` plus `authorization_scope_uid`; it is not encoded in
or inferred from the enum. Validation rejects unknown values, executable-policy
elevation without a separately authorized REQ-SPKC-025 review receipt, scope
mismatch, expired/revoked review, and any source hash not covered by the
derivation. Generated headers render the exact enum and both authorization
scope fields; harness loaders/checkers must reject missing, unknown, stale, or
insufficient trust or authorization before treating content as instructions.

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
      trust_scope: executable_policy
      authorization_scope_kind: project
      authorization_scope_uid: P-...
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

- [ ] Complete the textual BM25 side index, remaining embedded-database
  consumers, and server adapters; add WAND/Block-Max WAND,
  tenancy/capability/cancellation, optional ANN, and safe semantic policy.
- [ ] Do not reopen DBFS scorer/facade migration here: its compatibility and
  parity gate completed in Wave 4; Wave 10 may consume that frozen surface only.
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

## 16. Wave 4 Lexical Source Admission and Remaining Integration Design

### 16.1 Accepted capsule and call sequence

Commit `9eb667e23b` admits
`examples/05_stdlib/spipe/src/search/lexical_source.js` with its root unit
oracle. `createAuthorizedLexicalSourceV1` accepts exactly four own data
capabilities and snapshots their function values once:

1. `verifySearchReceipt` verifies and returns the exact frozen binding;
2. `readLexicalProviderPage` supplies one frozen, receipt-bearing provider page;
3. `authorizeArtifactCandidate` rechecks every collected candidate exactly once
   without early exit;
4. `verifyLexicalEvidence` verifies the final page-set and ordered-rank digests
   exactly once.

The returned object is frozen and exposes only `readLexicalSourceV1`. Port
exceptions collapse to stable public errors; port records are closed and frozen;
accessors, symbols, hidden fields, sparse arrays, mutation, or identity drift
are rejected. The hot path performs no tree scan, file reread, process launch,
network call, retry sleep, clock read, or randomness of its own.

### 16.2 Request and provider-page records

The public request is the exact closed shape
`{contractVersion,operation,query,context,pin,sourceK,excludedDocumentUid}` with
operation `lexical_source`. The context/pin bind workspace, project, worktree,
revision, snapshot/root, scope, policy, search receipt, and analyzer identity.
`sourceK` is `1..1000`, default `1000`; the query cap is 4,096 UTF-8 bytes.

The provider request is
`{receipt,bindingDigest,query,queryDigest,excludedDocumentUid,requestedLimit,
providerCursor}`. Each returned page is the exact frozen shape
`{schema,bindingDigest,providerIdentity,excludedDocumentUid,exclusionApplied,
providerCursorDigest,requestedLimit,pageStartRank,candidateCount,candidates,
nextCursor,nextCursorDigest,exhausted,pageDigest,receipt}`. The page cap is
1,000 candidates and 524,288 canonical bytes; the request cap is 64 pages and
2,097,152 aggregate raw-evidence bytes; cursor and document-ID caps are 8,192
and 512 UTF-8 bytes.

For page `n+1`, `providerCursor` is page `n`'s `nextCursor`, and its
`providerCursorDigest` must equal page `n`'s `nextCursorDigest`. Both cursor
digests hash `{bindingDigest,cursor}` under the cursor domain. The page receipt
attests the binding, exclusion, inbound cursor, requested limit, next cursor,
and page digest. Page evidence retains exactly
`{receiptUid,pageDigest,excludedDocumentUid,exclusionApplied,
providerCursorDigest,requestedLimit,nextCursorDigest,pageStartRank,
candidateCount,exhausted}` for aggregate verification.

Candidates use `{documentId,sourceRank,sourceScoreMilli}`. Ranks are dense
across pages; score is descending; ties use unsigned UTF-8 document ID. The
source completes on provider exhaustion or `sourceK`, then emits a complete
RRF-v2 lexical source with source identity, candidate digest, evidence identity,
and bounded counters. It never emits partial candidates.

### 16.3 Restricted canonical JSON oracle

All lexical digests use restricted `spipe-canonical-json-v1`, not ambient
`JSON.stringify`: NFC scalar strings/keys, duplicate-normalized-key rejection,
unsigned UTF-8 key ordering, dense arrays, closed data records, safe integer
numbers excluding `-0`, and lowercase long C0 escapes. U+0009 is therefore
encoded as `\u0009`, not the short `\t` spelling. Tests construct these
preimages with an independent restricted encoder and cover page-size invariance.

### 16.4 Provider-owned exclusion

When exact identity is pinned, `excludedDocumentUid` is passed into the provider
and must be removed before scoring order and pagination. The provider page,
receipt, binding, page-set digest, rank-evidence digest, evidence decision, and
source identity bind the exclusion. The producer also rejects the excluded UID
if returned. Caller post-filter is insufficient because removing an exact UID
from a provider-capped 1,000-row page cannot yield the requested complete
1,000-row lexical source.

The provider-adapter/protocol version and ownership mapping must be frozen next;
no filename is frozen yet. Its conformance oracle must prove pre-ranking
exclusion, page/cursor continuity, `spipe-search-provider/1.0`,
`spipe-unicode-lex-v1`, `bm25-fixed-v1`, and receipt parity before pipeline use.

### 16.5 Evidence and non-evidence

The admitted source passed focused `16/16`, full `158/158` unit, Wave 2 `9/9`,
Wave 3 `25/25`, Wave 4 `9/9`, legacy, security, workflows, performance, and
final highest-capability review.

The graph candidate at `/tmp/spkc-graph-candidates-4OKnKd` is not admitted.
After the third bounded cycle it remains `13/14`; its cyclic-graph assertion
uses an uncontracted `workUnits <= 9` oracle. Although seven static defects were
patched, neither full-suite nor final highest-capability evidence exists. The
files have no accepted commit and satisfy no AC.

### 16.6 Frozen remaining source/test ownership

Each future implementation is an indivisible product/oracle pair under
`examples/05_stdlib/spipe/`:

| Order | Product | Independent oracle | Gate |
|---:|---|---|---|
| 1 | `src/search/graph_candidates.js` | `test/unit/search_graph_candidates_test.js` | Exact accepted-edge traversal, contracted work-unit oracle, focused/full/final review |
| 2 | Provider adapter/protocol filenames pending ownership freeze | Separate conformance oracle pending the same freeze | Version, pre-ranking exclusion, cursor/page/receipt parity |
| 3 | `src/search/rerank_evidence.js` | `test/unit/search_rerank_evidence_test.js` | Lossless source/evidence assembly and one authority-bound verification |
| 4 | `src/search/pipeline.js` | `test/unit/search_pipeline_test.js` | Exact pin -> excluded complete sources -> exhaustive graph -> RRF-v2 -> evidence -> rerank -> user limit |

The pipeline may consume only admitted commits. It must not inline graph
traversal, provider translation, or rerank-evidence verification. AC-4 remains
open through all standalone prerequisites and closes only with end-to-end
pipeline and explanation evidence.

## 17. Graph Admission, Provider 1.1 Freeze, and Active Rerank Evidence

The rejected graph attempt in Section 16.5 remains a provenance record, but
commit `626b3e0797` supersedes its status with an admitted product/oracle pair.
Evidence is focused `16/16`; full unit `174/174`; Wave 2 `9/9`, Wave 3 `25/25`,
Wave 4 `9/9`; legacy integration and performance `PASS`; and pre-runtime plus
final highest-capability review `PASS`. The corrected cyclic fixture requires
exactly `workUnits == 10`.

### 17.1 Graph-source record and traversal design

The graph request remains the closed v1 record:

```text
{contractVersion, operation, context, pin, pinnedArtifactUid,
 lexicalSeeds, sourceK, maxWorkUnits, maxTotalWorkUnits, cursor}
```

Default/maximum bounds are `sourceK=1,000`, page work `50,000`, total work
`500,000`, nodes `20,000`, edges `50,000`, roots `1,001`, depth 3, and 512
UTF-8 bytes for request/seed identifier inputs accepted by `validText`. One
work unit is one incident edge examined
for one expanded frontier-path state, including excluded, already-used, and
non-improving edges. Paging stops before consuming the next edge; a cursor
resumes that exact position. Hitting total work with pending work destroys the
state and returns `limit_exceeded`, even when the page budget also expires.

Before traversal, every node is authorized exactly once in canonical UID order.
Accepted edges are verified exactly once and must be explicit or generated,
carry accepted status, bind both endpoints and the project/worktree/snapshot/
policy/search receipt, and return an exact authority echo. Nonaccepted edges are
excluded; malformed accepted records fail as snapshot corruption; missing or
bad authority evidence fails closed.

Traversal is both-direction and allows non-artifact intermediate nodes. It
stores the best state per `(nodeUid,distance)` and re-expands descendants when a
later path wins at the same distance. The comparison tuple, ascending, is:

1. distance;
2. seed tier (`exact` before `lexical`);
3. seed rank;
4. generated-edge count;
5. negative bottleneck confidence;
6. edge UID sequence by unsigned UTF-8;
7. direction sequence (`out` before `in`);
8. node UID sequence by unsigned UTF-8.

Candidates add artifact UID as the final tie-break, and `sourceK` truncation is
late. Evidence records retain ordered
`{edgeUid,authorityReceiptUid}` pairs. The convenience edge/receipt arrays are
derived; repeated use of one receipt across distinct edges remains visible in
the pair list. Independent literal SHA-256 fixtures cover
`acceptedEdgeSetDigest`, `evidenceDigest`, `sourceIdentity`, and
`candidateDigest`.

### 17.2 Authorized lexical-page wire records

Wire negotiation is `{major:1,minor:1}` with
`authorized_lexical_page:true`. Operation `lexical_page` accepts:

```text
{binding_digest, query_text, query_digest, excluded_document_uid,
 requested_limit, cursor}
```

and returns:

```text
{logical_root, excluded_document_uid, exclusion_applied, requested_limit,
 page_start_rank, hits, next_cursor, exhausted}
```

Each hit is `{document_id,source_rank,score_milli}`. Page schema is
`spipe-authorized-lexical-provider-page-v1`; adapter identity is
`spipe-authorized-lexical-provider-adapter-v1`. The semantic identities do not
change: provider `spipe-search-provider/1.0`, analyzer
`spipe-unicode-lex-v1`, scorer `bm25-fixed-v1`. Protocol 1.0 stays a legacy
surface and cannot back the admitted lexical source.

`excluded_document_uid` is removed before scoring/top-k insertion and before
page ranking. It does not alter the immutable snapshot's `N`, `df`, or average
document length. A cursor binds provider generation/implementation, workspace,
snapshot, authorization scope, logical root, binding digest, query digest,
excluded UID, and next rank. It must not bind `requested_limit` or a `qr-*`
receipt: requested limits can decrease across fragmented pages, and the wire
receipt is specific to one page.

The wire `qr-*` receipt and authority `D-*` receipt have separate domains. The
adapter verifies the wire result, stores a signed `D-*` lexical-page record, and
returns this exact projection:

```text
{receiptUid, kind, bindingDigest, excludedDocumentUid, exclusionApplied,
 providerCursorDigest, requestedLimit, nextCursorDigest, pageDigest}
```

`kind` is `lexical_page`. Aggregate verification resolves every `D-*` receipt
and binds the whole cursor chain, page-set digest, rank-evidence digest,
exclusion, policy, root, and provider identities. A caller cannot synthesize a
`D-*` receipt from a visible `qr-*` value.

### 17.3 Exact implementation ownership

| Surface | Exact owner/change |
|---|---|
| Shared JS identities and capabilities | modify `examples/05_stdlib/spipe/src/index/contracts.js` |
| Pre-ranking exclusion in logical search | modify `examples/05_stdlib/spipe/src/index/logical_index.js` |
| Wire 1.1 negotiation/validation | modify `examples/05_stdlib/spipe/src/provider/protocol.js` |
| Raw provider translation | modify `examples/05_stdlib/spipe/src/provider/adapter.js` |
| In-process fixed-point page production | modify `examples/05_stdlib/spipe/src/provider/js_fixed_point.js` |
| Public exports | modify `examples/05_stdlib/spipe/src/provider/index.js` |
| Authority-bound page/receipt bridge | add `examples/05_stdlib/spipe/src/provider/lexical_page.js` |
| Independent JS oracle | add `examples/05_stdlib/spipe/test/unit/search_lexical_provider_page_test.js` |
| Cross-provider vectors | add `examples/05_stdlib/spipe/test/fixture/wave4_search/authorized_lexical_provider_page_vectors.json` |

The existing native owners are
`src/app/spipe_knowledge_provider/lexical.spl`, `wire_query.spl`,
`wire_core.spl`, `protocol.spl`, and `service.spl`. They extend the same scorer,
snapshot, lifecycle, and protocol owners; the design forbids a second native
lexical implementation or a guessed process-adapter module.

### 17.4 Sync/async boundary and first implementation slice

`readLexicalProviderPage` is synchronous. A persistent Simple subprocess is an
asynchronous byte-stream client. Blocking the synchronous port on process I/O
would put waits and potentially retries on the hot path; spawning a process per
page is also forbidden. The admitted first slice is therefore JS/in-process:

1. add the wire-independent authorized page bridge and vector fixture;
2. adapt the existing JS fixed-point provider;
3. prove version, exact exclusion, cursor, `qr-*`/`D-*`, page, and aggregate
   receipt parity;
4. retain the native files as mapped owners but make no process integration
   claim.

Native integration resumes only after choosing either an async lexical-source
v2 or an async collection session that produces an immutable page replay for
the synchronous evidence consumer. That decision must freeze cancellation,
deadline, buffer, lifecycle, and error semantics before naming a Node process
adapter.

### 17.5 Conformance and NFR oracle

The new unit/vector oracle must cover negotiation, closed request/result shapes,
semantic identity stability, pre-ranking exclusion under a provider limit,
unchanged corpus statistics, rank continuity, fragmented page limits, cursor
replay/tampering, `qr-*` versus `D-*` non-substitutability, receipt resolution,
literal digests, hostile sizes/shapes, and provider implementation drift. Until
that oracle and implementation land, the provider status is **contract frozen,
not conforming**.

Candidate performance gates are:

- lazy initialization;
- no process spawn, full-tree scan, repeated read, or retry sleep per query;
- startup P95 at most 250 ms;
- warm lexical P95 below 100 ms on 50,000 artifacts;
- a qualified max-RSS receipt and configured process RSS cap.

The numeric RSS target remains blocked pending Wave 0 baseline/profile evidence.
These are candidate NFR targets, not current PASS evidence.

### 17.6 Active rerank evidence and pipeline order

The standalone `src/search/rerank_evidence.js` plus
`test/unit/search_rerank_evidence_test.js` implementation lane is active. It is
not yet pipeline-owned and must be admitted independently. The final pipeline
order is fixed:

1. exact identity resolution and pin;
2. complete lexical collection with provider-owned pre-ranking exclusion;
3. accepted-edge graph generation from the exact root and lexical seeds;
4. complete-pool RRF v2;
5. authority-bound rerank-evidence assembly/verification;
6. pair-based bounded reranking and explanations;
7. user limit last.

Graph admission closes only the standalone graph prerequisite. No provider
conformance, pipeline integration, or AC-4 completion is claimed here.

### 17.7 Authority bridge correction: full synchronous ABI

This subsection is authoritative over Sections 17.2-17.5 wherever they can be
read as permitting a page translator that merely invents the nine-field
`D-*` projection. That pre-authority adapter is rejected: it would make
`lexical_source.js` accept a UID with no verified `qr-*`, signature, retained
record, revocation check, or later resolution path. The first JavaScript slice
is still synchronous and in-process, but it is the complete authority bridge,
not a smaller compatibility shim.

The semantic contracts remain unchanged:

```text
provider       spipe-search-provider/1.0
analyzer       spipe-unicode-lex-v1
score          bm25-fixed-v1
wire           {major:1,minor:1}
wire capability authorized_lexical_page:true
wire operation lexical_page
adapter        spipe-authorized-lexical-provider-adapter-v1
page schema    spipe-authorized-lexical-provider-page-v1
page receipt   spipe-lexical-page-evidence-receipt-v1
aggregate      spipe-lexical-aggregate-evidence-receipt-v1
store          spipe-lexical-evidence-store-v1
```

Protocol `1.1` is transport evolution, not provider semantic identity `1.1`.
Protocol `1.0` remains usable by legacy search callers, but cannot satisfy the
authorized lexical-source port.

#### 17.7.1 Factory and captured ports

`createAuthorizedLexicalProviderPageBridgeV1(config)` accepts one closed plain
record with exactly these fields:

```text
{providerSession, issueTransportQueryReceiptV1,
 verifyTransportQueryReceiptV1, executeLexicalPageV11,
 lexicalEvidenceAuthority, lexicalEvidenceStore, clockNowMs}
```

Every function is synchronous. Returning a `Promise` or thenable is a contract
failure. The factory copies the seven values once, uses own property
descriptors without ordinary property reads, rejects accessors, unknown fields,
mutable identity records, and any proxy whose observable traps/descriptors do
not behave as the required closed data. JavaScript cannot identify a fully
transparent proxy by brand, so the contract does not claim an impossible
blanket proxy detector. The factory returns exactly this deeply frozen surface:

```text
{readLexicalProviderPage, verifyLexicalEvidence}
```

Those method names intentionally match the ports already captured by
`createAuthorizedLexicalSourceV1`; the composition root supplies the existing
`verifySearchReceipt` and `authorizeArtifactCandidate` ports separately.

`providerSession` is this closed frozen record:

```text
{wireProtocol:{major:1,minor:1}, authorizedLexicalPage:true,
 adapterIdentity, providerContractVersion, providerImplementationDigest,
 providerGeneration, analyzerIdentity, scoreContractVersion,
 workspaceUid, snapshotId, authorizationScopeDigest, lexicalRoot,
 policyHash, policyVersion, transportKeyId,transportAuthorityId,
 transportAuthorityGeneration,transportRevocationGeneration,deadlineMs,
 requestedLimit:{minimum:1,maximum:1000}}
```

The adapter identity and four semantic identity fields must equal the literals
above; digests are `sha256:` plus 64 lowercase hex characters. `policyVersion`
is an unsigned 32-bit integer and `deadlineMs` is in `[1,30000]`.
`providerGeneration` is `pg-` plus 32 lowercase hex characters; snapshot IDs
are `spks1-` plus 64 lowercase hex characters. Workspace, project, worktree,
artifact, and `D-*` values must pass the existing canonical UID parser
(admitted prefix and either 32 uppercase hexadecimal characters or 26
uppercase Crockford characters, excluding `I`, `L`, `O`, and `U`). Other
authority/session text is NFC, nonempty, contains no NUL, and is at most 512
UTF-8 bytes.
The transport key/authority/generation/revocation tuple comes from the trusted
transport authority at session creation. Both provider-side and bridge-side
verification decisions must echo it exactly; a newer revocation generation
invalidates the session rather than silently widening it.

The in-process provider side is composed separately as
`createInProcessLexicalPageExecutorV11({provider,providerSession,
verifyTransportQueryReceiptV1,lexicalCursorAuthority,clockNowMs})`. It captures
that exact closed configuration and returns one frozen direct function,
`executeLexicalPageV11(envelope)`. The composition root supplies the same
trusted transport verifier identity to this executor and to the bridge; the
executor verifies `qr-*` before calling the raw fixed-point index.

`lexicalCursorAuthority` is a closed capability with exactly the same
`identity()/sign(bytes)/verify(bytes,signature)` method shapes and frozen
six-field identity record specified below for `lexicalEvidenceAuthority`. Its
`key_id`, `authority_id`, `authority_generation`, `revocation_generation`,
`policy_version`, and `policy_digest` must equal the provider session's
transport tuple and policy. It is therefore the transport authority's cursor
signing face, normally the same object behind the query-receipt issuer/verifier.
It is not the evidence authority: `lexicalEvidenceAuthority` may use another
key/authority/generation but must bind the same policy. Both signatures are
Ed25519 and domain-separated.

`lexicalEvidenceAuthority` is the established closed authority capability:

```text
identity() -> {key_id,authority_id,authority_generation,policy_version,
               policy_digest,revocation_generation}
sign(bytes) -> Ed25519Base64UrlText
verify(bytes,signature) -> bool
```

The identity result is deeply frozen and closed. Its policy version/digest must
equal `providerSession.policyVersion/policyHash`. Authority and revocation
generations are unsigned 32-bit integers. The authority is the only page or
aggregate `D-*` signer; the provider, bridge, lexical source, and store cannot
mint an evidence UID independently.
`Ed25519Base64UrlText` is exactly 86 unpadded characters matching
`[A-Za-z0-9_-]{86}`. Both transport and evidence authorities use Ed25519; a
different algorithm or padded/base64 spelling is `incompatible_contract`.

`lexicalEvidenceStore` is a closed synchronous capability:

```text
reserveOperationV1({operationKey,inputDigest,kind})
  -> {status:"reserved",operationKey,reservationToken}
   | {status:"replay",operationKey,receiptUid,recordDigest}
   | {status:"tombstoned",operationKey,receiptUid,recordDigest,reason,
      observedAtMs}
commitReceiptV1({operationKey,inputDigest,reservationToken,receiptUid,
                 recordDigest,record})
  -> {status:"stored",receiptUid,recordDigest}
resolveReceiptV1({receiptUid})
  -> nil | {receiptUid,recordDigest,record}
tombstoneOperationV1({operationKey,inputDigest,reservationToken,receiptUid,
                      recordDigest,reason,observedAtMs})
  -> {status:"tombstoned",operationKey,receiptUid,recordDigest,reason,
      observedAtMs}
```

All records and results are deeply frozen closed data. `reservationToken` is a
store-local, single-use, unforgeable frozen token with no enumerable state.
Reserve is atomic. An existing reserved operation is `operation_conflict`;
there is no second writer. Commit is atomic across the operation-key mapping
and receipt object. A `reserveOperationV1` replay is legal only when input, UID,
and full record digest are byte-identical; commit never manufactures replay.
Tombstone is idempotent only for the same operation,
input, token, receipt UID/record digest (both may be null before D issuance),
reason, and time. For a reserved operation, the exact non-null token is required and
`receiptUid/recordDigest` are either both null or the just-created pair. For an
active/replay record or a post-commit resolve failure, `reservationToken` is
null and the exact stored UID/digest pair is required. Thus stale or corrupt
replay can be tombstoned without inventing a reservation token. Active or
tombstoned entries cannot be overwritten in the store generation.
`inputDigest` is not a second hash: for `kind:"lexical_page"` it is exactly the
`H(SPKC-LEXICAL-PAGE-OPERATION-V1,...)` value whose hex forms the `lpo-*` key;
for `kind:"lexical_aggregate"` it is exactly the corresponding aggregate
operation digest. These are the only two `kind` values. Tombstone `reason` is
exactly one of `interrupted`, `expired`, `revoked`, `binding_mismatch`,
`authority_generation_changed`, `policy_changed`, or `record_corrupt`.
`internal_error` is deliberately not a tombstone reason. If trusted
cursor-authority `identity`, `sign`, or `verify` malfunctions after reservation,
the bridge first persists `interrupted` and then returns public
`{code:"internal_error"}`. This is an explicit public/storage mapping, not an
enum coercion. A specific expiry, revocation, binding, authority-generation,
policy, or record-corruption classification established first retains
precedence.

`observedAtMs` on a tombstone is the post-reservation trusted start observation.
Only an `interrupted` tombstone caused by failure of that first observation may
use `observedAtMs:null`; no other tombstone may use null. A reservation has no
timestamp because it is intentionally created before any clock/liveness call.

#### 17.7.2 Existing lexical-source request records

The bridge consumes the current frozen page request unchanged:

```text
{receipt,bindingDigest,query,queryDigest,excludedDocumentUid,
 requestedLimit,providerCursor}
```

`receipt` is the exact verified search-binding echo with these fields:

```text
{contractVersion,operation,workspaceUid,projectUid,worktreeUid,revisionId,
 snapshotId,lexicalRoot,authorizationScopeDigest,policyHash,policyVersion,
 searchReceiptUid,analyzerIdentity,queryDigest,sourceK,excludedDocumentUid}
```

It must be frozen, closed, and agree with `providerSession` for workspace,
snapshot, scope, root, policy, and analyzer. `bindingDigest`, `queryDigest`,
exclusion, and the cursor digest are recomputed by the bridge rather than
trusted from strings supplied by the caller.

The aggregate port consumes the current `verifyLexicalEvidence` request:

```text
{binding,bindingDigest,providerIdentity,pageSetDigest,rankEvidenceDigest,
 excludedDocumentUid,exclusionApplied,pageReceipts,outputDocumentIds}
```

Each aggregate page-evidence entry supplied by the existing lexical source is
exactly:

```text
{receiptUid,pageDigest,excludedDocumentUid,exclusionApplied,
 providerCursorDigest,requestedLimit,nextCursorDigest,
 pageStartRank,candidateCount,exhausted}
```

This ten-field aggregate entry differs deliberately from the nine-field
provider-page `receipt` projection (which additionally has `kind` and
`bindingDigest`, and omits rank/count/exhausted). Neither projection is
authority by itself.

#### 17.7.3 Wire 1.1 records and `qr-*`

Initialization uses the existing closed request fields and an exact selected
minor version:

```text
{request_id,operation:"initialize",protocol:{major:1,minor:0|1},
 client:"spipe",required:{provider,analyzer,score,explanation,logical_index},
 limits:{max_frame_bytes:1048576}}
```

The success envelope remains
`{request_id,operation:"initialize",ok:true,result}`. For a 1.0 request,
`result.protocol` is exactly `{major:1,minor:0}` and `capabilities` retains the
current closed fields:

```text
{index_delta,lexical,explain,stats,cancel,shutdown,phrase,regex,wildcard,
 duplicate,symbols,semantic,scope_partition}
```

For a 1.1 request, `result.protocol` is exactly `{major:1,minor:1}` and its
closed capability record adds one final field,
`authorized_lexical_page:true`. The rest of `result` remains exactly:

```text
{protocol,provider,implementation_digest,provider_ids,analyzer_ids,score_ids,
 explanation_ids,logical_index_ids,capabilities,limits,optional_fields:[]}
```

The limits record is the existing closed `PROVIDER_LIMITS` record; 1.1 does not
silently enlarge it. The provider may accept either exact minor, but it must
return the requested minor—there is no silent upgrade or downgrade. A client
requesting 1.1 fails `protocol_unsupported` if 1.1 is unavailable and
`incompatible_contract` if the new capability is absent/false or any semantic
identity changes. Unknown major/minor values and extra capability fields fail
closed. A 1.0 caller continues to receive the byte-compatible 1.0 shape without
the new field. `providerSession` may be constructed only from a validated 1.1
result, its bound open/health root and scope, and the current trusted transport
authority identity.

For each fresh page, the bridge produces a deterministic request ID from the
page operation digest, issues one query receipt, and invokes one provider call.
`executeLexicalPageV11` accepts exactly the wire envelope below and returns
exactly the success response below or throws a closed provider error; it never
accepts or returns a lexical-source page record.
The wire envelope is closed:

```text
{request_id,operation:"lexical_page",protocol:{major:1,minor:1},
 provider_generation,workspace,snapshot,scope_digest,query_receipt,
 operation_receipt:null,deadline_ms,payload}
```

The payload is exactly:

```text
{binding_digest,query_text,query_digest,excluded_document_uid,
 requested_limit,cursor}
```

The successful response is exactly:

```text
{request_id,operation:"lexical_page",ok:true,protocol:{major:1,minor:1},
 provider_generation,workspace,snapshot,scope_digest,query_receipt,
 operation_receipt:null,result}
```

and `result` is:

```text
{logical_root,excluded_document_uid,exclusion_applied,requested_limit,
 page_start_rank,hits,next_cursor,exhausted}
```

Each hit is `{document_id,source_rank,score_milli}`. The request receipt must be
verified by the provider before query execution and echoed byte-for-byte in the
response. The bridge independently verifies the echo before accepting hits.

The `spipe-query-receipt-v1` record is the existing closed wire record:

```text
{schema,receipt_id,key_id,authority_id,authority_generation,request_id,
 operation,provider_generation,workspace,snapshot,scope_digest,logical_root,
 query_hash,issued_at_ms,expires_at_ms,policy_version,policy_digest,
 revocation_generation,signature}
```

`issueTransportQueryReceiptV1` accepts the closed expected tuple
`{requestId,operation,providerGeneration,workspace,snapshot,scopeDigest,
logicalRoot,queryHash,observedAtMs,expiresAtMs}` and returns that full frozen
receipt. `issued_at_ms` must equal `observedAtMs`; `expires_at_ms` must equal
`expiresAtMs`, which is `observedAtMs + min(deadlineMs,30000)`.
`verifyTransportQueryReceiptV1` accepts
`{receipt,expected,observedAtMs}` and returns exactly one deeply frozen closed
decision member:

```text
{decision:"verified",receiptId,keyId,authorityId,authorityGeneration,
 policyVersion,policyDigest,revocationGeneration,issuedAtMs,expiresAtMs}
{decision:"rejected",reason}
```

The rejected member has exactly `reason`, which is one of `invalid_signature`,
`expired`, `revoked`, `binding_mismatch`, `authority_generation_changed`, or
`policy_changed`. Identity, generation, root, policy, scope, time, and
revocation must match the expected session for the verified member. A thrown
value, thenable, unknown field/reason, mutable result, or other shape is a
verifier malfunction, not a rejected member. A `qr-*` value is never a `D-*`
value.
The response echo is equal only when the restricted canonical bytes of the
complete closed receipt are identical to those issued; object identity and a
partial field comparison are insufficient.

For protocol 1.1, `scope_digest` equals
`providerSession.authorizationScopeDigest` and `policy_digest` equals
`providerSession.policyHash`; these are separate bindings even if a legacy 1.0
deployment happened to reuse one value for both. `policy_version` equals the
session policy version. The 1.1 adapter must not inherit the legacy shortcut
that treated scope digest as policy digest.

#### 17.7.4 Canonical encoding and digest preimages

`C(v)` is restricted `spipe-canonical-json-v1`: NFC strings, null, booleans,
safe integers, dense arrays, closed plain/null-prototype data objects, and keys
sorted by unsigned UTF-8. Floats, `-0`, accessors, proxies, sparse arrays,
`undefined`, and non-NFC strings are rejected. Authority framing is:

```text
F(domain,v) = UTF8(domain + "\0") || U64BE(len(C(v))) || C(v)
H(domain,v) = "sha256:" || lowercase_hex(SHA256(F(domain,v)))
```

The existing lowercase lexical query/binding/cursor/page/page-set/rank/source
hashes retain their already-admitted `domain + "\0" || C(v)` encoding. The
bridge must not silently change their goldens to the length-framed authority
encoding.

The new and reused authority preimages are exact:

| Domain | Canonical value |
|---|---|
| `SPKC-LEXICAL-PROVIDER-SESSION-V1` | complete closed `providerSession` |
| `SPKC-LEXICAL-PAGE-OPERATION-V1` | `{adapterIdentity,providerImplementationDigest,providerGeneration,providerSessionDigest,bindingDigest,queryDigest,excludedDocumentUid,providerCursorDigest,requestedLimit}` |
| `SPKC-QUERY-PAYLOAD-V1` | `{operation:"lexical_page",payload}` |
| `SPKC-QUERY-RECEIPT-V1` | unsigned `spipe-query-receipt-v1` record without `receipt_id` or `signature` |
| `SPKC-AUTHORIZED-LEXICAL-CURSOR-V1` | unsigned authorized cursor below |
| `SPKC-LEXICAL-TRANSPORT-RECEIPT-DIGEST-V1` | complete verified `qr-*` record |
| `SPKC-LEXICAL-PAGE-EVIDENCE-RECEIPT-V1` | unsigned page evidence record below |
| `SPKC-LEXICAL-OUTPUT-DOCUMENTS-V1` | `{bindingDigest,documentIds}` |
| `SPKC-LEXICAL-AGGREGATE-OPERATION-V1` | `{providerSessionDigest,bindingDigest,pageSetDigest,rankEvidenceDigest,outputDocumentIdsDigest}` |
| `SPKC-LEXICAL-AGGREGATE-EVIDENCE-RECEIPT-V1` | unsigned aggregate evidence record below |
| `SPKC-LEXICAL-EVIDENCE-STORE-RECORD-V1` | complete signed page or aggregate record |

`query_hash` is `H(SPKC-QUERY-PAYLOAD-V1,{operation,payload})`. A query receipt
ID is exactly `qr-` followed by all 64 lowercase SHA-256 hex characters of its
receipt preimage (67 UTF-8 bytes total). A `D-*` UID is the first
32 uppercase hex characters of its evidence-receipt SHA-256; the store rejects
any truncated-UID collision through the full `recordDigest`.

Let `hex(H(...))` mean the 64 lowercase hex characters after `sha256:`. The
page operation key is exactly `lpo-` plus the page-operation hex; its request ID
is exactly `req-lp-` plus the same hex. The aggregate operation key is exactly
`lao-` plus the aggregate-operation hex. The store accepts only those two key
patterns, so page and aggregate operations cannot alias.

`providerSessionDigest` is computed once at bridge construction. It is stored
in every page and aggregate receipt and participates in both replay identities;
provider implementation drift therefore cannot reuse an old page operation.

#### 17.7.5 Authenticated provider cursor

A non-null wire cursor is the unpadded Base64Url encoding of restricted
canonical bytes for this exact closed record:

```text
{schema:"spipe-authorized-lexical-cursor-v1",key_id,authority_id,
 authority_generation,revocation_generation,adapter_identity,
 provider_contract_version,provider_implementation_digest,
 provider_generation,provider_session_digest,workspace,snapshot,scope_digest,
 logical_root,binding_digest,query_digest,excluded_document_uid,next_rank,
 issued_at_ms,expires_at_ms,policy_version,policy_digest,signature}
```

The signature is Ed25519 over
`F(SPKC-AUTHORIZED-LEXICAL-CURSOR-V1,unsigned-record-without-signature)`.
Decoding must be strict, the re-encoded canonical bytes must equal the input,
and every session/root/scope/policy/authority/revocation field must match.
`next_rank` is in `[1,1001]`. The cursor deliberately omits both the current
`requested_limit` and every page-local `qr-*`; a smaller terminal page and a
new transport receipt therefore remain legal. It does bind provider
implementation/session identity, exclusion, query, and next rank. Cursor issue
and expiry equal the verified request receipt times, so it cannot outlive the
request authority that caused its creation.

#### 17.7.6 Full signed page record

The unsigned page evidence record is closed and exact:

```text
{schema:"spipe-lexical-page-evidence-receipt-v1",
 receiptKind:"lexical_page",adapterIdentity,wireProtocol,
 keyId,authorityId,authorityGeneration,revocationGeneration,
 policyVersion,policyHash,providerSession,providerSessionDigest,
 binding,bindingDigest,queryDigest,
 pageOperationDigest,transportQueryReceipt,transportQueryReceiptDigest,
 providerCursor,page,issuedAtMs,expiresAtMs}
```

`providerCursor` is the inbound raw cursor or null. `page` is the complete page
returned to `lexical_source.js` except for its nine-field `receipt` projection:

```text
{schema,bindingDigest,providerIdentity,excludedDocumentUid,exclusionApplied,
 providerCursorDigest,requestedLimit,pageStartRank,candidateCount,candidates,
 nextCursor,nextCursorDigest,exhausted,pageDigest}
```

`providerIdentity` and candidates retain their existing exact closed shapes.
The page digest retains the already-admitted lowercase-domain preimage and does
not include raw `nextCursor`; the signed page record does include it. The full
stored record is `{...unsigned,receiptUid,signature}`. Its signature verifies
over `F(SPKC-LEXICAL-PAGE-EVIDENCE-RECEIPT-V1,unsigned)`. `receiptUid` is
recomputed from that same framed preimage. Its store `recordDigest` covers the
complete signed record with `SPKC-LEXICAL-EVIDENCE-STORE-RECORD-V1`.

The bridge derives the nine-field projection from this verified stored record;
it never accepts a projection as proof. Page expiry is at most 30 seconds and
must not exceed the echoed transport receipt expiry.

#### 17.7.7 Full signed aggregate record

The unsigned aggregate record is closed and exact:

```text
{schema:"spipe-lexical-aggregate-evidence-receipt-v1",
 receiptKind:"lexical_aggregate",adapterIdentity,wireProtocol,
 keyId,authorityId,authorityGeneration,revocationGeneration,
 policyVersion,policyHash,providerSession,providerSessionDigest,
 binding,bindingDigest,
 providerIdentity,excludedDocumentUid,exclusionApplied,pageReceipts,
 pageReceiptUids,transportQueryReceiptIds,pageSetDigest,rankEvidenceDigest,
 outputDocumentIds,outputDocumentIdsDigest,providerPageCount,
 providerCandidateCount,issuedAtMs,expiresAtMs}
```

The full record is `{...unsigned,receiptUid,signature}` using the aggregate
domain, UID rule, and store-record digest above. Aggregate expiry cannot exceed
the earliest page or transport-receipt expiry.

`verifyLexicalEvidence` resolves every page `D-*` in input order, verifies its
store digest, UID, signature, current authority/key/generation/revocation,
policy, expiry, full binding, provider session, and embedded `qr-*`; compares
the supplied projection to the stored record; then reconstructs cursor and rank
continuity from stored pages. It independently recomputes the existing
`pageSetDigest` and `rankEvidenceDigest`, plus `outputDocumentIdsDigest`. Only
then may it sign and atomically store the aggregate record. It immediately
re-resolves and re-verifies that aggregate before returning exactly:

```text
{bindingDigest,pageSetDigest,rankEvidenceDigest,excludedDocumentUid,
 exclusionApplied,authorityReceiptUid,decision:"verified"}
```

This immediate write/read witness is required for page and aggregate records.
It closes the prior contradiction between “stored/resolvable” evidence and an
ABI that exposed only a fabricated projection.

#### 17.7.8 Replay, revocation, cache, and fallback lifecycle

Page operation keys include the provider session/implementation, inbound cursor
digest, and requested limit; aggregate keys include the provider session and
completed evidence digests. The bridge derives the complete input digest and
operation key before calling `reserveOperationV1`. An exact live replay
resolves and fully re-verifies the old record and returns the same receipt UID
without provider execution or signing. A key mapped to different input bytes
is `operation_conflict`. Expired, revoked, wrong-root, wrong-policy, or
wrong-authority-generation evidence is tombstoned for that bridge generation
and fails closed; it is never refreshed under the same operation key. A new
provider/bridge generation and newly verified search binding are required.
The bridge calls `tombstoneOperationV1` before returning that failure; a
tombstone reserve never resolves or executes the provider again.

Once a reservation is returned, every non-commit exit—including an exception
after `qr-*` issuance or provider execution—must tombstone the reservation.
Consequently an identical retry cannot issue a second transport receipt or
create ambiguous evidence; it sees the tombstone and fails closed. Because the
first store is process-local, a process crash loses both provider and bridge
generation. Recovery constructs a new generation and requires a new verified
search binding rather than replaying the interrupted operation.

The first concrete store is bounded, process-local, and synchronous. Records
survive for the bridge generation only; restart persistence is explicitly not
claimed. All operation-table states—reserved, active/replay, and tombstoned—
count toward one 4,096-entry generation cap. `accountedBytes` includes the
restricted-canonical bytes of every operation key/input/state and signed record
plus a fixed 64-byte charge per opaque reservation token; it is capped at
64 MiB. Each reservation additionally pre-charges exactly 2,048 bytes of
worst-case tombstone headroom (`MAX_TOMBSTONE_BYTES_V1`); reservation fails
before any side effect if that headroom is unavailable. Tombstoning replaces
the reservation within its pre-charge. Commit atomically replaces reservation,
token, and headroom with the active record; if the active-record capacity check
fails, the reservation and its tombstone headroom remain intact, so mandatory
cleanup cannot itself exceed the cap. One signed page record is capped at 1 MiB
and one aggregate at 2 MiB.
Entries are not evicted or overwritten inside a generation; closing the bridge
destroys the whole store. Capacity is checked atomically before reservation or
commit and fails `limit_exceeded`, so reservation/tombstone indexes cannot grow
outside the stated envelope and no unsigned page is returned.

The raw provider owns immutable snapshot/index/corpus-statistics and optional
rank-list caches. The adapter caches only the validated 1.1 session identity.
The evidence store owns receipts/replay, not an alternative ranking cache. The
lexical source owns only per-call aggregation. Provider selection (`js_fixed`
or a later provider) occurs before bridge creation and is bound into
`providerImplementationDigest/providerGeneration`; fallback never switches
provider between pages. Mid-collection failure invalidates the collection.

#### 17.7.9 Ordered call sequence and failures

Every page call first validates/caps, makes one start `clockNowMs` observation,
rejects a throwing, non-safe-integer, negative, or bridge-local
time-regressing clock, derives the session/input/operation/query hashes, and
calls `reserveOperationV1`. Its two successful branches are disjoint:

- **Replay:** on `status:"replay"`, resolve the complete stored page, compare
  the returned UID and record digest with the reservation result, and fully
  re-verify the store digest, page UID/signature, complete embedded `qr-*`,
  authority/revocation, session/binding/root/scope/policy, cursor/page/rank
  semantics, and derived projection. Observe the end clock and re-check
  monotonicity, current transport/cursor/evidence authority identity, and all
  expiries. Return the same page and projection. This branch **does not call**
  `issueTransportQueryReceiptV1`, `executeLexicalPageV11`,
  `lexicalEvidenceAuthority.sign`, or `commitReceiptV1`.
- **Fresh:** on `status:"reserved"`, issue `qr-*`; execute the provider, which
  verifies the receipt before scoring; validate the closed provider page and
  exact canonical-byte receipt echo; independently verify `qr-*`; recompute
  cursor/page/rank semantics; read current evidence-authority identity; sign
  and self-verify the full page `D-*`; atomically commit; and immediately
  resolve and re-verify it. Observe the end clock, re-check monotonicity,
  current authority/revocation, and every transport/evidence/cursor expiry,
  then return the page and derived projection. No signing or commit happens
  before provider output is fully validated; the reservation is the only
  earlier store mutation.

A tombstoned reserve fails without calling the issuer, provider, signer, or
commit. Any page end-check failure tombstones the reserved or committed record
with the exact token/UID/digest form required by Section 17.7.1.

Every aggregate call follows the same disjoint structure after validate/cap,
start observation, operation derivation, and reserve. A replay resolves and
fully re-verifies the existing aggregate plus every referenced page, observes
and validates the end time/current authorities, then returns the same
seven-field decision without calling `lexicalEvidenceAuthority.sign` or
`commitReceiptV1`. A fresh reservation resolves and re-verifies every page
store digest, signature, `qr-*`, authority/revocation, binding, root, policy,
projection, cursor chain, and rank sequence; recomputes all aggregate digests;
signs/self-verifies/commits/re-resolves the aggregate `D-*`; observes end; and
requires every page, transport receipt, cursor, and aggregate record to remain
live and authority-current before returning. A tombstoned reserve fails
without signing or commit. A terminal end-check failure tombstones the exact
aggregate record.

On a page call, an invalid clock becomes `provider_unavailable`; on an
aggregate call it becomes `evidence_unverified`. The start time supplies
transport issue/expiry and newly signed evidence issue fields; the end time is
the final liveness gate. Authority and store methods do not consult another
bridge clock. `executeLexicalPageV11` also calls its provider-side
`clockNowMs` exactly twice on success: after envelope validation/before `qr-*`
verification, and after ranking/cursor construction/before response return. It
requires both observations to be nonnegative, safe, monotonic, and inside the
receipt lifetime. Invalid envelope uses zero calls; receipt rejection can use
one. Cursor issue/expiry fields are copied from the verified `qr-*`. The bridge
and executor clocks are two views of the same trusted monotonic clock service;
tests may feed the same start/end sequence to both.

Tombstone mapping is deterministic: elapsed receipt time is `expired`; a verifier-current revocation
decision is `revoked`; workspace/snapshot/scope/root/binding/session drift is
`binding_mismatch`; key or authority generation drift is
`authority_generation_changed`; policy digest/version drift is
`policy_changed`; and UID/digest/signature/canonical-record inconsistency is
`record_corrupt`. Otherwise incomplete provider/authority/store work is
`interrupted`. The first applicable reason in that order is stored.

After reservation, an otherwise unclassified trusted cursor-authority
malfunction stores `interrupted` before returning public `internal_error`.
The public code never becomes stored state and does not extend the tombstone
enum; the specific classifications in the preceding order win over this
catch-all mapping.

Bridge-level public error precedence is:

1. `invalid_request` for closed-shape/type/canonicality failure;
2. `limit_exceeded` for a valid-shaped value above a fixed cap;
3. `protocol_unsupported` or `incompatible_contract` for negotiation/identity;
4. `binding_mismatch` or `stale_cursor` for pin/root/cursor drift;
5. `operation_conflict` for replay-key conflict;
6. `unauthorized` for an absent, invalid, expired, or revoked `qr-*`;
7. `provider_unavailable` for provider execution/health failure;
8. `snapshot_corrupt` for a malformed or inconsistent provider page;
9. `evidence_unverified` for authority/store/receipt/aggregate failure;
10. `internal_error` for an otherwise unclassified exception.

Errors expose only `{code}` or `{code,field}`. The lexical-source boundary keeps
its current normalization: page-port exceptions become `provider_unavailable`;
aggregate-port exceptions become `evidence_unverified`.

Existing caps remain: query 4,096 UTF-8 bytes, cursor 8,192 bytes, one wire page
524,288 bytes, at most 1,000 candidates, 64 pages, and 2 MiB aggregate raw page
evidence. IDs/bindings are at most 512 UTF-8 bytes. Query-receipt and signature
records are additionally capped at 16 KiB; each Ed25519 signature is exactly 86
unpadded Base64Url characters.

#### 17.7.10 Exact implementation ownership and oracle

The complete in-process slice owns these files and no async/process adapter:

| File | Responsibility |
|---|---|
| `src/index/contracts.js` | 1.1 capability constants; semantic IDs unchanged |
| `src/index/logical_index.js` | provider-owned exclusion before scoring/top-k; corpus stats unchanged |
| `src/provider/protocol.js` | closed 1.1 envelopes, payload/result, `qr-*` validation contracts |
| `src/provider/adapter.js` | one validated session and exact wire/raw translation |
| `src/provider/js_fixed_point.js` | synchronous `lexical_page` execution and provider-side `qr-*` verification |
| `src/provider/lexical_page.js` | bridge factory, canonical preimages, page/aggregate signing and verification |
| `src/provider/lexical_evidence_store.js` | bounded synchronous atomic record/replay/tombstone store |
| `src/provider/index.js` | public exports only |
| `test/unit/search_lexical_provider_page_test.js` | independent closed-record and lifecycle oracle |
| `test/fixture/wave4_search/authorized_lexical_provider_page_vectors.json` | literal wire/page/receipt/aggregate/store digest goldens |

All relative source paths above are under `examples/05_stdlib/spipe/`. The
Simple-native files remain future semantic/parity mappings only; this slice
does not edit them and makes no async, subprocess, native, or cross-restart
durability claim.

The independent oracle must prove: exact factory/config/output shapes; direct
non-thenable calls; byte-compatible 1.0 initialization and exact non-downgraded
1.1 negotiation/capability; stable 1.0 semantic IDs;
provider-side and bridge-side `qr-*` verification; query/root/scope/policy/
revocation/generation binding; provider-owned pre-ranking exclusion with stable
corpus statistics; page/rank/cursor continuity; signed page and aggregate
records; immediate store re-resolution; exact replay and conflict; expiry and
revocation failure; reserved/active/tombstone accounting, both tombstone token
paths, post-commit corruption, start/end expiry crossing, exact cursor-authority
pinning; `qr-*`/`D-*` non-substitutability; aggregate reconstruction
from full stored pages; hostile caps/proxies/accessors/sparse arrays; no
mid-stream fallback; and independent literal goldens for every domain above.

Candidate NFRs are bridge construction P95 below 5 ms, added authority/store
overhead P95 below 10 ms per 1,000-hit page excluding scoring, total warm
lexical P95 below 100 ms on 50,000 artifacts, zero process spawn/file scan/
retry sleep on the hot path, bounded 64 MiB evidence-store memory, and no
unbounded cache. Startup remains below 250 ms. These stay candidate targets
until the implementation oracle and measured receipts pass; AC-4 remains open.

### 17.8 Current admission ledger (2026-08-26)

The ABI in Section 17.7 is frozen and review-passed in commit `47a922eec6`, but
the provider product is not implemented or conforming. The implementation
attempt at `/tmp/spkc-lexical-provider-z15Uhp/repo` ended at the pre-runtime
review cap with no in-scope edit. Resume in a fresh session from the complete
Section 17.7 ABI, including authority, bounded store, replay/tombstone,
authenticated cursor, two-clock checks, and exact error precedence. Do not
revive the rejected minimal adapter that merely fabricates the nine-field
projection.

The rerank-evidence candidate at
`/tmp/spkc-rerank-evidence4-aIcFIZ/repo` contains only the untracked product
`examples/05_stdlib/spipe/src/search/rerank_evidence.js` and oracle
`examples/05_stdlib/spipe/test/unit/search_rerank_evidence_test.js`; it has no
admission commit. Focused `16/16`, full unit `190/190`, Wave 2 `9/9`, Wave 3
`25/25`, Wave 4 `9/9`, plus legacy, security, workflow, and performance gates
passed. Final highest-capability review after the third cycle still rejected
the pair because oversized derived evidence arrays do not preserve the
contracted `limit_exceeded` precedence and the semantic contract string is not
correctly bound to the admitted consumer contract. A fresh session must fix
and review exactly these two files.

No earlier green result changes the dependency order: provider implementation
and admission first, rerank-evidence admission second, integrated pipeline
third. AC-4 remains open.

### 17.9 Superseding implementation-readiness ledger (2026-08-26)

Commit `4455b760da` admits the standalone rerank-evidence source and oracle.
Its evidence is syntax `PASS`, focused `18/18`, unit `192/192`, Wave 2 `9/9`,
Wave 3 `25/25`, Wave 4 `9/9`, and legacy, security, workflow, and performance
`PASS`, with final independent xhigh review `PASS` in cycle 2 of 3. The
integrated pipeline may depend on this admitted pair without reopening it.

Provider implementation readiness remains `FAIL`. The provider-authority ABI
repair stopped at the mandatory three-cycle cap with unresolved
collision-result signaling, executor error classification, cursor error
precedence, and canonical-byte accounting versus heap/RSS limits. It made no
product edit, executed no product test, and created no repository-history
commit. Retained object `3827a1099e` at
`/tmp/spkc-provider-abi-repair2-clean` is a failed immutable draft only. Its
contract text is excluded from this detail design.

Resume with a fresh, bounded provider-ABI repair that resolves those four
items, then implement and admit the provider. Only afterward may the pipeline
integrate exact identity, excluded lexical results, graph results,
complete-pool RRF v2, admitted rerank evidence, pair reranking/explanations,
and the final user limit. Wave 4 and AC-4 remain open.

### 17.10 Cursor-authority failure representation (2026-08-26)

The representability blocker from the final-four review is resolved without
broadening the ABI. After reservation, an unclassified malfunction of trusted
cursor-authority `identity`, `sign`, or `verify` first persists tombstone reason
`interrupted`, then returns public `internal_error`. `internal_error` is not and
must not become a tombstone-enum member. Specific failures already classified
as expiry, revocation, binding, authority-generation, policy, or record
corruption retain precedence. Product implementation and admission, Wave 4,
AC-4, and the integrated pipeline remain open; this contract correction is not
product evidence.

### 17.12 Full ABI consolidation review stop (2026-08-26)

The attempted eleven-item consolidation stopped `FAIL` after the mandatory
third review/fix cycle. No product file was edited, no product test ran, no
contract was admitted, and nothing was pushed. Preserve failed immutable
snapshot `e5c556de59d` at `/tmp/spkc-provider-abi-full-uWb9kD/repo` only for
forensic comparison; do not copy its contract text.

Implementation-readiness review passed, but independent highest-capability
review identified two self-containment failures. Section 17.11 excludes Section
17.7.1 while relying on its exact `providerSession`, authority, and executor
schemas. It also excludes Section 17.7.9 while omitting the complete public
error record and field shapes and exhaustive error precedence. The next fresh
design session must restate all of those definitions directly in Section 17.11
instead of inheriting excluded control prose. This is a failed handoff, not a
readiness claim: provider readiness/implementation/admission, Wave 4, AC-4, and
the integrated pipeline remain open.

### 17.13 Self-containment repair review stop (2026-08-26)

The fresh repair stopped `FAIL` after its mandatory third review/fix cycle. No
authoritative contract or product file was edited, no product test ran, and
nothing was pushed. Preserve immutable failed snapshot
`e77cb713d5703d864f32d16ab3abab0afb5d3215` at
`/tmp/spkc-provider-self-contained-JdUR6t/repo` only as forensic evidence; do
not copy its rejected clauses.

Implementation-readiness review passed, but independent highest-capability
review found three exact design blockers: the generic code-only unauthorized
arm overlaps the provenance arm; the pre-reserve binding/cursor rule conflicts
with traces reserving before `Cidentity`/`Cverify`; and the exact
`requestedLimit` range is absent despite the candidate cap. The next fresh
design session must make the executor-error union structurally disjoint,
choose one reserve/cursor order and tombstone owner, and specify
`requestedLimit` as `1..1000`. Provider readiness/implementation/admission,
Wave 4, AC-4, and the integrated pipeline remain open.

### 17.14 Fresh provider ABI correction — executable contract candidate (2026-08-26)

This section supersedes only the conflicting executor-failure, verifier-result,
reservation timestamp, cursor-order, and `requestedLimit` wording in Sections
17.7.1, 17.7.2, 17.7.3, 17.7.8, and 17.7.9. The exact provider-session
capability now advertises its fixed request-limit interval, and reservation is
intentionally timestamp-free so no liveness operation precedes it. It preserves
the previously frozen transport/evidence authority, signed-record, bounded
store, canonical-byte, public-error, and non-admission contracts except for
those narrow representational corrections. It is a documentation candidate,
not provider implementation or admission evidence.

#### 17.14.1 Closed `requestedLimit` contract

Every public page request, bridge page-operation preimage, wire-envelope
payload, executor input payload, executor success result, signed page record,
stored page projection, and page-replay result names the same semantic value:
`requestedLimit` in camel-case records and `requested_limit` in wire records.
It is a positive safe integer in the inclusive range **1..1000**. Its type and
range are checked after the containing closed shape/scalar/canonical checks and
before any authority, provider, signing, or store side effect. A valid-shaped
integer outside that range is `limit_exceeded`; a non-integer, unsafe integer,
absent field, or noncanonical representation is `invalid_request`. The same
value must agree canonically across the bridge request, operation preimage,
executor payload/result, returned page, signed `D-*`, and replay projection.
The `qr-*` has no direct request-limit field: it cryptographically binds the
restricted-canonical payload containing `requested_limit` through its exact
`query_hash`, which the bridge recomputes. It is a per-page value: authenticated cursors intentionally do not
bind it, so a subsequent page may use another value in `1..1000`.

The immutable provider-session capability is therefore explicit (and is the
same closed record stated in Section 17.7.1):

```text
{wireProtocol:{major:1,minor:1}, authorizedLexicalPage:true,
 adapterIdentity:"spipe-authorized-lexical-provider-adapter-v1",
 providerContractVersion:"spipe-search-provider/1.0",
 providerImplementationDigest,providerGeneration,
 analyzerIdentity:"spipe-unicode-lex-v1",scoreContractVersion:"bm25-fixed-v1",
 workspaceUid,snapshotId,authorizationScopeDigest,lexicalRoot,
 policyHash,policyVersion,transportKeyId,transportAuthorityId,
 transportAuthorityGeneration,transportRevocationGeneration,deadlineMs,
 requestedLimit:{minimum:1,maximum:1000}}
```

The final `requestedLimit` capability record is descriptive and frozen; it is
not caller-configurable. The request/payload field remains mandatory for each
call and must be within that exact advertised interval.

#### 17.14.2 Structurally disjoint executor failure union

`executeLexicalPageV11` returns either the existing closed success response or
exactly one deeply frozen closed failure member. The union is discriminated by
shape, not merely by a prose condition:

```text
{ok:false,error:{code}}
{ok:false,error:{code:"unauthorized",tombstoneReason}}
```

In the first member, `code` is exactly one of `invalid_request`,
`limit_exceeded`, `incompatible_contract`, `binding_mismatch`, `stale_cursor`,
`provider_unavailable`, `snapshot_corrupt`, or `internal_error`; it **excludes
`unauthorized`**. The second member has exactly the two shown error fields and
is the only executor representation of `unauthorized`. Its private
`tombstoneReason` is exactly one of the existing seven storage values:

```text
interrupted | expired | revoked | binding_mismatch |
authority_generation_changed | policy_changed | record_corrupt
```

The executor emits the two-field unauthorized member only for a classified
transport-receipt verifier rejection, with this exhaustive mapping:

| verifier result | private `tombstoneReason` |
|---|---|
| invalid signature/canonical receipt | `record_corrupt` |
| expired | `expired` |
| revoked | `revoked` |
| binding mismatch | `binding_mismatch` |
| authority-generation drift | `authority_generation_changed` |
| policy drift | `policy_changed` |

A verifier throw, thenable, malformed result, or unclassified trusted
cursor-authority malfunction is not an unauthorized member: it is the
code-only `{ok:false,error:{code:"internal_error"}}` member. No other code may
carry `tombstoneReason`. After reservation, the bridge validates this exact
union. For its unauthorized member it persists the private reason, but returns
only public `{code:"unauthorized"}`; the reason is never exposed to the
lexical-source or MCP boundary. For code-only `internal_error`, an executor
throw/thenable/malformed result, or unclassified cursor-authority malfunction,
the bridge persists `interrupted` before returning public `internal_error`.
The existing ordered tombstone classification takes priority whenever it has
already established a more specific legal reason.

#### 17.14.3 One page/replay/fresh order and one tombstone owner

The bridge is the sole owner of store reservation and tombstoning. The executor
never reserves, commits, tombstones, or calls the evidence store. For every
page call, the following total order is normative; no prose, trace, or oracle
may place `Cidentity` or `Cverify` before reservation:

1. Validate the outer closed request and nested scalar/canonical shape;
   enforce `requestedLimit` `1..1000`, query/cursor byte caps, and wire/page
   independent caps. This pre-reservation stage may inspect cursor type and
   raw UTF-8 length, but does not decode, authenticate, bind, or check liveness
   of a non-null cursor.
2. Validate negotiated protocol/session/capability identity and derive the
   operation key/input digest from the raw canonical cursor text or null. These
   are structural/capability checks only; no clock, authority, verifier,
   workspace/snapshot/root/binding equivalence, or cursor liveness operation is
   permitted before reservation.
3. Call `reserveOperationV1` exactly once. A rejected/collision/tombstoned
   reserve returns its existing public store result with no cursor-authority,
   transport issuer/verifier, provider, evidence authority, commit, or
   tombstone call.
4. With `status:"reserved"` or `status:"replay"`, make the one start-clock
   observation, then call cursor `identity()` and decode, canonical-reencode,
   `verify`, and compare every cursor
   session/workspace/snapshot/scope/root/binding/query/exclusion/generation/
   policy field and cursor time. A null cursor completes this cursor stage after
   `identity()` without a `verify` call. These checks occur before branch
   execution, so both fresh and replay have identical cursor authority.
5. For `status:"replay"`, resolve and re-verify the stored page record,
   embedded `qr-*`, stored cursor continuity, expiry, authority, binding, and
   projection; then make the end-clock/liveness check and return the retained
   page. It issues no `qr-*`, executes no provider, signs nothing, and commits
   nothing.
6. For `status:"reserved"`, issue `qr-*`; execute the provider; independently
   verify the echo; validate the complete returned page; authenticate any next
   cursor; derive/sign/self-verify the page `D-*`; atomically commit; resolve
   and re-verify; then make the end-clock/liveness check and return.

Every failure from steps 4–6 is post-reservation and is tombstoned by the
bridge before its public error is returned. The one ordered reason table is:

| first established post-reservation fact | persisted reason | public outcome |
|---|---|---|
| elapsed cursor/receipt/page lifetime | `expired` | `stale_cursor` for inbound cursor; otherwise owning public code |
| trusted current revocation decision | `revoked` | `unauthorized` for `qr-*`; otherwise owning public code |
| workspace/snapshot/scope/root/binding/session/query/exclusion drift | `binding_mismatch` | `stale_cursor` for inbound cursor; otherwise owning public code |
| key/authority generation drift | `authority_generation_changed` | `stale_cursor` for inbound cursor; otherwise owning public code |
| policy version/digest drift | `policy_changed` | `stale_cursor` for inbound cursor; otherwise owning public code |
| UID/digest/signature/canonical record/page/projection inconsistency | `record_corrupt` | classified `qr-*` verifier rejection is `unauthorized`; otherwise `snapshot_corrupt` or `evidence_unverified` at its page/D/store owner |
| any remaining incomplete provider/authority/store work | `interrupted` | owning public code, or `internal_error` for an unclassified trusted failure |

The first applicable row is final. An authenticated inbound cursor failure is
public `stale_cursor`; a verifier-classified `qr-*` failure uses the disjoint
unauthorized member and public redaction above. A pre-reservation malformed or
oversized cursor is respectively `invalid_request` or `limit_exceeded` and
creates no store entry. A later cursor failure cannot be reclassified as a
pre-reservation validation failure.

The page call oracle is consequently fixed: valid fresh and replay calls make
one bridge reserve, then one start-clock observation, then one cursor
`identity`; a non-null inbound cursor makes one cursor `verify` after that
identity. Fresh success may additionally verify and sign only the outbound
cursor after provider-page validation. Replay never issues, executes, signs, or
commits. Any post-reservation cursor error calls exactly one bridge tombstone;
cursor processing precedes fresh commit, so no commit result can own that
cleanup. No executor trace may tombstone independently.

#### 17.14.4 Required focused oracle rows

The provider-page oracle must include one adversarial row each for: generic
executor `unauthorized` shape rejection; unauthorized arm missing/adding a
field; all six verifier-to-seven-enum mappings; private-reason redaction;
malformed verifier result mapping to `internal_error` plus `interrupted`;
`requestedLimit` values `0`, `1`, `1000`, `1001`, unsafe integer, and string;
pre-reservation malformed/oversize cursor with no reserve; valid cursor failure
after reserve with exactly one tombstone; replay cursor failure after reserve;
and fresh/replay call counts proving `Cidentity`/`Cverify` follow reserve.
These tests are required before implementation readiness can become PASS.

### 17.15 Provider implementation non-admission: resolve the factory ABI first (2026-08-26)

The attempted implementation in `/tmp/spkc-provider-admission4-kVaqO2/repo`
(base `f7ec2dc1b0c0de4b42bb97940b17bec9db29e5a1`) stopped before runtime work
after two immutable xhigh pre-runtime `FAIL` reviews. The final review attempt
added no edit to its exact ten-file scope and ran no runtime test, commit, or
push. The forensic candidate itself has an existing dirty diff. Never
transplant its code or wording.

The failure is structural. Section 17.14.3 requires bridge-owned
post-reservation cursor `identity`, decode, and `verify`, while the frozen
seven-field bridge factory configuration has no cursor-authority port. This
document does not silently widen that closed factory. A fresh design session
must explicitly choose and fully specify a compatible configuration ABI first,
including capability ownership and construction-time validation; a new
implementation lane may begin only after that design receives fresh
implementation-readiness and independent highest-capability review.

No provider behavior is admitted from the stopped candidate: mandatory
tombstones, the exact executor-error union, full replay verification, cursor
digest, store accounting/idempotency, closed-object accessors, and all required
oracle vectors remain unimplemented. Provider admission, Wave 4, AC-4, and the
integrated pipeline remain open.

## 18. Wave 5 Readiness: Resource, Tool, and Materialized-View Slice (2026-08-26)

<!-- codex-design -->

This slice implements the normative MCP-view design without changing the
provider/cursor sections above. Its frozen internal calls are:

```text
WorkspaceRegistry.open(workspaceId) -> KnowledgeSnapshot
ResourceResolver.resolve(snapshot, uri) -> ResourceTarget
ProjectionPort.list(snapshot, target, cursor, limit) -> ResourcePage
ProjectionPort.read(snapshot, target, range) -> ResourceContent
Materializer.sync(snapshot, view, outputRoot) -> MaterializeReceipt
```

`mcp/protocol/resources.js` and `mcp/protocol/tools.js` adapt those calls to
MCP only. Their request sequence is validate bounded input; select/open one
workspace; perform only workspace-level request admission; resolve one URI to
a canonical target; authorize that canonical target; use one immutable snapshot;
render a bounded result; attach snapshot/cursor/cache metadata. They must not walk the
host tree, call a search executable, or refresh an index. `spipe_search` may
initially use the admitted exact/lexical snapshot indexes only; optional
provider/semantic enhancement is an independently gated dependency.

Implement URI and projection first, then legacy-compatible stdio resource/tool
routing, then `.spipe/view` materialization. The resolver has one exact
canonicalization path: UTF-8/NFC validation, one percent decode, rejection of
remaining dangerous percent escapes and all traversal/Windows unsafe segments,
then workspace/revision authorization. `ProjectionUid` identifies every
aggregate; artifact/section UIDs identify only canonical targets. Directory
ordering is normalized display key, kind, UID, and every cursor binds the
effective authorization scope as well as its snapshot and page state.

Materialization is unavailable rather than emulated unsafely when an admitted
descriptor-relative native provider or pinned trusted helper is absent.
Publication stages projection-bound bytes, atomically replaces generated files,
syncs durability, and publishes a manifest last. Cleanup consults the previous
manifest and preserves unknown/user-modified/reparse/hard-linked entries.
Generated aggregates use `projection-uid`; only single canonical projections
may show `canonical-uid`/`canonical-path` headers.

Admission requires one successful evidence run each: exact legacy transcript
compatibility; URI negative matrix; deterministic list/read/cursor fixture;
public versus private cache/ETag fixture; materializer no-op/delta/recovery
fixture; Unix symlink and Windows reparse race tests for every claimed native
provider; and the focused SSpec/manual. No notification, HTTP-2026, editor,
FUSE/ProjFS, or refactor claim is admitted by these tests.

## 19. Wave 5 URI foundation: non-admission and replacement test contract (2026-08-26)

<!-- codex-design -->

The three-cycle URI-foundation candidate is uncommitted and not admitted; Wave
5 URI execution remains pending. Do not import its code. The next implementation
must expose `authorizeCanonicalTarget(resolved, principal, snapshot)` only after
canonical alias resolution. A resulting receipt contains exactly:

```text
CanonicalReadReceiptV1{
receiptVersion, normalizedAliasUri, canonicalUri, workspaceUid, projectUid,
targetKind, targetUid, snapshotUid, revisionId, principalScopeHash,
policyVersion, decision, issuedAtMs, expiresAtMs, receiptUid, issuerKeyId,
revocationEpoch, signature
}
```

`spipe://skill` follows that path. On every list/read/tool call, resolve then
verify the signed `D-` record through
`AuthorizationPort.verifyCanonicalTargetReceiptV1`: it allowlists the receipt
version and issuer key, verifies the signature over
`spipe-uri-read-v1\0` plus canonical JSON of every preceding binding field,
checks `decision == allow`, `issuedAtMs <= clockNowMs < expiresAtMs`, and checks
the current revocation epoch. Then compare every binding field against the
direct snapshot lookup and resolved target; mismatch triggers reauthorization
or a redacted closed error. Validate
the snapshot's existence, immutability, workspace/project ownership, revision,
and target-kind/UID membership directly—never by a URI/query assertion.

The replacement suite must table-drive every URI family (workspace root,
workspace view, project artifact, project section, trace, diagnostics, and
legacy alias) against: malformed/overlong or unsupported URI; fragment or empty
identity segment; empty/duplicate/unknown bounded query field; bad/double
percent decode; traversal, slash/backslash, encoded separator/dot, drive/UNC,
Windows device/reparse, ADS colon, trailing dot/space; controls or malformed
Unicode; NFC/NFD collision and mixed-case identity; bad/stale/foreign cursor;
forged/expired/signature-invalid/revoked receipt; every alias/canonical, scope/policy,
snapshot/revision, or kind/UID receipt mismatch; and hidden versus absent
target. `spipe_search` is a tool-input contract, not a URI family. Assert
fail-closed, bounded, path-redacted public results.

For positive evidence, assert canonical list/read/render behavior for each
accepted surface: workspace root/view, artifact, section, trace, diagnostics,
legacy alias after canonical reauthorization, and the `spipe_search` tool. A
positive alias case must render only the canonical authorized target; it cannot
prove success by returning legacy-alias text or an unbound URI echo.

## 20. Selected transactional authority-service detail design (F1/N1)

This supersedes direct host-CAS execution and consumes REQ-SPKC-031/032 and
NFR-SPKC-026/027; no source is admitted. `AuthorityServiceV1` owns admission,
decision store, canonical open, leases, and a private certified backend. Clients
own only `AuthorityClientV1` and cannot construct a store/backend or treat a
pointer as authority.

1. Authenticate and validate exact scope/capability/trust, bounded key, and
   canonical proposal before transaction admission.
2. Validate `G=0` paired-null or `G>0` exact raw predecessor bytes/digest for
   `G-1`, next canonical pointer `G`, and terminal/object graph. In one
   serializable transaction, equal `(scope,key)` returns stored bytes; changed
   bytes rejects; a different contender returns the one durable `MismatchV1`
   winner; missing successor current is durable `HostReplaceFatalV1(SPK704)`.
   Otherwise write Request, Decision, and OpenIndex durably.
3. Commit, then return exact `ReplacedV1`/`MismatchV1`/SPK704 outcome. An invalid
   authenticated capability/scope/trust/authorization binding before Request
   admission is explicit non-enumerating `CapabilityDeniedV1`; only
   authentication/availability/transport failure is payload-free
   `ServiceTransportFailureV1`;
   a post-commit lost reply is client-local `IndeterminateDeliveryV1` and
   resolves only by same key plus request digest. A resolve with no admitted
   request returns only signed `NoAdmissionV1(scope,key,requestDigest,
   admissionWatermark,negativeIndexProof)`, never cache absence.
4. `open` pins the committed index, validates the full graph, then returns a
   lease-bound immutable view. Tenant UID appears in every primary/secondary
   key; audit records retain actor/key/capability/scope/request/decision digests,
   timestamp and code, never private canonical content.

Partitions/unavailable quorum admit no decision. An unexpired lease may serve
only its proven commit index; stale/revoked lease fails closed. Recovery
replays the decision log before service. `CertifiedAuthorityBackendV1` has only
private `certifyTuple`, `prepareEffects`, `commitEffects`, and `verifyEffects`
commands; certificate/result mismatch, expiry, or native error denies before
decision commit. Node has no backend chooser and no filesystem fallback.

The qualified deployment uses the §21.11 1,024-tenant/8,192-global queue,
1-MiB request bound, 500 decisions/s, publish 25/75-ms and open 10/30-ms
P95/P99, RPO=0, and 60-s single-member RTO. The qualifying fixture is three
8-vCPU/32-GiB/NVMe Linux nodes, recording CPU model/count and governor/turbo/
frequency policy, RAM, OS/kernel, isolated network topology/link
characteristics, and storage device/filesystem/mount options; it pins the
50,000-artifact corpus SHA-256 and canonical deterministic generator
revision/seed/distribution manifest. It uses a monotonic raw clock, five-minute
warmup, 30-minute/100,000-op 70/20/10 open/publish/resolve load at 70% capacity,
nearest-rank percentiles, and one power-cut per member. Telemetry samples queue,
commit, fsync, replication, lease, certificate, and failover; RPO/RTO boundaries
are §22.9's power-cut-to-log/open events.

### 20.1 First source-slice implementation contract (non-admitted)

The first source slice creates `authority/protocol`, `authority/client`,
`authority/service`, `authority/records`, and `authority/service_main` only as
closed codec/router boundaries. It is not a substitute decision store. The
request encoders must carry the signed caller/capability identity and every
scope coordinate (tenant, workspace, project-or-null, worktree, revision,
registry, base, snapshot), key, digest, and P3 raw-byte evidence; open binds a
required decision digest. Decoder validation is exact and rejects additional or
noncanonical fields before service dispatch.

`service_main` accepts only mutually authenticated framed IPC connections whose
peer credential and capability verifier are constructed at the service
composition root from trusted OS/certificate configuration. It must not read
credentials from env/argv/globals or accept a caller-provided verifier. Without
an admitted private durable backend it returns a pre-admission failure and
creates no mutable record, audit admission, receipt, backend command, or local
publication effect. This state claims zero positive availability.

`AuthorityClientV1.publish` invokes `selectCommitInputV1` once, binds the P2
replay digest/scope, and sends one `PublishRequestV1`. It neither constructs nor
selects a store/backend. Reply loss returns `IndeterminateDeliveryV1`; only a
same-scope/key/digest resolve can replace it, with exact durable terminal/winner
evidence or quorum-signed `NoAdmissionV1`. Missing or lost resolve remains
indeterminate. F2 is reachable only from a lexical private composition root and
requires live certification, parity, and service commit checks; normal Node is
denied before staging.

This slice tests only canonical codecs, the exactly-once P2 call sequence,
capability/transport denial, lost-delivery representation, and fail-closed
service main. It explicitly does not execute or satisfy W5A-65..93, and it
does not claim any §21.11 deployment target.

### 20.2 Sealed trust, send-state, and response-verification prerequisite

The source slice has one lexical composition owner.  It alone binds the client
channel, service listener, OS peer-credential/platform-certificate adapter,
service credential, trusted verification roots, response verifier, durable
store, and optional certified backend.  Product modules obtain only opaque
already-bound handles.  There is no exported factory/installer, constructor
argument, public DI token, test authority, environment/argv/global selector,
or caller-provided signer/verifier/store/backend object.  This applies equally
to Node and tests; normal Node has no substitute authority.

`AuthorityClientV1.publish` uses the following exact state machine after its
single P2 preflight: `prepared -> authenticated -> sendStarted -> awaitingReply
-> definitive|indeterminate`.  `authenticated` means mutual peer/service
identity and the connection binding have been verified.  Only a failure before
`sendStarted` returns local `ServiceTransportFailureV1`; the transition is
recorded immediately before the first framed write.  Once entered, all write,
flush, timeout, cancellation, peer-close, and decoder failures are
`IndeterminateDeliveryV1` unless the client verifies a definitive receipt.  A
valid service `CapabilityDeniedV1` is decoded as a service pre-admission result
even though it arrives after `sendStarted`.  `resolveAccepted` reuses the
unchanged `{scopeDigest,idempotencyKey,requestDigest,connectionBindingDigest}`;
it never tries another publish or changes scope/key/digest.

`AuthorityResponseReceiptV1` is canonical signed data, not a transport-shaped
object.  It binds `{header,responseKind,serviceInstanceUid,authorityKeyId,
authorityKeyEpoch,tenantUid,callerSubjectDigest,connectionBindingDigest,
scopeDigest,requestDigest,idempotencyKeyOrNull,decisionDigestOrNull,
terminalDigestOrNull,admissionWatermarkOrNull,negativeIndexProofDigestOrNull,
issuedAtMs,expiresAtMs,signature}`.  Terminal/winner responses require exact
non-null decision/terminal bytes and digests and null negative-proof fields.
`NoAdmissionV1` requires exact non-null quorum watermark and signed negative
proof and null terminal/winner fields.  Before returning either, the client
checks canonical bytes, signature/key epoch/revocation, service identity,
authenticated connection and caller-subject binding, original request tuple,
expiry, and the applicable durable terminal/proof binding.  Any failure keeps
the post-send request indeterminate.

Private test composition is a separate executable fixture, not public product
injection: test code can request named barriers and read observations but cannot
construct a peer credential, signer, verifier, durable proof, store, backend,
or authority response.  Valid signed vectors originate inside that sealed
fixture; public tests supply only invalid/malformed values.  This permits
negative trust-boundary evidence without granting synthetic publication
authority or claiming durable-service admission.

### 20.3 Snapshot-read kernel: closed, fixture-only, and non-admitted

The read-kernel implementation boundary is
`SnapshotAuthorityPortV1.openBoundSnapshot(binding)`.  It accepts no raw
manifest, map, path, store, snapshot handle, URI, cursor, or projection object.
Its sealed composition root internally supplies its only admissible value: a
private branded `PublishedAuthorityInventoryV1`; it does not expose or rename
the separate `TargetInventoryStoreV1.openPublishedAuthorityInventoryV1`
boundary.  Before a result is exposed,
the kernel compares all seven binding coordinates
`{workspaceUid,projectUidOrNull,worktreeUid,baseSnapshotUid,
authoritySnapshotUid,revisionId,registryRevisionId}` plus
`authorityInstanceUid` and `authorityManifestDigest`; a mismatch returns a
closed non-admission failure.  `resolveCanonicalTarget` and
`listDirectoryTarget` return opaque candidate values with no locator, byte
reader, grant, URI, path, cursor position, or rendering method.

This module has no imports from external-open, MCP, URI parsing, cursor,
filesystem, store, or projection surfaces.  Its private fixture tests are
limited to shape/brand/binding/membership negatives and opaque-result checks.
They cannot create a positive open, call a renderer, or stand in for a durable
publication.  No public factory, installer, fake inventory builder, or test DI
hook exists.

The first positive canonical open is intentionally deferred: a service must
first publish the exact inventory durably, then `AuthorizationPortV1` must
verify the canonical-read receipt and issue/verify a cursor when applicable,
and only then may `ProjectionPortV1` and the resolver consume a verified grant.
The frozen trace-inventory candidate is excluded from this kernel because its
aliased-object limit bypass invalidates unique-membership proof; it supplies no
strict-trace completion evidence.
