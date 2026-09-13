<!-- codex-design -->
# Detail design: Simple distributed textual databases

**Date:** 2026-09-13  
**Selection:** Authority A + Adapters A + Operating B + Retention A  
**Status:** Design only; all types and paths below are proposed unless explicitly identified as existing

## 1. Purpose and boundaries

This design defines the reusable SCV protocol beneath a Git-backed, local-first textual database. Git establishes replicated bytes, jj manages local revision work, SCV supplies identity, validation, reduction, settlement, evidence, bridges, and retention, and SJ remains the only local checkout mutation owner. GitHub Git and GitHub Actions are the first live adapters. Other Git and CI systems enter through capability-tested interfaces rather than provider conditions in the semantic core.

The pure core has no filesystem, Git, jj, subprocess, network, clock, credential, provider SDK, or raw-runtime dependency. It accepts immutable values and returns immutable plans/results. App-layer orchestration performs effects through existing environment/process/HAL facades and submits local mutations through the existing SJ lease/capsule. Existing `ChangeIdentity` and `RevisionIdentity` remain canonical SCV identities; compact database aliases are an additional lookup representation.

The initial durable data workspace is a sibling `simple-data` repository, not a submodule. Canonical Git contains semantic history and evidence manifests. Raw high-volume evidence lives in a controlled content-addressed store (CAS).

## 2. Logical package layout

Exact placement is chosen during implementation after dependency checks, but ownership is fixed:

```text
src/lib/scv/db/
    identity_map.spl          # pure identity values and map transitions
    canonical_encoding.spl   # pure canonical encoder/decoder
    patch.spl                # DbPatch and typed operations
    schema.spl               # keys, references, ACL and merge declarations
    merge_policy.spl         # pure authorization-independent merge planner
    reducer.spl              # pure incremental/full materialization
    settlement.spl           # pure candidate planning and receipt validation
    evidence.spl             # immutable config/test/evidence values
    bridge.spl               # provider-neutral intent/binding transitions
    retention.spl            # pure rollup, pins, resolution and resnapshot plans
    errors.spl               # closed protocol error algebra
src/lib/scv/db/port/
    git_settlement_transport.spl
    ci_observation_source.spl
    evidence_store.spl
    provider_bridge.spl
src/app/scv/db/
    command orchestration and adapters
```

The implementation should reuse or extend `src/lib/scv/lifecycle/sync.spl` model/store/codec neighbors for lifecycle field planning and `LifecycleOutboxEvent`. It should extend `src/lib/scv/metadata_db.spl` behind a batched compatibility boundary instead of adding a second live metadata writer. Configuration/evidence support should extend `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`. SJ integration should use its existing client, protected-ref policy, integration planning, and repository lease rather than invoking jj or Git from the reducer.

## 3. Common scalar types

All `*Id`, digest, signature, and revision values are validated wrappers rather than interchangeable `text` in implementation.

```simple
struct DatabaseNamespace: bytes: [u8]       # exactly 16 canonical bytes
struct AuthorityEpoch: value: u64
struct EntityKind: value: text              # schema-known ASCII token
struct ActorIncarnation: bytes: [u8]         # at least 128 random bits
struct ActorCounter: value: u64
struct BatchId: digest: Digest
struct SemanticRevision: digest: Digest
struct SchemaRevision: digest: Digest
struct ReducerRevision: digest: Digest
struct TreeId: algorithm: text, bytes: [u8]
struct CommitId: object_format: text, bytes: [u8]
struct KeyId: value: text
struct Digest: algorithm: text, version: u32, bytes: [u8]
struct Signature: algorithm: text, version: u32, bytes: [u8]
struct CanonicalInstant: unix_ns: i64        # evidence only; never merge order
```

Digests and signatures always carry algorithm/version. No protocol field assumes SHA-1 or a fixed Git object format.

## 4. Identity model

### 4.1 Exact shared interfaces

```simple
enum EntityRef:
    ProvisionalRef(
        namespace: DatabaseNamespace,
        kind: EntityKind,
        actor: ActorIncarnation,
        counter: ActorCounter,
    )
    SettledRef(
        namespace: DatabaseNamespace,
        epoch: AuthorityEpoch,
        kind: EntityKind,
        sequence: u64,
    )

struct AliasBinding:
    provisional: EntityRef
    settled: EntityRef
    settlement_batch: BatchId

enum EntityDisposition:
    Live
    Tombstoned(tombstone_batch: BatchId)
    MergedInto(target: EntityRef, batch: BatchId)
    SplitInto(targets: [EntityRef], batch: BatchId)

struct AllocatorMark:
    namespace: DatabaseNamespace
    epoch: AuthorityEpoch
    kind: EntityKind
    high_water: u64

struct AcceptedBatch:
    batch_id: BatchId
    canonical_digest: Digest
    semantic_revision: SemanticRevision
    settlement_batch: BatchId?

struct IdentityMap:
    forward: Map<EntityRef, EntityRef>
    reverse: Map<EntityRef, EntityRef>
    allocators: Map<(DatabaseNamespace, AuthorityEpoch, EntityKind), AllocatorMark>
    accepted: Map<BatchId, AcceptedBatch>
    dispositions: Map<EntityRef, EntityDisposition>
```

Required pure operations:

```simple
trait IdentityMapProtocol:
    fn resolve(map: IdentityMap, ref: EntityRef) -> Result<EntityRef, DbError>
    fn reverse_resolve(map: IdentityMap, settled: EntityRef) -> Result<EntityRef, DbError>
    fn validate_new_ref(map: IdentityMap, ref: EntityRef) -> Result<(), DbError>
    fn plan_allocation(map: IdentityMap, refs: [EntityRef], authority: AuthorityContext) -> Result<AllocationPlan, DbError>
    fn apply_allocation(map: IdentityMap, plan: AllocationPlan) -> Result<IdentityMap, DbError>
    fn apply_disposition(map: IdentityMap, ref: EntityRef, disposition: EntityDisposition) -> Result<IdentityMap, DbError>
```

`resolve` follows merge/split knowledge with a bounded visited set. It returns a typed ambiguity for a split, never chooses a target. Allocation sorts new provisional references by their canonical bytes, increments the persisted per-kind high-water mark, rejects overflow, and never scans live rows to discover the next value. Actor state persists `(namespace, incarnation, last_counter)` atomically. A restored/cloned state that cannot prove exclusive monotonic continuation rotates incarnation before issuance.

A textual bare sequence is accepted only beneath a versioned file/table header that binds namespace, epoch, and kind. Otherwise decoding returns `MissingReferenceContext`.

## 5. Patch, schema, authorization, and merge

### 5.1 Patch interfaces

```simple
struct DbPatch:
    batch_id: BatchId
    namespace: DatabaseNamespace
    epoch: AuthorityEpoch
    actor: ActorIncarnation
    actor_counter: ActorCounter
    base_revision: SemanticRevision
    causal_dependencies: [BatchId]
    schema_revision: SchemaRevision
    reducer_revision: ReducerRevision
    operations: [DbOperation]
    payload_digest: Digest
    signer: KeyId
    signature: Signature
    provenance: Provenance

enum DbOperation:
    Create(entity: EntityRef, kind: EntityKind, fields: Map<FieldId, Value>)
    UpdateFields(entity: EntityRef, edits: [FieldEdit], precondition: RowPrecondition)
    AddSetMember(entity: EntityRef, field: FieldId, member: Value, dot: CausalDot)
    RemoveObservedSetMember(entity: EntityRef, field: FieldId, observed: [CausalDot])
    AppendObservation(observation: Observation)
    Tombstone(entity: EntityRef, precondition: RowPrecondition)
    ResolveConflict(conflict: ConflictId, resolution: ConflictResolution)
    BindExternalIdentity(binding: ProviderBinding)

struct FieldEdit:
    field: FieldId
    before: ValueDigest?
    after: Value

struct RowPrecondition:
    base_row: ObjectRef?          # retrievable base values, not digest alone
    expected_revision: SemanticRevision?
    expected_fields: Map<FieldId, ValueDigest>

struct CausalDot:
    actor: ActorIncarnation
    counter: ActorCounter
```

Operation order is significant within one patch. Dependencies are topologically ordered across patches; canonical batch-ID bytes break ties only among causally independent ready patches. Settlement order never replaces the declared causal graph.

### 5.2 Schema and merge policy

```simple
enum FieldMergeRule:
    ScalarConflict
    AuthorityWins(authority: AuthorityRuleId)
    OrderedListConflict
    ObservedRemoveSet
    AddWinsSet
    RemoveWinsSet
    AppendByStableIdentity(identity_fields: [FieldId])
    Derived(reducer: ReducerFunctionId)

struct EntitySchema:
    kind: EntityKind
    key_fields: [FieldId]
    fields: Map<FieldId, FieldSchema>
    references: [ReferenceConstraint]
    uniqueness: [UniqueConstraint]
    tombstone_policy: TombstonePolicy

struct MergePolicy:
    schema_revision: SchemaRevision
    reducer_revision: ReducerRevision
    entities: Map<EntityKind, EntitySchema>
    field_authorities: Map<AuthorityRuleId, FieldAuthorityRule>

struct AuthorizedPatch:
    patch: DbPatch
    authorization_receipt: AuthorizationReceipt

struct MergeInput:
    current: MaterializedState
    authorized_patch: AuthorizedPatch
    identity_map: IdentityMap
    policy: MergePolicy

struct MergePlan:
    ordered_effects: [MaterializedEffect]
    conflicts: [DbConflict]
    new_revision: SemanticRevision
    audit: [DecisionRecord]

trait SemanticReducer:
    fn validate_patch(patch: DbPatch, schema: SchemaCatalog) -> Result<ValidatedPatch, DbError>
    fn plan_merge(input: MergeInput) -> Result<MergePlan, DbError>
    fn apply_plan(state: MaterializedState, plan: MergePlan) -> Result<MaterializedState, DbError>
    fn full_materialize(checkpoint: Checkpoint, log: [AuthorizedPatch], policy: MergePolicy) -> Result<MaterializedState, DbError>
```

Authentication and authorization happen before construction of `AuthorizedPatch`. The merge planner cannot accept a raw `DbPatch`, preventing an authority hint inside data from granting permission. Authorization verifies signature/key state, ACL, namespace/epoch, allowed operation/entity/field scope, and CI restrictions.

`ScalarConflict` permits equal concurrent results and different-field merging but preserves incompatible same-field edits. Delete/update creates a conflict or retains the schema-selected tombstone; it never silently resurrects. Append collections deduplicate by schema-declared stable identity. Derived values are recomputed from deduplicated inputs. Natural-key collision across distinct UIDs is a conflict unless an explicit equivalence operation is authorized.

## 6. Canonical encoding

Canonical bytes, not the human SDN projection, are signed and hashed. The encoding is `SCVDB-CANON-v1`:

1. Prefix every root with ASCII domain plus NUL: `scv-db/<type>/v1\0`.
2. Encode each value as one-byte type tag, unsigned varint byte length, then payload.
3. Integers use minimal unsigned/signed varint form; non-minimal encodings are invalid.
4. Text is valid UTF-8 normalized to NFC. Entity/schema identifiers that require ASCII reject non-ASCII rather than normalize.
5. Struct fields appear in schema field-number order. Unknown required fields fail; declared extension fields are retained and ordered by field number.
6. Maps sort by the complete canonical key bytes; duplicate canonical keys fail. Sets sort unique canonical member bytes. Lists preserve order.
7. Optional absent and present-empty have distinct tags. Floating-point evidence, if admitted, uses canonical IEEE-754 binary64, normalizes negative zero, and rejects NaN unless the schema defines one canonical NaN.
8. Digests bind repository identity, namespace, epoch, schema revision, reducer revision, and object domain to prevent cross-domain replay.

`batch_id` is derived from canonical patch content excluding `batch_id`, `payload_digest`, and `signature`. `payload_digest` covers the same domain-separated bytes. The signature covers the digest plus signer/key-algorithm metadata. A known batch ID with unequal canonical digest is `BatchIdentityCollision` and is quarantined.

SDN is a deterministic textual projection for review/editing. Projection files declare encoding version and contextual reference header. Manual edits are diffed against the recorded projection revision, converted into typed operations, and validated; arbitrary file replacement never bypasses patch admission.

## 7. Settlement

### 7.1 Values and transport port

```simple
struct AuthorityContext:
    repository: RepositoryIdentity
    namespace: DatabaseNamespace
    epoch: AuthorityEpoch
    settled_ref: text
    signer: KeyId

struct SettlementHead:
    commit: CommitId
    tree: TreeId
    receipt: SettlementReceipt
    acknowledgement: SettlementAcknowledgement
    identity_map: IdentityMap
    semantic_revision: SemanticRevision

struct GitRefHead:
    commit: CommitId
    tree: TreeId
    parent: CommitId?

struct SettlementCandidate:
    expected_head: CommitId
    sole_parent: CommitId
    tree: TreeId
    candidate_commit: CommitId
    accepted_batches: [BatchId]
    allocations: [AliasBinding]
    resulting_high_water: [AllocatorMark]
    semantic_revision: SemanticRevision
    receipt: SettlementReceipt

struct SettlementReceipt:
    subject: SettlementReceiptSubject
    signature: Signature

struct SettlementReceiptSubject:
    repository: RepositoryIdentity
    namespace: DatabaseNamespace
    epoch: AuthorityEpoch
    parent: CommitId
    candidate_tree: TreeId
    previous_receipt: Digest?       # digest of prior accepted receipt subject
    allocator_marks: [AllocatorMark]
    schema_revision: SchemaRevision
    reducer_revision: ReducerRevision
    batch_set_digest: Digest

struct SettlementAcknowledgement:
    receipt_digest: Digest
    accepted_commit: CommitId
    accepted_tree: TreeId
    settled_ref: text
    observed_parent: CommitId
    authority_signer: KeyId
    signature: Signature

struct ReceiptIndexEntry:
    accepted_commit: CommitId
    receipt: SettlementReceipt
    acknowledgement: SettlementAcknowledgement

struct ReceiptIndexHead:
    ref: text
    commit: CommitId
    tree: TreeId
    last_entry: Digest?
    entry_count: u64

struct ReceiptIndexCandidate:
    expected_index_head: CommitId
    sole_parent: CommitId
    tree: TreeId
    candidate_commit: CommitId
    entry: ReceiptIndexEntry

enum ReceiptIndexPublishResult:
    ReceiptIndexed(index_head: CommitId)
    IndexHeadAdvanced(actual_head: CommitId)
    IndexOutcomeUncertain(correlation: text)

enum PublishResult:
    Published(observed_head: CommitId)
    HeadAdvanced(actual_head: CommitId)
    OutcomeUncertain(correlation: text)

struct GitTransportCapabilities:
    object_format: text
    exact_head_fetch: bool
    expected_old_oid_update: bool
    force_protected: bool
    delete_protected: bool
    read_back: bool
    admitted_single_integrator: bool
    receipt_index_append: bool
    maximum_object_bytes: u64
    maximum_update_bytes: u64

trait GitSettlementTransport:
    fn capabilities(remote: SettlementRemote) -> Result<GitTransportCapabilities, DbError>
    fn fetch_ref_head(remote: SettlementRemote, ref: text) -> Result<GitRefHead, DbError>
    fn fetch_exact_head(remote: SettlementRemote, ref: text) -> Result<SettlementHead, DbError>
    fn publish_candidate(remote: SettlementRemote, candidate: SettlementCandidate) -> Result<PublishResult, DbError>
    fn verify_accepted_batch(remote: SettlementRemote, ref: text, batch: BatchId) -> Result<AcceptedSettlement, DbError>
    fn fetch_receipt_index_head(remote: SettlementRemote, receipt_ref: text) -> Result<ReceiptIndexHead, DbError>
    fn fetch_receipt_entry(remote: SettlementRemote, receipt_ref: text, commit: CommitId) -> Result<ReceiptIndexEntry, DbError>
    fn fetch_receipt_by_digest(remote: SettlementRemote, digest: Digest) -> Result<ReceiptIndexEntry, DbError>
    fn append_receipt_entry(remote: SettlementRemote, candidate: ReceiptIndexCandidate) -> Result<ReceiptIndexPublishResult, DbError>
```

On GitHub-hosted authorities, these transport methods are called only by a trusted, version-pinned SCV settlement worker authenticated as a repository-scoped GitHub App. The deployment policy pins the worker artifact digest and its supported schema/reducer revisions; startup attestation must match that policy before the App credential is made available. That worker verifies the complete `SettlementReceiptSubject`, patch authorization, reducer result, constraints, and candidate bytes before it permits the protected settled-ref update. GitHub supplies branch/ref policy, credential isolation, expected-old-OID update behavior, and read-back; GitHub does not run an SCV semantic merge hook and is not assumed to understand allocator or schema invariants. The App installation and protected-ref policy deny ordinary producer credentials direct settlement and receipt-index writes. An optional self-hosted pre-receive hook may repeat validation as defense in depth, but correctness and portability never depend on it.

### 7.2 Planning and publication algorithm

1. Outside the SJ lease, fetch exact canonical head and transport capabilities. Fail closed unless force/delete protection, receipt-index append/read, and either expected-old-OID CAS or admitted single-integrator semantics are proven, and read-back exists.
2. Fetch the receipt-index entry for the fetched head. Validate both signatures; require the acknowledgement's commit/tree/parent to equal the fetched commit/tree/parent and its receipt digest to equal the canonical receipt-subject digest. Follow `previous_receipt` through index entries to the trusted checkpoint and reject ancestry, namespace/epoch, version, or allocator regression.
3. Decode pending immutable patches from quarantine. Enforce quotas, verify canonical digest/signature/ACL, and construct `AuthorizedPatch` values.
4. Under a short SJ repository lease, confirm the local data workspace still represents fetched head `H`; create or refresh the candidate workspace. Release the lease before any remote wait.
5. Pure planning resolves known aliases, topologically orders patches, merges, validates constraints/reference closure, allocates genuinely new references deterministically, rewrites typed references, and constructs one tree containing state, maps, dispositions, allocator marks, and accepted registry. The candidate tree contains the prior accepted receipt digest, but no receipt or acknowledgement for itself.
6. Under a short SJ lease, materialize candidate commit `P` with sole parent `H`; release it. Now that the candidate tree digest is final, construct and sign `SettlementReceiptSubject(repository, namespace, epoch, H, candidate_tree, previous_receipt, high_water_marks, schema, reducer, batch_set_digest)`. The signed receipt travels with the publication request; it is not claimed to be inside the candidate tree.
7. Submit the candidate and signed subject to the pinned settlement worker. It independently decodes and validates the canonical subject, checks that `parent == H`, recomputes the candidate tree, patch set, allocator marks, schema/reducer result, ACL, and reference closure, and only then publishes without force using expected old OID `H`. Do not hold SJ/DB leases during network I/O. GitHub protection/CAS rejects a racing update; it is not the semantic validator.
8. On `OutcomeUncertain`, enter `verification_required`; perform read-back by original batch IDs and candidate commit before any replan. If accepted, create/fetch a separately signed acknowledgement that binds receipt digest to observed accepted commit/tree/ref/parent. If not provably accepted or rejected, remain uncertain and allocate nothing.
9. Append the receipt plus acknowledgement to the authority-owned receipt index using the independent protocol below. Until the entry is fetched and verified, the settled head is accepted-but-unacknowledged and cannot be used as an allocation base. Under an SJ lease, advance the local projection and cached receipt index only after that verification.

`SettlementHead` therefore means a fetched settled commit/tree together with its separately fetched, fully verified receipt-index entry. The signed subject and signed acknowledgement jointly constitute settlement receipt evidence: the former chains policy/allocation/tree state, and the latter binds that subject to the accepted commit OID. `fetch_ref_head` is the raw read-back primitive used to detect an accepted-but-unacknowledged commit; `fetch_exact_head` composes that read with receipt-index verification and must not return success for an unacknowledged head. Recovery may reconstruct a missing acknowledgement only after proving that the exact signed subject's candidate tree is the accepted commit tree and its parent is the subject parent; it then appends one idempotent index entry. Receipt-index keys are receipt-subject digests; replay of the same entry is a no-op and a second commit/subject under one key is quarantined. The commit never contains its own OID, receipt, or acknowledgement, so there is no self-reference or false atomic-inclusion claim.

### 7.3 Protected receipt-index protocol

Each `(repository, namespace, authority epoch)` has exactly one configured receipt ref, initially `refs/scv/receipts/<namespace>/<epoch>`. It is distinct from `settled`, protected against force and deletion, and writable only by the settlement GitHub App/authority credential. Its commits form a linear append-only chain. Each commit has exactly one parent (except the signed genesis checkpoint) and adds exactly one immutable entry at `entries/<receipt-subject-digest>`, plus secondary `by-commit/<accepted-commit>` and ordered `sequence/<zero-padded-entry-count>` records. All three records must resolve to identical canonical entry bytes. The entry count increments by one, and the new entry's subject `previous_receipt` must equal the prior index head's `last_entry`. The acknowledged settled commit must be the unique next child in the settled ancestry represented by the prior entry. Receipt-index commits contain no mutable in-place row.

Receipt publication is a second transaction with its own expected-old OID, independent of the settled-ref CAS:

1. Before updating `settled`, the trusted worker durably stores the validated candidate, signed subject, expected settled head, and current receipt-index head in its recovery journal. Producer acknowledgement has not occurred.
2. After read-back proves `P` is the settled head, the worker signs `SettlementAcknowledgement(receipt_digest, P, candidate_tree, settled_ref, H, authority_signer)` and fetches receipt-index head `R`.
3. If either index lookup by receipt digest or accepted commit already returns the same verified semantic entry, indexing is an idempotent success. If only one secondary key exists, bytes differ, or either key names another subject/commit, quarantine as receipt-index corruption.
4. Otherwise construct index commit `I` with sole parent `R`, validate chain/sequence/settled ancestry, and update the receipt ref using expected old OID `R`, never force.
5. On `IndexHeadAdvanced`, fetch the new index head. If the desired entry is now present, succeed; otherwise validate every intervening append and rebuild one candidate on the new head. Bounded orchestration retry applies, but entry ordering is always settled ancestry order rather than arrival time.
6. On `IndexOutcomeUncertain` or a lost acknowledgement from the Git host, read both receipt-digest and commit indexes before retrying. Never append a second logical entry. If the update is neither provably accepted nor rejected, retain the recovery journal and block further allocation.
7. Only after read-back verifies `I`, all three indexes, signatures, and their protected-ref ancestry may the worker acknowledge settlement to the submitter and project the accepted IDs locally.

If `P` is accepted but its receipt entry is missing (worker crash between the two CAS operations), recovery treats the settled ref as frozen. The pinned worker reads the durable journal or deterministically reconstructs the subject fields from `P`, `H`, the accepted-batch delta, allocator state, and schema/reducer identifiers; it verifies that reconstructed canonical bytes equal any retained signed subject. It then signs or reuses the acknowledgement and runs the receipt-index CAS protocol. If reconstruction is ambiguous, the required signing key is unavailable/revoked, or `P` fails semantic revalidation, recovery fails closed for operator repair; it does not roll back `settled`, advance it, or allocate new numbers. A periodic reconciler checks for this accepted/index-missing state, but polling is recovery latency reduction rather than correctness authority.

Settlement state transitions:

```text
discovered -> validated -> planned -> candidate_local -> publishing
publishing -> head_advanced -> replanning
publishing -> verification_required
verification_required -> accepted_verified -> receipt_indexed -> projected
verification_required -> rejected_verified | uncertain
accepted_verified -> receipt_recovery_required -> receipt_indexed
any pre-publication state -> quarantined | conflicted
```

Recovery first loads local intent, then fetches canonical history. Canonical accepted-batch membership dominates local phase markers. Regression or inability to fence a restored authority returns `AuthorityRegression`; operators must establish a new namespace rather than mint under ambiguous history.

## 8. Configuration-aware evidence

```simple
struct RevisionRef<T>:
    entity: EntityRef
    revision: Digest

struct TestDefinitionRevision:
    test: EntityRef
    revision: Digest
    definition: ObjectRef

struct ConfigRevision:
    config: EntityRef
    revision: Digest
    effective_values: Map<ConfigKey, RedactedValue>
    base: RevisionRef<ConfigRevision>?

struct ConfigSetRevision:
    config_set: EntityRef
    revision: Digest
    members: [RevisionRef<ConfigRevision>]

struct ReproductionRevision:
    reproduction: EntityRef
    revision: Digest
    source: SourceSnapshotRef
    test_definition: RevisionRef<TestDefinitionRevision>
    argv: [text]
    input_dependencies: [EvidenceDependency]
    seed: text?
    toolchain: [ObjectRef]
    config: RevisionRef<ConfigRevision>
    device_state: ObjectRef?

struct RunManifest:
    run: EntityRef
    revision: Digest
    provider_identity: ProviderObservationIdentity
    source_revision: SourceSnapshotRef
    test_definitions: [RevisionRef<TestDefinitionRevision>]
    config_set: RevisionRef<ConfigSetRevision>
    expectation_revision: RevisionRef<ExpectationRevision>
    planned_cases: [CaseRef]
    chunks: [EvidenceChunk]
    completion: RunCompletion
    missing_shards: [text]
    supersedes: RevisionRef<RunManifest>?
    artifacts: [EvidenceDependency]

struct Observation:
    observation: EntityRef
    revision: Digest
    provider_identity: ProviderObservationIdentity
    source_revision: SourceSnapshotRef
    test_definition: RevisionRef<TestDefinitionRevision>
    config_revision: RevisionRef<ConfigRevision>
    case: CaseRef
    run: RevisionRef<RunManifest>
    attempt: u32
    actual: ActualOutcome
    measurements: [Measurement]
    reproduction: RevisionRef<ReproductionRevision>?
    payload_digest: Digest

struct ExpectationRevision:
    expectation: EntityRef
    revision: Digest
    reviewed_by: KeyId
    rules: [ExpectationRule]

struct ExpectationRule:
    test: RevisionRef<TestDefinitionRevision>
    config_set: RevisionRef<ConfigSetRevision>?
    exact_config: RevisionRef<ConfigRevision>?
    expected: ExpectedOutcome
    failure_signature: RevisionRef<FailureSignatureRevision>?
    bug: EntityRef?
    reproduction: RevisionRef<ReproductionRevision>?
    priority: u32
    review_after: CanonicalInstant?

struct OutcomeEvaluation:
    observation: RevisionRef<Observation>
    expectation_revision: RevisionRef<ExpectationRevision>
    classification: OutcomeClass
    rule_digest: Digest?

struct BugOccurrence:
    bug: EntityRef
    observation: RevisionRef<Observation>
    config_revision: RevisionRef<ConfigRevision>
    reproduction: RevisionRef<ReproductionRevision>

enum OutcomeClass:
    Pass
    KnownFailure
    UnexpectedPass
    SignatureMismatch
    UnexpectedFailure
    InfrastructureError
    NotRun
    Incomplete
    Unclassified
```

`RevisionRef<T>` is the only cross-entity reference to an immutable revision: both its stable entity identity and content revision digest participate in canonical encoding, reference closure, and authorization. A digest alone cannot substitute for it, and a bare entity reference resolves no moving "latest" value. Embedded expectation rules are addressed by their canonical `rule_digest` within the referenced `ExpectationRevision`; they are not independently mutable entities.

All named profiles resolve to immutable revisions at run start. Custom failures require non-optional configuration and reproduction revision references at admission. Reproduction dependencies record digest plus `available | restricted | expired | missing`; a mutable jj change ID or private path is insufficient. CI keys observations by adapter-declared provider tuple. Same tuple/digest is idempotent; same tuple/different digest is quarantined.

Evaluation never alters observations. Expectation rules choose exact config before frozen config-set default; equal-priority contradictory matches are invalid. Outside-set behavior is explicit. A terminal manifest is the only basis for complete planned coverage; absent records are `NotRun`/`Incomplete`, never pass. CI signer roles cannot authorize expectation, bug-closing, configuration-promotion, or release-qualification operations.

The `RunnerTestDb` compatibility extension accepts optional immutable references during migration and writes both legacy views and new semantic entities in one SJ-owned batch. Readers select a source/test revision before calculating current status, preventing late old-code results from replacing current evidence.

## 9. CI ingestion and adapter capabilities

```simple
struct CiSourceCapabilities:
    identity_dimensions: [IdentityDimension]
    uniqueness_tuple: [IdentityDimension]
    event_hints: bool
    polling: bool
    bundle_import: bool
    artifact_download: bool
    attestations: bool
    pagination: PaginationCapability
    retention: RetentionCapability
    maximum_bundle_bytes: u64

struct CiCursor:
    provider_instance: ProviderInstance
    opaque_position: text
    overlap_from: CanonicalInstant

struct NormalizedRunEnvelope:
    provider_identity: ProviderObservationIdentity
    manifest: RunManifest
    chunks: [EvidenceChunk]
    attestations: [Attestation]

trait CiObservationSource:
    fn capabilities(source: CiSource) -> Result<CiSourceCapabilities, DbError>
    fn discover(source: CiSource, cursor: CiCursor?) -> Result<DiscoveryPage, DbError>
    fn fetch_bundle(source: CiSource, item: DiscoveryItem, quota: ImportQuota) -> Result<QuarantinedBundle, DbError>
    fn normalize(bundle: ValidatedBundle) -> Result<NormalizedRunEnvelope, DbError>
```

GitHub Actions is the first live implementation. Fixtures must also exercise GitLab-CI identity/event semantics, Jenkins-class poll/bundle semantics, and a non-GitHub Git authority. Capabilities, not provider name, determine behavior.

Before producer acknowledgement, a content-addressed immutable manifest is discoverable. Webhooks enqueue only a hint. Polling uses pagination plus overlap windows; cursor advancement occurs after normalized input is locally durable and canonical acceptance is verified. Bundle handling streams into CAS quarantine outside the checkout and enforces configured byte, file, record, depth, path, Unicode, decompression-ratio, and time limits. Links and devices are rejected. Import never executes supplied content.

## 10. Bug/provider bridge

```simple
struct ProviderCapabilities:
    create_idempotency: IdempotencyCapability
    conditional_update: bool
    revisions_or_etags: bool
    event_delivery: bool
    polling: bool
    pagination: PaginationCapability
    supported_fields: Set<FieldId>

struct ProviderBinding:
    binding: EntityRef
    local_entity: EntityRef
    provider_instance: ProviderInstance
    project: text
    remote_kind: text
    remote_id: text
    remote_revision: text?
    last_common_state: ObjectRef
    capability_digest: Digest
    authority_policy: EntityRef

enum BridgeState:
    Pending
    Leased
    SentUnconfirmed
    Acknowledged
    Conflicted
    Quarantined

struct BridgeIntent:
    intent: EntityRef
    revision: Digest
    binding: EntityRef?
    operation: ProviderOperation
    idempotency_key: text
    correlation_id: text
    causation_id: text?
    payload_digest: Digest

struct BridgeDelivery:
    delivery_id: Digest
    format_version: u32
    intent: RevisionRef<BridgeIntent>
    provider_instance: ProviderInstance
    state: BridgeState
    lease_owner: ReplicaId?
    lease_generation: u64
    lease_expires: CanonicalInstant?
    attempt_count: u32
    next_attempt: CanonicalInstant?
    last_provider_revision: RemoteRevision?
    provider_receipt: ProviderReceipt?
    conflict: ConflictId?
    last_error_code: text?
    updated_at: CanonicalInstant

trait BridgeDeliveryStore:
    fn create(intent: RevisionRef<BridgeIntent>, provider: ProviderInstance) -> Result<BridgeDelivery, DbError>
    fn acquire(delivery: Digest, owner: ReplicaId, now: CanonicalInstant, ttl_ns: i64) -> Result<BridgeDelivery, DbError>
    fn mark_sent_unconfirmed(delivery: Digest, owner: ReplicaId, generation: u64, correlation: text) -> Result<BridgeDelivery, DbError>
    fn acknowledge(delivery: Digest, owner: ReplicaId, generation: u64, receipt: ProviderReceipt) -> Result<BridgeDelivery, DbError>
    fn conflict(delivery: Digest, owner: ReplicaId, generation: u64, conflict: ConflictId) -> Result<BridgeDelivery, DbError>
    fn quarantine(delivery: Digest, owner: ReplicaId?, generation: u64?, error: DbError) -> Result<BridgeDelivery, DbError>
    fn release_for_retry(delivery: Digest, owner: ReplicaId, generation: u64, next: CanonicalInstant, error_code: text) -> Result<BridgeDelivery, DbError>

trait ProviderBridge:
    fn capabilities(provider: ProviderInstance) -> Result<ProviderCapabilities, DbError>
    fn read_remote(provider: ProviderInstance, binding: ProviderBinding) -> Result<RemoteSnapshot, DbError>
    fn deliver(provider: ProviderInstance, intent: BridgeIntent, expected: RemoteRevision?) -> Result<DeliveryResult, DbError>
    fn reconcile(provider: ProviderInstance, binding: ProviderBinding, cursor: ProviderCursor?) -> Result<ReconciliationPage, DbError>
```

Canonical `BridgeIntent` is committed atomically with the semantic edit, using the existing lifecycle envelope fields for correlation, causation, idempotency, provider delivery ID, and payload digest. Lease owner, retry count, next attempt, and jitter are replica-local and never merge into canonical business state.

`BridgeDelivery` is the exact replica-local ownership record for one `(intent revision, provider instance)`. Its `delivery_id` is the domain-separated digest of that pair. It is serialized as `SCVDB-BRIDGE-LOCAL-v1` canonical bytes in the local SCV WAL/store and is never committed to the shared semantic log. Only the canonical intent, provider binding updates, and acknowledged provider receipt enter replicated patches. Every leased transition compares `(lease_owner, lease_generation)`; stale workers cannot acknowledge or reschedule after ownership changes. Legal transitions are `Pending -> Leased`, `Leased -> SentUnconfirmed | Acknowledged | Conflicted | Quarantined | Pending`, and `SentUnconfirmed -> Leased | Acknowledged | Conflicted | Quarantined`. `Acknowledged`, `Conflicted`, and `Quarantined` are terminal for that delivery record; a reviewed corrective action creates a new intent/delivery. Acquisition after expiry increments the generation. Store migration decodes the old version, derives all missing fields without provider I/O, writes a new generation atomically, and retains the old generation until recovery commit; unsupported or lossy versions fail closed.

Bridge execution obtains a short local delivery lease, reads intent, releases DB/SJ locks, calls the provider, then records the result in a new controlled transaction. Timeout after a potentially successful create becomes `SentUnconfirmed`; read-back reconciliation precedes retry. Where native idempotency is absent, use a stable correlation marker, one outbound owner, read-back, and explicit uncertainty. Permission failure, inaccessible/filtered result, and confirmed deletion are distinct results. Per-field policy performs three-way comparison against retrievable `last_common_state`; incompatible shared scalar changes become conflicts. Stable provider/causation IDs suppress echoes without suppressing every bot-authored event.

## 11. Retention and evidence CAS

```simple
enum EvidenceAvailability:
    Available
    Restricted
    Expired
    Missing

struct EvidenceDependency:
    object: ObjectRef
    availability: EvidenceAvailability
    locations: [EvidenceLocation]

struct RetentionClass:
    name: text
    exact_days: u32?
    pin_policy: PinPolicy
    rollup_policy: RollupPolicy?

struct EvidencePin:
    root: ObjectRef
    reason: PinReason
    dependency_closure_digest: Digest
    expires: CanonicalInstant?

struct DailyCohortRollup:
    rollup: EntityRef
    content_revision: Digest
    day: text
    cohort: Digest
    aggregation_revision: ReducerRevision
    input_set_digest: Digest
    counts: Map<OutcomeClass, u64>
    timing: MergeableTimingSketch
    generation: u32
    provenance: [ObjectRef]

struct RetentionCatalog:
    catalog: EntityRef
    revision: Digest
    format_version: u32
    policy_revision: Digest
    classes: Map<text, RetentionClass>
    assignments: Map<ObjectRef, text>
    pins: Map<ObjectRef, [EvidencePin]>
    availability: Map<ObjectRef, EvidenceAvailability>
    rollups: Map<(text, Digest), RevisionRef<DailyCohortRollup>>
    resnapshot_checkpoints: [ResnapshotCatalogEntry]
    history_horizon: SemanticRevision

struct RetentionPlan:
    base_catalog: RevisionRef<RetentionCatalog>
    now: CanonicalInstant
    deletions: [ObjectRef]
    required_rollups: [DailyCohortRollup]
    protected_by_pin: [ObjectRef]
    resolution_changes: [ResolutionChange]
    plan_digest: Digest

trait RetentionCatalogProtocol:
    fn plan(catalog: RetentionCatalog, inventory: EvidenceInventory, now: CanonicalInstant) -> Result<RetentionPlan, DbError>
    fn authorize(plan: RetentionPlan, policy: RetentionPolicy, actor: KeyId) -> Result<AuthorizedRetentionPlan, DbError>
    fn record_rollups(catalog: RetentionCatalog, plan: AuthorizedRetentionPlan) -> Result<RetentionCatalog, DbError>
    fn record_deletion(catalog: RetentionCatalog, plan: AuthorizedRetentionPlan, receipts: [DeletionReceipt]) -> Result<RetentionCatalog, DbError>
    fn query_resolution(catalog: RetentionCatalog, object: ObjectRef, requested: SemanticRevision) -> QueryResolution
    fn migrate(catalog: RetentionCatalog, target_version: u32) -> Result<RetentionCatalog, DbError>

enum QueryResolution:
    Exact
    Aggregated
    Restricted
    Unavailable

trait EvidenceStore:
    fn put(stream: ByteStream, expected: Digest, quota: EvidenceQuota) -> Result<ObjectRef, DbError>
    fn stat(object: ObjectRef) -> Result<EvidenceAvailability, DbError>
    fn hydrate(object: ObjectRef, target: QuarantineTarget) -> Result<HydratedEvidence, DbError>
    fn verify_closure(root: ObjectRef) -> Result<ClosureReceipt, DbError>
```

`RetentionCatalog` is immutable canonical semantic state owned by the pure retention reducer and mutated only by authorized `DbPatch` operations through the SJ/SCV transaction path. It uses the same `SCVDB-CANON-v1` rules; its `revision` is the domain-separated digest of all fields except itself. CAS inventory and deletion execution remain adapter state and cannot directly mutate the catalog. The ordered transition is `catalog -> planned -> authorized -> rollups_recorded -> external_delete_attempted -> deletion_receipts_recorded`; failure before receipts leaves availability unchanged. A deletion receipt can move `Available` to `Expired` or `Missing`, never back to `Available`; successful verified hydration may create a new location and explicit availability patch. Migration is a pure, versioned transform with golden bytes and full/incremental equality evidence. Unknown fields round-trip only where declared optional; unsupported/lossy migration fails closed. The previous catalog revision remains reachable as semantic history.

Routine raw observations remain exact for 28 days. Before provider expiry, unresolved-failure and release pins require 100% digest-verified dependency closure in controlled CAS. Deleting raw inputs creates or revises a daily rollup with reducer revision and provenance; counts deduplicate observation identity and timing uses a mergeable histogram/sketch plus sufficient statistics. Percentiles are never averaged. Late input produces a new rollup revision and input-set digest.

Compaction is plan/preview/apply: calculate exact queries and dependencies that would be lost, require policy authorization, verify pins, apply external deletion, then record availability. Pending unsynchronized work is never age-pruned. Git history is not presented as erasable; confidentiality policy defaults-deny secrets/PII before admission, and restricted CAS supports encryption/key erasure.

Resnapshot checkpoints include canonical materialized state, complete identity aliases, allocator marks, dispositions/tombstones, schema/reducer revisions, accepted-batch horizon, and history catalog. Rebase validates every pending dependency. An operation older than the supported replay horizon receives `ResnapshotRequired`; no heuristic create/resurrection is attempted.

## 12. Transaction and lease boundaries

There are four distinct atomicity domains:

| Domain | Atomic unit | Must not include |
|---|---|---|
| Pure reducer | one immutable `MergePlan` application | I/O, clock, credentials |
| Local SCV DB | WAL-backed batched map/state replacement | network waits |
| SJ workspace | short repository lease/capsule mutation | provider/Git remote waits |
| Canonical Git | one tree/commit and protected ref update | provider HTTP side effect |

The coordinator uses an intent/effect/receipt pattern: persist intent locally, release lease, perform remote effect, read back, then commit receipt/projection through SJ. It never holds the metadata DB lock and SJ repository lease while waiting for network. Lock acquisition order, when both are momentarily necessary, is SJ repository lease then DB transaction; the reverse order is forbidden. Lease expiry does not imply a remote operation failed.

Local DB updates must expose a batch API that applies identity map, accepted registry, state/index roots, bridge intent, and WAL marker as one recoverable transaction. Projection files are replaced only after all new files are durable; recovery chooses either the old complete generation or new complete generation by committed generation marker.

## 13. Error algebra

```simple
enum DbError:
    InvalidCanonicalEncoding(detail: text)
    UnsupportedSchema(found: SchemaRevision)
    UnsupportedReducer(found: ReducerRevision)
    DowngradeRejected(found: Digest, required: Digest)
    SignatureInvalid(key: KeyId)
    KeyRevoked(key: KeyId)
    Unauthorized(operation: text, subject: text)
    NamespaceMismatch
    AuthorityEpochMismatch
    AuthorityRegression(detail: text)
    ActorCounterRegression(actor: ActorIncarnation)
    BatchIdentityCollision(batch: BatchId)
    MissingReference(ref: EntityRef)
    MissingReferenceContext(sequence: u64)
    AmbiguousSplit(ref: EntityRef)
    TombstonedReference(ref: EntityRef)
    ConstraintViolation(name: text)
    MergeConflict(conflict: ConflictId)
    DependencyCycle(batches: [BatchId])
    HeadAdvanced(expected: CommitId, actual: CommitId)
    PublicationUncertain(correlation: text)
    UnsupportedTransportCapability(name: text)
    QuotaExceeded(kind: text, limit: u64)
    ObservationIdentityCollision(identity: ProviderObservationIdentity)
    EvidenceUnavailable(object: ObjectRef, state: EvidenceAvailability)
    ProviderPermissionDenied
    ProviderObjectDeleted
    ProviderEffectUncertain(correlation: text)
    ResnapshotRequired(minimum: SemanticRevision)
    Busy(lease: text)
```

Errors are stable machine-readable codes with non-secret diagnostics and causation/correlation IDs. Retriable classification is explicit: `HeadAdvanced`, selected transport unavailability, `Busy`, and rate limiting may retry with bounds; malformed bytes, authorization, collision, regression, unknown versions, quota violations, and unresolved uncertainty fail closed.

## 14. Migration and compatibility

Migration phases are reversible until ownership cutover:

1. **Baseline:** record current metadata load/insert/save, runner paths, Git pack/clone behavior, and deployed Git/jj/gh capabilities.
2. **Shadow export:** derive new canonical entities and indexes from existing SCV metadata/test DB without changing readers. Preserve canonical `ChangeIdentity`/`RevisionIdentity` and record source digests.
3. **Differential read:** compare legacy and semantic projections for identity, reference closure, test status, and counts. Mismatch blocks progress.
4. **Dual write through one owner:** extend existing compatibility boundary to construct one semantic patch plus legacy projection inside one SJ-controlled operation. No independent watcher/writer.
5. **Reader switch:** retain documented test tracking paths via a hydration/adapter view; pin exact data revision where releases require it.
6. **Ownership cutover:** stop legacy writes, record a signed checkpoint/receipt, and make semantic state authoritative.
7. **Rollback:** before cutover, disable semantic reads and retain shadow data; after cutover, restore the last internally consistent signed checkpoint and replay accepted batches. Never roll allocator marks backward.

Schema/reducer migration requires a migration function, golden canonical bytes, old-reader behavior declaration, and equality proof between full and incremental materialization. Unknown required fields or versions are rejected. Optional extensions round-trip unchanged. Data-repository publication remains independent of source commits; a source configuration points to repository identity and may optionally pin a data revision.

## 15. Observability and security

Structured diagnostics use correlation IDs but exclude secrets, raw evidence, tokens, signatures, private paths, and unredacted provider payloads.

Counters:

- patches discovered/validated/accepted/deduplicated/quarantined/conflicted;
- provisional references allocated and alias lookup hit/miss/depth;
- settlement attempts, head races, uncertain publications, verification outcomes, and receipt regressions;
- CI bundles/bytes/records rejected by quota and cursor lag;
- observations by classification, identity collisions, incomplete manifests, and missing shards;
- bridge intents by state, retries, uncertain effects, conflicts, and reconciliation lag;
- CAS bytes by class, closure failures, pin expiry risk, rollup revisions, and query resolution;
- SJ lease wait/hold time and DB batch/WAL recovery generations.

Histograms record canonical decode, authorization, reference validation, alias/current-status/dedup query, pure reduction, 10k import, candidate construction, protected publication/read-back, reconciliation, compaction dry-run, resnapshot/rebase, and hydration time. Memory/pack/clone metrics follow the NFR fixture receipt. Debug status reports schema/reducer, authority namespace/epoch, canonical/local heads, last receipt digest, high-water marks, pending/conflict/quarantine counts, adapter capabilities, and evidence availability without exposing credentials.

Credential-bearing adapters run outside the pure core with repository/project-scoped credentials inaccessible to untrusted build steps. Transport authentication never grants semantic authorization. Quarantine parsers are streaming and bounded; reproduction content is data until a separate explicitly trusted execution command validates and hydrates it.

## 16. Complexity and performance design

Let `A` be aliases, `O` patch operations, `R` referenced entities, `D` causal edges, and `C` conflicts.

| Operation | Target complexity | Storage/index note |
|---|---:|---|
| alias resolve/reverse | expected `O(1)`, worst `O(log A)` | persisted hash/B-tree indexes; bounded disposition chain |
| batch deduplication | expected `O(1)`, worst `O(log B)` | batch ID plus canonical digest |
| causal ordering | `O(B + D)` plus ready-set tie ordering | never full-history sort on hot queries |
| validation/reduction | `O(O + R + C log C)` | schema/reference indexes loaded once per batch |
| 10k observation import | `O(O)` expected | streaming decode and batched mutation |
| current-status query | `O(log O + k)` | revision/config keyed materialized index |
| daily rollup | `O(n)` in deduplicated day/cohort inputs | mergeable sketch |
| compaction dry-run | `O(A + retained manifests + pins)` | maintenance path, bounded memory iterator |

Startup opens version/receipt headers and index roots; it does not scan all projection files or spawn one subprocess per table. Hot alias, status, and dedup requests use warm in-process indexes and do not invoke Git/jj/provider commands. Fetch, settlement, reconciliation, resnapshot, and compaction are explicit maintenance/effect paths. Index invalidation is generation-based: a verified canonical generation atomically swaps roots; cache keys include generation/schema/reducer, so no per-entry invalidation race exists. Local indexes are rebuildable and not committed on every refresh.

Acceptance uses the Operating B corpus: at least one million aliases and observations and a 10,000-observation batch. Required thresholds are p95 alias/current status <=100 ms, p95 dedup <=250 ms, import <=5 s and 256 MiB RSS, compaction dry-run <=10 s and 512 MiB RSS, and 10k-operation resnapshot/rebase <=60 s. These remain unproven until Phase 0 and three recorded acceptance runs; this document makes no benchmark claim.

## 17. Invariants and design verification

The implementation and system specs must prove:

1. Accepted sequence values are unique and never reused within namespace/epoch/kind.
2. Alias forward/reverse maps, allocator marks, dispositions, accepted registry, rewritten references, and candidate tree change atomically.
3. Canonical bytes are host-independent and bind all replay domains.
4. Full and incremental materialization yield identical canonical state/tree digests.
5. Settlement races accept at most one child of fetched head; uncertain publication is read back before allocation.
6. Observation, expectation, and evaluation authority/data remain separate; missing evidence is never pass.
7. Provider/CI replay is idempotent, mismatching reused identity is quarantined, and remote uncertainty is explicit.
8. No network operation holds an SJ/DB lease and no adapter independently mutates the checkout.
9. Exact/aggregated/restricted/unavailable query resolution is honest and pinned dependency closure is verified before expiry.
10. Existing SCV identities and documented reader paths survive migration.

This design covers REQ-001 through REQ-036 and NFR-001 through NFR-015. Architecture and system-test artifacts provide the requirement-to-scenario matrix; implementation may refine internal field representation but must preserve these named shared interfaces and behavioral contracts or update requirements/design and receive review first.
