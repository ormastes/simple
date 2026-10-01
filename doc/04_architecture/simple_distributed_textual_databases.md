<!-- codex-design -->

# Architecture: Simple distributed textual databases

**Date:** 2026-09-13  
**Status:** Proposed architecture for selected requirements A/A/B/A  
**Decision:** Fixed settlement authority, GitHub-first live adapters, one-million-row operating tier, canonical semantic Git plus external evidence CAS

## 1. Context and decision

SCV needs a local-first textual database that can be edited offline, exchanged through Git, managed locally with jj, populated by CI, and projected to bug and Git servers. It must do this without adding an always-on database service and without allowing Git, jj, CI, provider adapters, and filesystem watchers to become independent writers.

The selected architecture is a **semantic replicated log with centrally settled compact aliases**:

- immutable `DbPatch` batches are the replication unit;
- a pure, deterministic reducer materializes canonical textual state;
- one protected `settled` Git ref is the allocation and admission authority;
- jj manages local revision work, but all mutation crosses the existing SJ lease/capsule;
- GitHub Git and GitHub Actions are the first live adapters;
- Git, CI, and issue-server integration is expressed through provider-neutral capability traits;
- canonical Git retains durable semantic history and manifests, while high-volume raw evidence lives in a controlled content-addressed store (CAS).

Git establishes shared bytes. jj supplies local revision workflow. SCV owns semantic identity, authorization, validation, conflict semantics, settlement receipts, and projections. A remote branch update is necessary for settlement but is not sufficient without SCV read-back and receipt validation.

This is an application/library architecture, not a compiler transform. MDSOC is applied as a virtual capsule with explicit ports and tree-private adapters; compile-time feature weaving is not justified.

## 2. Current-state constraints

The design extends, rather than assumes completion of, these real surfaces:

| Existing path | Current role and constraint |
|---|---|
| `src/lib/scv/sj_capsule.spl` | Owns the exclusive repository lease and the staged SCV transaction. Its comments explicitly state that the default jj lane is unavailable and that an independent `scvd` writer is forbidden. |
| `src/lib/scv/jj_adapter.spl` | Provides pinned jj argv execution and machine-template reads. It is the lower-level jj seam; settlement orchestration must not duplicate subprocess logic. |
| `src/app/sj/client.spl` and `src/app/sj/**` | Provide the app-facing SJ command/lease path and protected-ref policies. New mutation commands enter here or through an equivalent established request handler. |
| `src/lib/scv/backend_git.spl` | Is read-only by construction except for SCV-side mapping/projection records. It is not a settlement transport and must remain honest about that distinction. |
| `src/lib/scv/metadata_db.spl` | Wraps textual `SdnDatabase` plus WAL. `insert` copies the database and `next_key` derives from row count; neither behavior is suitable for the selected scale or distributed allocation. |
| `src/lib/scv/lifecycle/sync.spl` | Supplies `lifecycle_sync_field`, `SyncFieldPlan`, `LifecycleOutboxEvent`, idempotency/correlation fields, and conflict persistence. It is a planner/envelope foundation, not yet a durable bidirectional bridge. |
| `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl` | Wraps `TestDatabaseExtended` and already accepts `cohort_id` and resource evidence, but result updates do not bind immutable configuration and reproduction revisions. |
| `doc/03_plan/app/tools/scv_complete_impl_plan.md` | Establishes Git byte authority, jj local history, SCV identity, and the SJ single-writer lane. |

Consequently, implementation must add batch mutation before scale testing, complete an admitted live jj/SJ path before claiming settlement, and extend the runner compatibility boundary rather than create a second test database.

## 3. Capsule and layer model

### 3.1 Virtual capsule

`DistributedTextDbCapsule` is the conceptual MDSOC capsule. It groups a stable semantic core with replaceable outer adapters:

```text
                         DistributedTextDbCapsule
┌─────────────────────────────────────────────────────────────────────┐
│ App orchestration: status/fetch/publish/settle/sync/reconcile       │
├─────────────────────────────────────────────────────────────────────┤
│ SJ transaction boundary: lease, plan, durable intent, local commit │
├─────────────────────────────────────────────────────────────────────┤
│ Settlement │ CI ingestion │ Provider bridge │ Retention/hydration  │
├─────────────────────────────────────────────────────────────────────┤
│ Authorization → validation → pure reducer → canonical projection   │
├─────────────────────────────────────────────────────────────────────┤
│ Shared contracts: IDs, patches, schema, receipts, evidence, errors │
├─────────────────────────────────────────────────────────────────────┤
│ Ports: Git │ jj │ CI source │ issue provider │ CAS │ clock/crypto   │
└─────────────────────────────────────────────────────────────────────┘
```

The capsule is instantiated by app-layer composition. Provider choice is runtime configuration through traits; semantic behavior is selected by versioned schema/reducer metadata, not provider conditionals.

### 3.2 Layers and dependency direction

| Layer | Proposed logical modules | May depend on |
|---|---|---|
| L0 contracts | `identity_map`, `db_patch`, `semantic_schema`, `settlement_receipt`, evidence/provider envelopes, typed errors | Canonical encoding and value types only |
| L1 semantic core | `db_reducer`, `db_merge_policy`, `observation`, `expectation`, `rollup` | L0 |
| L2 durable local state | batched metadata store, patch journal, receipt store, indexes, quarantine catalog, bridge state | L0–L1 and existing storage facades |
| L3 orchestration | `settlement`, `ci_ingestion`, `bridge_delivery`, `retention`, `resnapshot` | L0–L2 and port traits |
| L4 provider adapters | GitHub Git, GitHub Actions, generic Git fixtures, GitLab/Jenkins-class CI fixtures, GitHub Issues, external CAS | Port traits and existing approved process/network/HAL facades |
| L5 app/SJ | SCV CLI commands, SJ request operations, status/diagnostics | L0–L4 facades |

Dependencies point inward. L0–L1 cannot import Git, jj, GitHub, process, filesystem, network, credentials, clock, or random APIs. L4 cannot reach into another adapter's private tree. L5 cannot bypass L3 to mutate storage.

### 3.3 Tree-level encapsulation and shared nodes

All implementation remains in the repository's current categorization, with final directories confirmed during detail design. Shared protocol nodes live under `src/lib/scv/**`; app command parsing stays under `src/app/sj/**` or the existing SCV app entry point. Test-runner production remains under `src/lib/nogc_sync_mut/test_runner/**` and calls the evidence ingestion facade.

| Raw layer/capsule | Common node exposed upward | Public to parent | Public to next-layer sibling |
|---|---|---|---|
| Identity/storage | `EntityRef`, `IdentityMapView`, `AllocatorState`, `Tombstone` | immutable lookup and transactional mutation plan | reducer receives only immutable views |
| Semantic protocol | `DbPatch`, `DbOperation`, `SemanticSchema`, `ReduceResult` | validate/reduce/replay | settlement and ingestion share the same reducer facade |
| Settlement | `SettlementPlan`, `SettlementReceipt`, `SettlementError` | plan/publish/verify/recover | adapters see `GitSettlementTransport`, never allocator internals |
| Evidence | `RunManifest`, `Observation`, `ExpectationRevision`, `OutcomeEvaluation` | append/query/classify | CI adapter emits normalized envelopes only |
| Bridge | `ProviderBinding`, `BridgeIntent`, `DeliveryReceipt`, `SyncConflict` | reconcile/import/export | provider adapters implement the bridge port only |
| Retention | `EvidenceManifest`, `Availability`, `RetentionPin`, `RollupRevision` | hydrate/compact/query-resolution | CAS adapter handles bytes, not semantic policy |

Everything else is tree-private. “Public to next layer” means these explicit facades, never general sibling visibility.

## 4. Shared capability interfaces

These names are the frozen design vocabulary for implementation and fixtures.

### 4.1 Semantic contracts

```text
IdentityMap
  resolve(EntityRef) -> Result<ResolvedIdentity, IdentityError>
  plan_bindings(AllocationPlan) -> Result<IdentityDelta, IdentityError>
  apply_atomic(IdentityDelta, AcceptedBatch) -> Result<IdentityMapView, StoreError>

PatchAuthorizer
  authorize(DbPatch, ActorClaims, SemanticSchema) -> Result<AuthorizedPatch, AdmissionError>

PatchValidator
  validate(AuthorizedPatch, IdentityMapView, SemanticSnapshot) -> Result<ValidatedPatch, AdmissionError>

SemanticReducer
  reduce(SemanticSnapshot, ValidatedPatch, MergePolicy) -> Result<ReduceResult, ReduceError>
  replay(SemanticSnapshot, [ValidatedPatch]) -> Result<ReduceResult, ReduceError>

MergePolicy
  plan_field(BaseValue, LocalValue, IncomingValue, FieldRule, Causality) -> FieldDecision

CanonicalCodec
  encode(DomainTag, CanonicalValue) -> Result<bytes, CodecError>
  digest/sign/verify with declared algorithm and version
```

Authorization is always completed before `SemanticReducer.reduce`. The reducer consumes already-authorized values and has no way to perform I/O. Canonical encoding is tagged, length-framed, domain-separated, uses stable map ordering, and declares UTF-8 normalization.

All references to immutable evidence or source state use a tagged `RevisionRef`, not an unqualified string. Its variants cover Git object/tree identity, canonical semantic revision, test-definition revision, configuration revision, configuration-set revision, reproduction revision, expectation revision, run manifest, and CAS object digest. Each variant carries its repository/database/provider namespace and format/version fields. A mutable jj change ID, moving branch/profile name, provider URL, or bare digest is provenance only and cannot satisfy a field typed as an exact revision.

### 4.2 Durable-state ports

```text
SemanticStore
  snapshot(MaterializationKey?) -> Result<SemanticSnapshot, StoreError>
  commit(AcceptedTransition) -> Result<MaterializationKey, StoreError>
  replay_log(HistoryRange) -> Result<[AcceptedPatch], StoreError>

ReceiptStore
  trusted_head(Namespace, Epoch) -> Result<TrustedSettlementHead, ReceiptError>
  bind_accepted(AcceptedCommitBinding) -> Result<(), ReceiptError>
  find_batch(BatchId, PayloadDigest) -> Result<AcceptedLocation?, ReceiptError>

SettlementRecoveryJournal
  persist_prepared(SettlementSubject, CandidateCommit) -> Result<JournalId, ReceiptError>
  mark_semantic_accepted(JournalId, AcceptedCommitBinding) -> Result<(), ReceiptError>
  mark_receipt_indexed(JournalId, ReceiptIndexEntry) -> Result<(), ReceiptError>
  pending() -> Result<[SettlementRecoveryRecord], ReceiptError>

IndexStore
  open(MaterializationKey, IndexFormat) -> Result<IndexView, IndexError>
  apply_delta(MaterializationKey, ReduceDelta) -> Result<IndexView, IndexError>
  rebuild(SemanticSnapshot, IndexFormat) -> Result<IndexGeneration, IndexError>
  activate(IndexGeneration) -> Result<(), IndexError>

QuarantineStore
  begin(UntrustedSource, Quota) -> Result<QuarantineWriter, QuarantineError>
  seal(ExpectedDigest) -> Result<QuarantinedObject, QuarantineError>
  promote(QuarantinedObject, ValidatedEnvelope) -> Result<DurableInput, QuarantineError>

DiscoveryStateStore
  cursor(SourceInstance) -> Result<DiscoveryCursor, StoreError>
  record_durable(NormalizedInput) -> Result<DurableInputId, StoreError>
  advance(Cursor, CanonicalAcceptance) -> Result<(), StoreError>

BridgeStateStore
  enqueue_atomic(SemanticEdit, BridgeIntent) -> Result<IntentId, StoreError>
  lease(IntentId, LeaseBounds) -> Result<DeliveryLease, DeliveryError>
  reconcile(DeliveryTransition) -> Result<DeliveryState, DeliveryError>

BridgeDelivery
  deliver(DeliveryLease, ProviderCapabilities) -> Result<ProviderEffect, DeliveryError>
  read_back(SentUnconfirmed, CorrelationMarker) -> Result<DeliveryTransition, DeliveryError>
  release(DeliveryLease, DeliveryTransition) -> Result<(), DeliveryError>

RetentionCatalog
  classify(EvidenceManifest, RetentionPolicyRevision) -> Result<RetentionClass, RetentionError>
  closure(RetentionPin) -> Result<DependencyClosure, RetentionError>
  resolution(RevisionRef) -> Result<HistoricalResolution, RetentionError>
  plan_compaction(Cutoff, PinSet) -> Result<CompactionPlan, RetentionError>
```

These are semantic transactions, not promises that the current `SdnDatabase` offers a matching primitive. The storage implementation must add batch mutation/WAL behavior that makes each method's atomicity true. Replica-local retry and cursor data are addressed separately from canonical semantic state, even when one physical implementation serves both behind distinct ports.

### 4.3 Infrastructure ports

```text
GitSettlementTransport
  capabilities() -> GitSettlementCapabilities
  fetch_settlement_head(SettledRef) -> Result<SettlementHead, GitTransportError>
  publish_candidate(ExpectedOldOid, CandidateCommit) -> Result<PublishOutcome, GitTransportError>
  verify_accepted(BatchId, SettlementSubject) -> Result<AcceptedCommitBinding, GitTransportError>
  prove_ancestry(AncestorOid, DescendantOid) -> Result<bool, GitTransportError>

SettlementReceiptTransport
  fetch_receipt_head(ReceiptIndexRef) -> Result<ReceiptIndexHead, GitTransportError>
  publish_entry(ExpectedReceiptOid, ReceiptIndexEntryCommit) -> Result<PublishOutcome, GitTransportError>
  find_entry(SubjectDigest, AcceptedOid) -> Result<ReceiptIndexEntry?, GitTransportError>

JjWorkspacePort
  snapshot() -> Result<JjSnapshot, JjError>
  read_machine_ids(RevisionSelector) -> Result<JjRevisionIds, JjError>
  create_candidate(ParentOid, CanonicalTree, Description) -> Result<CandidateCommit, JjError>

CiObservationSource
  capabilities() -> CiSourceCapabilities
  discover(Cursor, OverlapWindow) -> Result<DiscoveryPage, CiSourceError>
  fetch_manifest(ExternalRunIdentity) -> Result<UntrustedManifest, CiSourceError>
  fetch_bundle(ArtifactLocator, Quota) -> Result<QuarantinedObject, CiSourceError>

IssueProvider
  capabilities() -> ProviderCapabilities
  read(RemoteIdentity) -> Result<RemoteProjection, ProviderError>
  create(BridgeIntent, IdempotencyContext) -> Result<ProviderEffect, ProviderError>
  update(RemoteIdentity, Preconditions, BridgeIntent) -> Result<ProviderEffect, ProviderError>
  discover(Cursor, OverlapWindow) -> Result<ProviderPage, ProviderError>

EvidenceStore
  put_verified(Stream, ExpectedDigest, RetentionClass) -> Result<EvidenceLocation, EvidenceError>
  stat(Digest) -> Result<EvidenceAvailability, EvidenceError>
  hydrate(Digest, ByteLimit) -> Result<VerifiedStream, EvidenceError>
  pin/unpin through reviewed retention policy
```

`SettlementHead` means the fetched protected semantic-ref OID and its parent/tree metadata. `ReceiptIndexHead` independently means the head of the protected `refs/heads/settlement-receipts` ref and its complete receipt entries. Both `refs/heads/settled` and `refs/heads/settlement-receipts` deny force/delete and restrict writers to the pinned settlement identity. Neither type implies that a semantic commit contains its own OID or a self-contained post-publication receipt.

Cross-cutting host capabilities are `Clock`, `RandomSource`, `Signer`, `SignatureVerifier`, `CredentialProvider`, and `MetricsSink`. They enter only orchestration or adapters. Production implementations use existing Simple time, crypto, environment/process, and I/O facades; deterministic tests supply fixed capabilities. `SjMutationPort` is the sole app-to-writer capability and exposes bounded `begin`, `commit`, `abort`, and recovery operations around the existing SJ lease/capsule—it does not expose the lease primitive to adapters. `BridgeDelivery` owns provider effects and uncertain-effect read-back; `BridgeStateStore` owns durable state transitions. `RetentionCatalog` owns policy and historical-resolution truth; `EvidenceStore` owns bytes. Neither boundary may silently perform the other's responsibility.

Capability objects declare object format, ref protection, expected-old-OID/CAS behavior, read-back, restricted-pusher identity, pagination, event/poll/bundle support, identity dimensions, artifact retention, attestation, quotas, and idempotency limitations. Unsupported allocator safety returns a typed error; it never silently degrades to force push or last-write-wins. Hosted Git requires no server hook: a trusted, version-pinned SCV settlement worker or GitHub App validates semantic admission before using its restricted credential, while GitHub enforces only ref protection, allowed pusher/update policy, and non-force fast-forward/CAS behavior. A self-hosted Git hook may repeat validation as defense in depth, but portability and correctness never depend on that hook.

## 5. Identity and settlement architecture

### 5.1 Identity model

An offline identity is `(database_namespace, entity_kind, actor_incarnation_128+, actor_counter)`. Settlement adds the permanent alias `(database_namespace, authority_epoch, entity_kind, u64)`. Existing SCV `ChangeIdentity` and `RevisionIdentity` remain canonical and may acquire aliases; they are never rewritten as if the integer were their identity.

`IdentityMap` stores, in one atomic logical update:

- forward and reverse aliases;
- allocator high-water mark per kind;
- accepted batch IDs and canonical digests;
- merge/split links and tombstones;
- authority namespace/epoch and trusted settlement subject/checkpoint head.

Contextual fields may be elided from textual rows only under a versioned file/table header. API boundaries reject a bare integer without namespace, epoch, and kind context. Numbers are never derived from `rows.len()` or the maximum live ID, never reused, and never reset during compaction.

### 5.2 Admission and publication sequence

```text
fetch settlement head H + receipt-index head Q + trusted prior checkpoint R
  → validate ancestry/high-water/epoch
  → authenticate actor and authorize operations
  → validate schema, reducer, digest, dependencies, constraints, references
  → topologically order causal batches; use batch ID only as deterministic tie-break
  → plan aliases from persisted high-water marks
  → pure reduce and rewrite typed references
  → create canonical candidate tree T and commit P with sole parent H
  → sign non-cyclic SettlementSubject S over T, H, namespace/epoch, HWM,
    batch digest/ID, and schema/reducer versions
  → trusted pinned SCV worker validates S and crash-safely journals (S, P) locally
  → worker uses its restricted credential for expected-old-OID publication of P
  → fetch/read back accepted batch and commit OID
  → journal AcceptedCommitBinding(S.digest, accepted OID)
  → append one complete ReceiptIndexEntry(S, binding) to receipt ref Q by CAS
  → expose aliases as settled
```

Allocation and candidate construction occur within one bounded SJ mutation transaction, but network publication must not hold the local DB lease indefinitely. The coordinator therefore persists a complete candidate intent, releases local storage locks, performs bounded network I/O, then reacquires SJ to reconcile the observed result. Only the protected Git update is the shared settlement point. Local state remains `publish_uncertain` until read-back proves acceptance or rejection.

The candidate's sole parent is fetched `H`. Two integrators may compute the same next integer, but only one expected-old-OID update can be admitted. The loser discards its allocation plan, fetches the new settlement head and trusted prior checkpoint, and recomputes. No textual merge of independently allocated sequences is permitted.

### 5.3 Non-cyclic receipt protocol and rollback defense

Receipt construction is split into two records so no Git object authenticates its own unknown OID:

1. Build the complete canonical candidate tree `T`, including allocator state, alias/reference rewrites, accepted-batch entry, and the **previous** accepted checkpoint reference. `T` contains neither its own tree digest nor the new receipt/signature.
2. Compute `tree_digest(T)`. Create and sign `SettlementSubject S = {domain, namespace, authority_epoch, expected_parent_oid=H, candidate_tree_digest, allocator_high_water_marks, batch_id, batch_digest, schema_version, reducer_version, previous_subject_digest}`. `S` is immutable admission material outside `T`.
3. A trusted, version-pinned SCV settlement worker (deployed with a restricted GitHub App or equivalent credential) verifies patch authorization, reducer/schema versions, reference closure, high-water marks, `S`, and the actual parent/tree. It constructs `P` with sole parent `H` and tree `T`; before attempting the semantic ref, it crash-safely persists `(S, P, expected H)` in its local `SettlementRecoveryJournal`. The journal is trusted worker state, not a Git receipt-index entry and not part of `T`.
4. The same worker publishes the journaled `P` with its restricted credential by requesting a protected non-force expected-old-OID update of the semantic `settled` ref. GitHub does **not** interpret or verify `S`; it only enforces ref rules, fast-forward/CAS, and which identity may update the ref. Hosted operation therefore requires no custom hook. A self-hosted hook may independently validate `S` as an optional extra defense.
5. The worker fetches the protected semantic ref and verifies that its accepted commit has parent `H`, tree digest `S.candidate_tree_digest`, and the expected accepted batch. It creates `AcceptedCommitBinding = {subject_digest, accepted_commit_oid, observed_ref, observed_at, verifier/key}` and crash-safely records it beside `S` in the local recovery journal.
6. The worker creates one complete `ReceiptIndexEntry {subject: S, acknowledgement: AcceptedCommitBinding}` and appends it in one commit on the protected receipt-index ref using expected-old receipt-head `Q`. Receipt-index writers deduplicate by `(subject_digest, accepted_commit_oid)` and rebase/retry only this complete-entry append when another receipt writer advances the ref. The receipt-index commit can contain `P`'s OID because it is a different commit on a different ref; it never contains its own OID.
7. After fetch/read-back verifies that complete entry, the journal record becomes `receipt_indexed` and may be checkpointed/pruned under recovery policy. The next accepted semantic candidate carries the previous accepted subject digest and accepted commit OID/checkpoint in its tree, making prior acceptance visible in semantic history without asking the prior commit to contain its own OID.

In this terminology, a complete `SettlementReceipt` is the non-cyclic pair `(SettlementSubject, AcceptedCommitBinding)`. The signed object is the subject; the acknowledgement is verified observation metadata and is not claimed to have been signed before its OID existed. The prepared subject lives only in the trusted worker's crash-safe journal. Only the complete pair is replicated through the protected receipt-index ref and later checkpointed by the next accepted semantic tree.

There are exactly three durability domains:

1. **Trusted local recovery journal:** durably holds the validated subject/candidate before network mutation, then the acknowledgement and progress markers. It supports process-crash recovery but is not shared settlement authority.
2. **Protected semantic `settled` ref:** atomically selects `P` through one expected-old-OID update. Its tree atomically contains semantic state, allocator changes, aliases, and accepted-batch registry.
3. **Protected receipt-index ref:** receives one complete subject-plus-acknowledgement entry through one independent expected-old receipt-head update. It is portable verification evidence, not the settlement point.

The two remote ref updates are not a distributed transaction. Recovery closes every gap:

- local journal prepared, semantic head still `H`: resume the journaled candidate if `H` is unchanged; if it advanced, mark the local record `superseded` and replan without publishing any partial receipt entry;
- semantic publication result uncertain: fetch the semantic ref; if `P` or the matching batch/tree is accepted, record the acknowledgement, otherwise distinguish stale-head rejection from retryable transport uncertainty before taking another action;
- semantic `P` accepted, no complete receipt-index entry: rebuild the entry from journaled `S` plus read-back acknowledgement and publish it before exposing aliases or allocating again;
- receipt-index publication result uncertain: fetch the receipt-index ref and search `(subject_digest, accepted_commit_oid)` before retrying;
- receipt-index CAS loses a race: fetch its new head, deduplicate, and append the same complete entry on that head without republishing `P`;
- process crashes after receipt read-back but before journal cleanup: observe the complete entry, mark the journal record `receipt_indexed`, and clean up idempotently.

A local acknowledgement is evidence of verified observation, not a second settlement authority. The protected semantic ref remains the settlement point; the protected receipt-index ref makes the complete receipt durable and portable.

Chaining detects a rollback only relative to a trusted observation: a client with a trusted local binding/checkpoint rejects a fetched non-descendant, previous-subject mismatch, epoch regression, or allocator high-water regression. Signatures prevent fabrication or mutation of subjects, but cannot by themselves reveal replay of an older valid signed head to a fresh client. A fresh clone therefore requires a pinned/trusted bootstrap checkpoint or an independently witnessed current head; fixed remote protection and old-authority fencing remain operational assumptions. If those assumptions cannot be proved after restoration, allocation stops and recovery creates a new namespace.

Allocation fails closed on:

- non-descendant head, missing trusted prior checkpoint, or previous-subject mismatch;
- namespace/epoch mismatch;
- allocator regression;
- unknown/revoked signer or unsupported algorithm;
- missing accepted-batch/reference closure;
- inability to prove old-authority fencing after restoration.

For fixed authority A, a mirror never allocates. If disaster recovery cannot prove the old authority fenced, operators create a new database namespace rather than merely incrementing an epoch under ambiguous dual authority.

### 5.4 Settlement state machine

```text
draft → validated → journal_preparing → journaled → publishing
 publishing → accepted_unverified → receipt_publishing → settled
 publishing → stale_head → replanning
 publishing → publish_uncertain → reconciling → receipt_publishing | rejected | quarantined
 receipt_publishing → receipt_uncertain → reconciling → settled | quarantined
 any pre-settlement state → rejected | quarantined
```

`settled` requires canonical read-back plus subject and accepted-commit-binding verification. Retry from `publish_uncertain` first searches accepted history by batch ID and subject digest; it does not construct another allocation.

## 6. Pure reducer and merge semantics

`DbPatch` carries stable batch ID, namespace/epoch, actor incarnation, base semantic revision, causal dependencies, ordered typed operations, preconditions, schema/reducer versions, provenance, signature identity, and canonical payload digest. Reuse of an ID with different canonical bytes enters quarantine.

Operations include `Create`, `UpdateFields`, `AddSetMember`, `RemoveObservedSetMember`, `AppendObservation`, `Tombstone`, `ResolveConflict`, and `BindExternalIdentity`. Schema metadata—not textual parser guesses—defines keys, references, scalar/list/set behavior, uniqueness, ownership, and tombstones.

The reducer rules are:

- same identity and same bytes is idempotent replay;
- same identity and different bytes is corruption;
- different fields merge when preconditions remain valid;
- concurrent incompatible scalar changes produce a durable conflict;
- set behavior follows the declared observed-remove/add-wins/remove-wins rule with causal metadata;
- delete/update preserves a tombstone conflict and never silently resurrects;
- provider or remote arrival order does not manufacture causality;
- derived counts and summaries are recomputed from deduplicated accepted inputs.

Full replay and incremental materialization must yield identical canonical state/tree digests. Reducer migration runs both versions against the same admitted log before activation. The active schema/reducer pair is settlement-subject/checkpoint-bound.

## 7. CI and configuration-aware evidence

The runner records actual outcome separately from expectations and evaluations. `RunnerTestDb` remains the compatibility entry point while its update API is extended to accept an immutable evidence envelope containing `TestDefinitionRevision`, `ConfigRevision`, `ConfigSetRevision`, `ReproductionRevision`, `RunManifest`, `Observation`, and provider identity.

GitHub Actions is the first live source. GitLab-CI and Jenkins-class event, polling, and bundle semantics are covered by contract fixtures before their adapters are considered live. Generic `CiObservationSource` normalization ensures provider-specific run IDs never leak into semantic deduplication without a declared provider-instance namespace.

Producer flow has six distinct stages:

- **Freeze:** bind source, test-definition, effective configuration, configuration-set, and expectation revisions.
- **Bundle:** write bounded immutable chunks and a terminal manifest.
- **Discover:** make the manifest discoverable before acknowledging producer completion.
- **Quarantine:** fetch untrusted bytes into CAS quarantine, never into the checkout.
- **Validate:** stream-check quotas, paths, Unicode, links/devices, decompression, canonical digest, attestation, and authorization.
- **Accept:** commit normalized observations through SJ and advance the discovery cursor only after durable canonical acceptance.

Webhooks are latency hints. Persisted cursor polling uses overlap windows and stable identities. Duplicate webhook/poll/bundle delivery converges; identity reuse with different content quarantines. CI may append observations and evidence only. Expectation approval, bug closure, configuration promotion, and release qualification require separately authorized semantic operations.

An actual outcome is immutable. `OutcomeEvaluation` names the expectation revision and yields PASS, XFAIL, XPASS, signature mismatch, infrastructure error, NOT_RUN, INCOMPLETE, or UNCLASSIFIED. Absence is never PASS. Every custom-configuration failure binds exact configuration and reproduction revisions with dependency availability.

## 8. Bug and Git/CI server connectivity

### 8.1 Provider-neutral bridge

`ProviderBinding` stores local entity, provider instance/project/kind/remote ID, provider revision or ETag, last-common state, capability snapshot, field-authority policy, and sync state. A GitHub issue number is an external alias, never the SCV settled ID.

Canonical semantic edit and `BridgeIntent` are committed together. Transient lease, attempts, backoff, and rate-limit state remain replica-local. `LifecycleOutboxEvent` in `src/lib/scv/lifecycle/sync.spl` is extended rather than replaced; its event, correlation, causation, idempotency, delivery, schema, and payload digest fields form the envelope.

Bridge delivery state machine:

```text
pending → leased → sent_unconfirmed → acknowledged
                 ↘ conflicted
                 ↘ quarantined
leased → pending                  (expired local lease)
sent_unconfirmed → reconciling → acknowledged | conflicted | quarantined
```

There is no claim of atomicity across Git and a provider HTTP API. Delivery is at least once with idempotent effect where supported. Where creation has no provider idempotency key, use a stable correlation marker, serialize outbound ownership, and read back after timeout. Never blindly repeat an ambiguous create.

Three-way comparison uses stored last-common values. One-sided edits propagate, equal edits converge, and incompatible shared scalar edits conflict unless reviewed field authority selects a side. Permission loss, filtered visibility, missing access, and confirmed deletion are distinct results. Causation/provider IDs plus comparison with last exported projection prevent loops; bot authorship alone never suppresses an event.

### 8.2 Server classes

- **GitHub Git:** live fixed settlement authority transport using protected non-force expected-old-OID publication, restricted GitHub App/worker identity, and read-back. The pinned SCV worker performs semantic validation; GitHub does not.
- **Generic Git server:** usable for allocation only if its capability implementation proves protected force/delete behavior, admitted CAS or single-integrator equivalence, ancestry, object format, and read-back. Otherwise it is exchange/mirror-only.
- **GitHub Actions:** first live CI source using immutable manifests, artifacts/bundles, webhook hints, and reconciliation polling.
- **GitLab/Jenkins-class CI:** fixture-backed normalizers for different identity, retry, event, polling, and artifact models; live support is later work.
- **GitHub Issues:** first live issue bridge through `IssueProvider`.
- **Other bug servers:** plug into the same binding/intent/receipt model; adapters cannot change reducer semantics.

## 9. Storage, indexes, and invalidation

### 9.1 Durable placement

The sibling `simple-data` Git/jj workspace contains schema, merge policy, identity map/checkpoints, bugs, configuration revisions, reproductions, expectations, accepted low-volume changes, daily summaries, evidence manifests, and sync receipts. Local WALs, parsed indexes, locks, delivery retries, cursors, and quarantine staging are not committed as arbitrary working files.

Raw high-volume evidence is content-addressed outside permanent canonical Git ancestry. Evidence manifests record digest, byte size, media/schema type, retention class, locations, availability (`exact`, `restricted`, `unavailable`), encryption/key reference where applicable, and dependency closure. Routine raw observations are exact for 28 days; unresolved failures and release evidence pin complete closure.

### 9.2 Indexes

The one-million-row tier requires rebuildable local indexes:

- settled alias forward/reverse lookup;
- provisional identity lookup;
- accepted batch/digest deduplication;
- observation provider-identity deduplication;
- current test status keyed by source/test/config/case revision;
- causal dependency and reference-closure indexes;
- provider binding and outbox state;
- evidence digest/availability/pin index;
- rollup cohort and provenance index.

Indexes store a `MaterializationKey` containing canonical settled tree digest, settlement-subject/checkpoint digest, schema version, reducer version, and index format version. Startup opens an index only if all fields match. Accepted settlement invalidates by changed entity/table keys from `ReduceResult`; it does not rescan the whole tree. Schema/reducer/index-version change or missing delta triggers an explicit maintenance rebuild into a new generation followed by atomic generation swap.

Provider cursor caches are invalidated by provider instance, capability revision, credential scope change, and overlap-window reconciliation. Evidence availability is TTL-refreshed but digest identity never changes. Negative alias and provider lookups have short bounded TTLs and are invalidated on accepted relevant patches.

`SdnDatabase` per-row copy and full-file rewrite are prohibited on the ingestion hot path. A batched mutation API applies a validated batch and commits one WAL/checkpoint transaction. Dense local handles may accelerate provisional and settled references without changing canonical identity.

## 10. Startup and hot paths

### 10.1 Startup

Normal command startup performs bounded reads only:

1. locate source and sibling data workspace configuration;
2. load the latest trusted local receipt/checkpoint header;
3. validate namespace, epoch, schema/reducer, and index generation;
4. memory-map/open local indexes or report `ReindexRequired`;
5. recover incomplete local SJ/WAL transactions and uncertain publication/delivery intents;
6. expose read-only status before any network operation.

Startup does not fetch Git, poll CI, hydrate CAS, scan all batches, or run a per-query subprocess. Those are explicit `fetch`, `sync`, `reconcile`, `hydrate`, or maintenance operations. A cold rebuild is observable maintenance, never hidden in a latency-sensitive query.

### 10.2 Hot request paths

| Request | Required path | Forbidden behavior |
|---|---|---|
| Alias resolve | index lookup → contextual validation → row/checkpoint confirmation as needed | full textual DB scan, Git/jj subprocess |
| Current test status | composite status index → pinned expectation evaluation → availability summary | resolving moving config names, provider API call |
| Observation dedup | provider identity index → canonical digest comparison | loading whole run history |
| Local patch validation | schema cache → identity/reference indexes → pure reducer | network wait while holding SJ/DB lease |
| Provider status | durable local binding/receipt view; explicit refresh is separate | implicit API poll on every display |

At Operating B, warm p95 targets are ≤100 ms for alias and current-status queries and ≤250 ms for dedup lookup. A validated 10,000-observation import is ≤5 s and ≤256 MiB RSS; compaction dry-run over one million rows is ≤10 s and ≤512 MiB RSS. Every measurement records fixture digest, environment, tool versions, warm/cold definition, sample method, command, timeout, and raw receipt. Metrics expose decode, authorization, reference validation, reduce, index update, WAL/checkpoint, Git construction, publication, read-back, provider rate limit, queue depth, quarantine count, cache hit/miss, and maximum RSS.

## 11. Security model

Trust boundaries are producer → quarantine, adapter → normalized operation, local actor → authorization, SJ → mutable checkout, and settlement worker → protected remote.

- Untrusted artifacts are streamed into a content-addressed quarantine outside the checkout with byte/file/record/depth/path/Unicode/decompression/time quotas and link/device rejection.
- Importers parse data only; they never execute reproduction commands, hooks, scripts, or uploaded binaries.
- Credentials use app/process facades, are scoped per repository/project, and are unavailable to untrusted test steps.
- Transport authentication does not grant semantic authorization. `PatchAuthorizer` enforces operation and field ACLs before merge planning.
- Signature and digest records carry algorithm/version, key identity, domain separation, rotation, revocation, namespace, epoch, repository, and provider domain.
- Admissible Git metadata defaults to denying secrets and unnecessary PII. Restricted raw evidence may be encrypted and later rendered inaccessible through controlled key erasure.
- Deletion reports state honestly that bytes copied into Git history or clones cannot be guaranteed erased.
- Git hooks, attributes, LFS, or submodules are not security mechanisms because jj compatibility is incomplete; the initial topology uses a sibling clone.
- Provider payload strings never become shell fragments. Process adapters pass structured argv through existing approved facades.

Unsupported protection, ambiguous publication/effect, malformed encoding, quota breach, unknown reducer/schema, receipt regression, and incomplete reference closure all fail closed with typed errors.

## 12. Failure handling and recovery

| Failure | Durable state | Recovery |
|---|---|---|
| Crash before candidate intent commit | old complete state | discard transient work |
| Crash after journal, before semantic publication | `journaled` | validate journaled subject/candidate against fetched head, then publish or replan |
| Semantic ref accepted but response lost | `publish_uncertain` | fetch and verify accepted batch/tree against journaled subject; acknowledge without reallocating |
| Semantic ref accepted, receipt entry absent | `accepted_unverified` | read back, journal acknowledgement, and append one complete receipt-index entry |
| Receipt-index update response lost | `receipt_uncertain` | fetch receipt ref and deduplicate subject/OID before retrying the complete entry |
| Stale expected head | `stale_head` | fetch receipt/head, discard allocation proposal, rerun admission/reducer |
| Receipt/high-water regression | blocked allocation | operator proves restoration lineage or creates a new namespace |
| Local WAL/index torn update | protected settled tree plus trusted subject/checkpoint remain authority | WAL recovery or rebuild index generation |
| CI terminal manifest missing chunks | immutable `INCOMPLETE` run | accept late chunk/revised terminal manifest under explicit supersession |
| Webhook lost | cursor unchanged | overlapping reconciliation poll imports stable identities |
| Provider create outcome ambiguous | `sent_unconfirmed` | read-back by correlation marker; no blind duplicate create |
| Permission loss | provider access error | preserve local entity/binding; never infer deletion |
| CAS object expired/missing | availability transition | report restricted/unavailable; do not claim exact evidence |
| Long-offline stale operation | `ResnapshotRequired` | resnapshot aliases/tombstones, rebase pending semantic operations |
| Queue pressure/outage | bounded spool and backpressure | reject new low-priority intake before dropping oldest pending semantic work |

Recovery target is under ten minutes once dependencies are reachable. All recovery transitions are idempotent and observable. No generic retry loop may exceed bounded policy; ambiguous effects enter reconciliation.

## 13. Retention and rollups

Canonical Git retains identities, allocator state, settlement subject/checkpoint chain, accepted semantic batches, bugs, configurations, expectations, summaries, evidence manifests, tombstones, and history catalog. It does not retain every raw test byte forever.

After the exact 28-day window, routine telemetry becomes versioned daily cohort rollups. Counts deduplicate stable observation identities. Timing stores mergeable sufficient statistics/sketches; it never averages daily percentiles. Late data creates a new rollup revision with explicit provenance. Queries always report `exact`, `aggregated`, `restricted`, or `unavailable`.

Compaction is a semantic maintenance plan, not an assertion that Git garbage collection deletes reachable history. It previews lost exact resolution, respects pending work and evidence pins, and keeps alias/tombstone knowledge for the supported replay horizon. Ten-year-equivalent packed canonical objects and full clone transfer each target ≤2 GiB, measured separately from CAS.

## 14. Migration and rollout

1. **Freeze and baseline:** record deployed jj/Git/GitHub tooling; inventory ID producers, DB writers, reader paths, and provider credentials; benchmark current metadata load/insert/save and runner queries.
2. **Introduce contracts:** add canonical identity/patch/schema/receipt/evidence types and pure reducer fixtures without changing current writers.
3. **Batch local storage:** replace per-row whole-database copying on the new path with atomic batch mutation, persisted high-water marks, indexes, and deterministic replay.
4. **Shadow projection:** export current SCV/test data into the new semantic model; compare counts, identities, references, statuses, and canonical digests. Preserve existing reader paths through compatibility views.
5. **Complete SJ/jj lane:** implement and verify the real admitted mutation path. Do not promote the `recorded` or `unavailable` seam in `sj_capsule.spl` as production settlement.
6. **Git settlement shadow:** build candidates and receipts against an isolated data remote without accepting shared numbers; fault-inject races, lost acknowledgements, crashes, and rollback.
7. **Enable fixed authority:** protect `refs/heads/settled` and `refs/heads/settlement-receipts`, restrict both to the pinned settlement identity, establish initial receipt/allocator state, and switch allocation only after differential and recovery gates pass.
8. **Extend runner evidence:** add immutable config/reproduction/run envelopes behind `RunnerTestDb`; dual-write and compare before changing canonical ownership.
9. **Enable GitHub Actions ingestion:** quarantine, normalize, and shadow-import; then grant observation-only publishing authority.
10. **Enable GitHub Issues bridge:** start export-only, then import/reconcile after conflict, loop, permission, and uncertain-create tests pass.
11. **Activate CAS retention:** verify dependency closure and hydration before any provider artifact expires; enable dry-run compaction before destructive retention.
12. **Ownership cutover:** perform a one-time SJ-controlled migration, disable legacy independent writers, retain rollback to the last consistent receipt/checkpoint, and drill resnapshot/recovery.

Migration does not move executable specs into `doc/06_spec`, does not require source commits for every data event, and does not introduce per-OS implementations.

## 15. Alternatives considered

| Alternative | Decision | Reason |
|---|---|---|
| Always-on SQL/database server | Reject | Violates backend constraint and weakens offline/local-first operation. |
| Globally allocated integer at offline creation | Reject | Requires connectivity or risks collisions. |
| Row count or maximum live ID allocation | Reject | Reuses IDs after deletion/restore and races across replicas. |
| Transferable authority epochs now | Defer | A/A/B/A selected a fixed authority; transfer adds fencing complexity not required initially. |
| Federated independent namespaces | Defer | Useful for sovereign forks, but weakens compact shared numbering and complicates imports. |
| Git text merge for allocator state | Reject | Two valid-looking sequences can collide; only admission against one head is safe. |
| Git merge driver / live submodule | Reject initially | jj does not provide complete hooks/attributes/submodule/LFS compatibility. |
| CI webhook as durable queue | Reject | Delivery and workflow concurrency do not provide durable exactly-once discovery. |
| All raw evidence in canonical Git | Reject | Violates selected Retention A and clone-growth target. |
| Raw evidence only in ephemeral CI artifacts | Reject | Expiry breaks pinned reproduction closure. |
| Provider database/issue tracker as canonical | Reject | Couples semantics and availability to one server; provider IDs remain bindings. |
| Last-write-wins by timestamp | Reject | Clock/order does not express causality and silently loses concurrent edits. |
| MDSOC compile-time feature transform | Reject | This concern requires runtime adapter composition, not compiler weaving. |

## 16. Architecture invariants and acceptance evidence

The design is acceptable only when tests demonstrate:

1. one SJ-owned local mutator and no network wait under the DB lease;
2. no collision or accepted-number reuse under racing replicas/integrators;
3. journal/read-back recovery after lost semantic or receipt-index publication acknowledgement, with no partial remote receipt entry;
4. receipt ancestry/high-water rollback rejection;
5. deterministic full/incremental reducer equality across supported hosts;
6. explicit conflicts for concurrent scalar and delete/update races;
7. immutable configuration/reproduction-bound outcomes with no missing-as-PASS;
8. deduplicated webhook/poll/bundle ingestion and bounded quarantine;
9. provider uncertain-effect reconciliation without duplicate creation;
10. exact/aggregated/restricted/unavailable query honesty and verified archive closure;
11. the Operating B latency, RSS, import, compaction, recovery, and repository-growth targets using reproducible receipts;
12. GitHub live adapters plus provider-neutral Git, GitLab-CI, and Jenkins-class contract fixtures.

No implementation may call the architecture complete merely because Git accepted a commit. Acceptance is the combined proof of SCV admission, expected-head publication, canonical read-back, valid receipt, deterministic materialization, and indexed query correctness.

## 17. Consequences

### Positive

- Offline creation and editing coexist with compact settled references.
- Git/jj remain the backend and local workflow; no new service is required.
- A pure reducer makes merge behavior replayable, testable, and provider-neutral.
- CI and bug servers connect through bounded capabilities without owning semantic truth.
- External CAS contains telemetry growth while canonical Git retains durable decisions and integrity manifests.

### Negative

- Compact numbering is unavailable until the fixed authority accepts a batch.
- Settlement and provider delivery need explicit uncertain states and reconciliation.
- Permanent aliases/tombstones impose nonzero retained metadata.
- One-million-row performance requires new batched storage and indexes before rollout.
- Exactly-once effects cannot be promised across arbitrary provider APIs.

### Neutral

- Gaps in accepted numeric sequences are normal.
- A Git commit order does not imply causal order among offline edits.
- Old exact telemetry may become aggregated or unavailable by declared retention policy.
- Provider and Git server adapters may be added later without changing semantic contracts, but allocator mode remains capability-gated.

## 18. References

- `doc/01_research/local/simple_distributed_textual_databases.md`
- `doc/01_research/domain/simple_distributed_textual_databases.md`
- `doc/02_requirements/feature/simple_distributed_textual_databases.md`
- `doc/02_requirements/nfr/simple_distributed_textual_databases.md`
- `doc/03_plan/app/tools/scv_complete_impl_plan.md`
- `src/lib/scv/sj_capsule.spl`
- `src/lib/scv/jj_adapter.spl`
- `src/lib/scv/backend_git.spl`
- `src/lib/scv/metadata_db.spl`
- `src/lib/scv/lifecycle/sync.spl`
- `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`
- `src/app/sj/client.spl`
