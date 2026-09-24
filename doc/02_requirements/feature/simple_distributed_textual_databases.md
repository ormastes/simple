# Requirements: Simple distributed textual databases

**Date:** 2026-09-13  
**Selection:** Authority A + Adapters A + Operating B + Retention A  
**Status:** Selected requirements

## Goal

Provide a local-first SCV semantic database whose immutable textual state and change batches replicate through Git, whose local history is managed through jj under the SJ writer boundary, whose compact integer aliases are settled by one fenced Git authority, and whose provider-neutral adapters connect GitHub-first Git/CI/bug services without introducing an always-on database server.

## Identity and settlement

- **REQ-001 — Offline identity:** A replica shall create entities offline using a durable database namespace, entity kind, random actor incarnation of at least 128 bits, and monotonic actor-local counter. Clone or counter rollback shall rotate the actor incarnation.
- **REQ-002 — Compact alias:** A settled entity shall have a permanent `(database_namespace, authority_epoch, entity_kind, u64)` alias. A file/table may elide contextual fields only through a versioned header; a bare integer copied without context shall be rejected.
- **REQ-003 — Canonical identity preservation:** Existing SCV `ChangeIdentity` and `RevisionIdentity` values shall remain canonical. Compact aliases shall not renumber, replace, or invalidate them.
- **REQ-004 — Identity map:** `IdentityMap` shall atomically store forward/reverse aliases, per-kind allocator high-water marks, accepted batches, merge/split links, and tombstones. Accepted numbers shall never be reused or recalculated from row count or maximum live ID.
- **REQ-005 — Fixed authority:** Exactly one configured Git settlement remote and protected `settled` ref shall allocate within a `(database_namespace, authority_epoch)`. Mirrors shall be read-only. Failure to prove old-authority fencing during disaster recovery shall require a new namespace.
- **REQ-006 — Settlement admission:** SCV shall authorize and validate patch signature, ACL, namespace/epoch, schema/reducer versions, base/dependencies, constraints, and reference closure before allocation or publication.
- **REQ-007 — Atomic candidate:** One candidate commit whose sole Git parent is fetched head `H` shall contain allocator state, alias mappings, rewritten typed references, tombstones, and accepted-batch registry updates in one tree.
- **REQ-008 — Publication and uncertainty:** `GitSettlementTransport` shall publish by protected non-force expected-old-OID update or an admitted single-integrator equivalent, then fetch/read back the accepted batch and OID. A stale head shall replan allocations; an uncertain outcome shall never allocate again until canonical history is checked.
- **REQ-009 — Rollback detection:** A signed, hash-chained settlement receipt shall bind namespace, epoch, prior receipt, accepted head/tree, allocator high-water marks, schema/reducer versions, and batch digest. Ancestry, epoch, or high-water regression shall block allocation.

## Semantic change protocol

- **REQ-010 — Typed patches:** `DbPatch` shall contain a stable batch ID, namespace/epoch, actor/incarnation, base semantic revision, causal dependencies, ordered typed operations, preconditions, canonical payload digest, signature/key identity, provenance, and schema/reducer versions.
- **REQ-011 — Canonical encoding:** Hash/signature bytes shall use tagged, length-framed, domain-separated canonical encoding with stable map ordering and declared UTF-8/normalization rules. Reuse of a batch ID with different canonical bytes shall be quarantined as corruption.
- **REQ-012 — Pure reducer:** The deterministic reducer and `MergePolicy` shall contain no Git, jj, CI, issue-provider, network, or credential I/O. Authorization shall precede merge planning.
- **REQ-013 — Merge semantics:** Schema metadata shall define keys, references, scalar/list/set policy, uniqueness, ownership, and tombstones. Different-field edits may merge; incompatible concurrent scalar edits and delete/update races shall remain explicit conflicts unless a selected field-authority rule decides them.
- **REQ-014 — Causality:** Settlement order shall not manufacture causal order. The reducer shall preserve original dependencies/base values and use causal topological order plus canonical batch-ID tie-break only where deterministic ordering is required.
- **REQ-015 — Replay and compatibility:** Accepted batch replay shall be idempotent. Clients shall negotiate schema/reducer compatibility, reject unsupported versions/downgrades, and prove full-versus-incremental materialization equality during reducer migration.

## Configuration-aware test evidence

- **REQ-016 — Immutable evidence entities:** The model shall include immutable `TestDefinitionRevision`, `ConfigRevision`, `ConfigSetRevision`, `ReproductionRevision`, `RunManifest`, `Observation`, `ExpectationRevision`, `ExpectationRule`, `OutcomeEvaluation`, and `BugOccurrence` entities.
- **REQ-017 — Observation identity:** Each observation shall bind a capability-declared provider identity tuple, source/test-definition/config/case revisions, run and attempt, and payload digest. Same identity and digest shall be idempotent; same identity with different bytes shall be quarantined.
- **REQ-018 — Outcome separation:** Actual observations shall be immutable and separate from reviewed expectation policy and revision-pinned evaluation. Classification shall distinguish PASS, XFAIL, XPASS, signature mismatch, infrastructure error, NOT_RUN, INCOMPLETE, and UNCLASSIFIED.
- **REQ-019 — Configuration and reproduction:** Every custom-configuration failure shall reference an exact effective configuration and exact reproduction revision with hashed dependency availability. Moving names, private paths, or a mutable jj change ID alone shall not establish reproducibility.
- **REQ-020 — Coverage finality:** A terminal run manifest shall bind planned coverage, chunks and digests, completion state, retries/supersession, missing shards, artifacts, and policy revision. Missing observations shall never imply PASS.
- **REQ-021 — CI authority:** CI producers may append observations and evidence only. They shall not approve expectations, close bugs, promote configurations, or qualify untrusted fork evidence for release.

## Git, CI, and bug-server adapters

- **REQ-022 — Git capability contract:** `GitSettlementTransport` shall expose exact-head fetch, candidate publication, accepted-batch verification, object-format and protection capabilities, limits, and classified failures. Missing force/delete protection, admitted CAS/single-integrator behavior, or read-back shall make allocator mode unsupported.
- **REQ-023 — GitHub-first delivery:** The first live adapter shall support GitHub Git settlement and GitHub Actions ingestion. Contract fixtures shall cover at least one non-GitHub Git authority and event, pull/poll, and bundle-only CI sources, including GitLab-CI and Jenkins-class semantics.
- **REQ-024 — Provider-neutral CI:** `CiObservationSource` shall declare available identity dimensions, uniqueness tuple, event/poll/bundle/artifact/attestation/pagination/retention capabilities, and normalize them into immutable run/job-attempt/artifact envelopes.
- **REQ-025 — Durable discovery:** Webhooks shall be latency hints. An immutable discoverable manifest shall be durable before producer acknowledgement; polling shall use persisted cursors and overlapping windows; cursors shall advance only after normalized input is durable and canonical acceptance is recorded.
- **REQ-026 — Bounded ingestion:** Untrusted bundles shall enter content-addressed quarantine outside the checkout and be subject to byte/file/record/depth/path/Unicode/decompression/time quotas, link/device rejection, streaming validation, and canonical digest checks. Reproduction content shall never execute during import.
- **REQ-027 — Bridge delivery:** Canonical bridge intent shall be committed with the semantic edit. Replica-local lease/retry/backoff state shall be separate. Delivery states shall include pending, leased, sent-unconfirmed, acknowledged, conflicted, and quarantined, with read-back reconciliation after uncertain provider effects.
- **REQ-028 — Provider conflict semantics:** `ProviderBinding` shall namespace external IDs by provider instance/project, retain last-common state and capabilities, distinguish permission loss from deletion, prevent causation loops, and apply reviewed per-field authority for multi-provider synchronization.
- **REQ-029 — Writer ownership:** All local mutation shall pass through the existing SJ lease/capsule. Provider/network waits shall not hold the DB lease, and Git/jj/adapters shall not independently mutate the same checkout.

## Retention, security, and operations

- **REQ-030 — Semantic and evidence placement:** Canonical Git shall retain aliases, allocator/settlement receipts, bugs, configurations, expectations, durable semantic history, summaries, and evidence manifests. Raw high-volume evidence shall use a controlled external content-addressed store.
- **REQ-031 — Retention classes:** Routine raw telemetry shall be exact for 28 days then represented by versioned daily cohort rollups. Unresolved failures, releases, pending work, and reproductions shall pin complete dependency closure until policy permits release.
- **REQ-032 — Honest resolution:** Historical queries shall report `exact`, `aggregated`, `restricted`, or `unavailable`; they shall never return an aggregate as an exact revision or a manifest as proof that bytes still exist.
- **REQ-033 — Rollup correctness:** Counts shall deduplicate stable observation identities. Timing shall retain mergeable sufficient statistics/sketches; daily percentiles shall not be averaged. Late input shall create revised rollup provenance.
- **REQ-034 — Resnapshot:** Epoch rollover/resnapshot shall include aliases, allocator high-water marks, tombstone/merge knowledge, schema/reducer identity, accepted batches, and history catalog. Stale operations shall return typed `ResnapshotRequired`; they shall not heuristically resurrect entities.
- **REQ-035 — Confidentiality and deletion:** Admissible metadata shall default-deny secrets and unnecessary PII before Git ingestion. Restricted evidence shall support encryption/key erasure where required, while incident/legal-deletion reports shall state that bytes already copied into immutable Git history or clones cannot be guaranteed erased.
- **REQ-036 — One app path:** CLI and app-layer orchestration shall use one cross-platform codebase; OS/provider differences shall live behind existing HAL/provider interfaces, with no per-OS sibling implementation or raw-runtime fallback.

## Selection traceability

- Authority A selected: REQ-005, REQ-008, REQ-009.
- Adapters A selected: REQ-022 through REQ-025.
- Operating B selected: NFR-001 through NFR-006.
- Retention A selected: REQ-030 through REQ-035 and NFR-007 through NFR-010.

