# Simple distributed textual databases: SCV + jj + GitHub

**Date:** 2026-09-13  
**Status:** Research-backed proposal; not an implemented or benchmarked change.  
**Scope:** Compact settled identifiers, offline editing, semantic synchronization, configuration-aware test evidence, CI ingestion, bug-tracker bridges, and retention.  
**Backend constraint:** Git establishes shared bytes; jj manages local revision workflows; SCV supplies semantic identity, validation, and synchronization. No new always-on database server.

## 1. Recommended decision

Implement a **Git-backed, local-first semantic database protocol**, not a new storage backend. Each developer, CI worker, and integration adapter can own a local replica. GitHub is the rendezvous point and canonical settlement authority, much as an upstream Git repository already is for source changes.

Use distributed identifiers when an entity is created. After a protected settlement branch accepts an allocation, render and store references using a compact integer. Retain the original identifier once in a durable alias dictionary, rather than repeating it in every row. This preserves offline references and existing SCV identity while giving the requested smaller textual representation and integer indexing.

Keep three independent concepts:

- **Observations:** immutable records of what a test actually did in an exact configuration.
- **Expectations:** versioned policy stating what should happen in a configuration or a known configuration set.
- **Classification:** the interpretation of an observation against a particular expectation revision.

The canonical data repository should contain bugs, configuration definitions, expectation policies, identity mappings, useful evidence, and compact summaries. High-frequency execution telemetry should have separate retention and optional hydration. A bug-server or CI-server adapter publishes semantic changes; it does not overwrite the textual DB with a server dump.

## 2. Research and existing implementation

### 2.1 Relevant precedents

| Precedent | Verified property | What to borrow | What not to assume |
|---|---|---|---|
| Datomic temporary IDs | Transaction data accepts temporary references; transaction results return a temporary-to-resolved-ID map. [R1, R2] | Explicit, atomic ID resolution and reference rewriting | Datomic itself is not the proposed backend, and its transaction-local tempids are not an offline replication protocol |
| git-bug | Stores distributed issue data as Git objects and supports third-party bridges. [R3] | Offline bug work, Git transport, provider-neutral local records | Its exact storage layout or merge policy need not fit SDN or jj |
| SQLite Session | Changesets carry primary keys and before-values; application detects duplicate-key, missing-row, changed-value, and constraint conflicts. [R4] | Typed changesets, preconditions, and explicit conflicts | Applying a changeset is not automatically a complete distributed database |
| jj | Git-backed collaboration is supported; compatibility is incomplete for Git attributes/hooks/submodules/LFS. [R5] | Local editing and revision management on the existing Git backend | A Git merge driver or submodule workflow is not automatically supported by jj |
| pytest | Conditional expected failures, failure-type restrictions, and unexpected-pass classification are supported. [R6] | Separate actual outcome from configuration-dependent expectation | Marking a failure expected does not make the test pass |
| Git | Non-forced branch updates require fast-forward history; reachable objects are retained by garbage collection. [R7, R8] | Optimistic settlement and durable replication | Writing a compact checkpoint does not delete reachable history |
| GitHub Actions/webhooks | Workflow concurrency is bounded; webhook failures are not automatically redelivered; artifacts expire according to retention settings. [R9–R11] | Existing CI as an intermittent worker, reconciliation, retained evidence packs | Triggers are not a durable message queue and artifacts are not permanent archives |

### 2.2 Repository observations

The following files were read at **`718e4dde2d6bc6238718300298345264c856790e`**. These are source inspections, not claims that their behavior was executed or verified here.

| Existing surface | Observation | Design consequence |
|---|---|---|
| `doc/03_plan/app/tools/scv_complete_impl_plan.md` | Explicitly separates Git byte authority, jj history, and SCV identity; mutations use the `sj` single-writer lane. [P1] | Extend the existing architecture; do not introduce another mutating daemon |
| `src/lib/scv/metadata_db.spl` | Uses textual `SdnDatabase` plus WAL. `next_key()` uses current row count. An insert-path comment identifies whole-database copying as a performance concern. [P2] | Do not use that local count for shared IDs; add batch mutation before scaling ingestion |
| `src/lib/scv/lifecycle/sync.spl` | Has `lifecycle_sync_field`, `SyncConflict`, and `LifecycleOutboxEvent` with correlation, causation, idempotency, and payload fields. [P3] | Reuse the planner and event envelope; add durable delivery/reconciliation around them |
| `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl` | `RunnerTestDb` accepts `cohort_id`, resource evidence, and run tracking through the extended DB. The inspected result-update signature has no explicit configuration/reproduction references. [P4] | Extend this compatibility boundary rather than create another unrelated test DB |
| `doc/README.md` | Documents canonical test tracking paths and warns against moving them casually. [P5] | Preserve reader paths during migration; change storage ownership through an explicit hydration/adapter step |

The sync source establishes planning and envelope primitives. It does **not by itself establish** that a crash-safe, live, bidirectional provider bridge is complete.

## 3. Authority model and deployment

### 3.1 Components

```text
Developer replica A ─┐
Developer replica B ─┼── Git fetch/push ── GitHub data repository
CI worker replica ──┤                          │
Adapter replica ────┘                    settled branch
       │                                       │
       └── provider API ── GitHub Issues / CI / future bug server
```

SCV orchestrates these components. jj remains the local revision interface. `gh` supplies GitHub authentication/API operations, issue access, and artifact retrieval where required. Git transport remains the repository replication mechanism.

An integrator is a **role**, not a new service. It may run as a maintainer command, a job in existing CI, or a GitHub Actions workflow. When none runs, local editing and exchange of provisional batches still work; numeric settlement waits.

Do not let a CI adapter, an IDE watcher, a Git subprocess, and jj independently mutate the same checkout. Route mutations through the existing `sj` lease/capsule or its established migration-safe execution path. An unavailable write lane should cause a clear operational failure, not an uncoordinated fallback writer.

### 3.2 Repository layout

Proposed initial arrangement:

```text
workspace/
    simple/                    # source repository; existing code workflow
    simple-data/               # separate Git-backed jj workspace
        schema/
        merge-policy/
        identity/
        bugs/
        configs/
        config-sets/
        reproductions/
        expectations/
        changes/               # low-volume durable semantic change batches
        summaries/daily/
        evidence-manifests/
        sync/
```

Local-only state includes pending drafts, delivery retry state, parsed indexes, locks, and local WAL files. Those are not replicated as arbitrary working files. Replicate immutable logical batches and committed checkpoints, not a live WAL or a mutable server database file.

Use ordinary branch/bookmark names such as `settled` and `inbox/<replica>` initially. Avoid a ref per test or per observation. Batch paths are unique, so two producers do not edit one shared append file.

A source-repository configuration points to the data repository identity and optionally a pinned data revision. Live data synchronization must not require a parent source commit for every test run. Releases may pin the exact data revision separately.

Prefer a sibling clone over a live submodule for the initial jj implementation. The inspected jj compatibility documentation lists submodules, `.gitattributes`, hooks, and Git LFS as unsupported or unavailable in the normal workflow. Pin and test the actual deployed jj version rather than assuming Git behavior transfers. [R5]

## 4. Distributed IDs followed by compact sequential IDs

### 4.1 Identity and representation

Use the following conceptual tagged reference:

```text
EntityRef = Provisional(uid)
          | Settled(database_namespace, entity_kind, sequence)
```

A provisional `uid` is a well-tested distributed identifier, or a persistent random replica incarnation plus a durable local counter. Do not invent a short host-name-based identifier. If the counter state can be cloned or rolled back, generate a new incarnation and detect conflicting counter reuse.

Example, abbreviated for readability:

```text
Before settlement:
    bug: ~A...:57
    observation.bug_ref: ~A...:57

Accepted allocation:
    ~A...:57 -> bug:1042

After settlement:
    bug.id: 1042
    observation.bug_ref: 1042
```

The containing table and file header provide the database namespace and entity kind. They do not need to be repeated on every textual foreign key. The permanent alias record remains available:

```text
entity_uid | entity_kind | settled_id | settlement_batch
A...:57    | bug         | 1042       | settlement-88
```

This is a compact representation of stable identity, not deletion of identity. Existing canonical SCV Change/Revision identities should not be renumbered; they can also receive compact aliases where useful.

### 4.2 Required guarantees

A settled ID is assigned only by the selected authoritative lineage. An ID uploaded to a personal branch is not settled. Never reuse an accepted number after deletion, never recalculate it from row count, and never renumber accepted entities during compaction. Gaps are acceptable.

Every independently writable authority has its own database namespace. A mirror may reproduce accepted mappings but may not allocate competing numbers in the same namespace. Forks either retain upstream as settlement authority or obtain a distinct namespace. Importing a fork then requires explicit cross-namespace aliases.

Retain provisional aliases for as long as old replicas or retained artifacts can reference them. Garbage-collecting them after an arbitrary month can turn an old update into an apparent new insert. Aliases may be compressed and indexed; they must remain resolvable under the declared support horizon.

Use a persisted allocator high-water mark, not `rows.len()` or `max(live_id)`. After a disaster restore, restore the authoritative allocation lineage before minting numbers. A stale restoration must not restart an already-used sequence; otherwise create a new authority namespace.

### 4.3 Settlement protocol without a DB server

1. Fetch canonical branch head **H** and read its allocation high-water marks, alias dictionary, schema version, and applied-batch registry.
2. Read pending immutable batches. Resolve references already known in H. Reject unauthorized operations and incompatible schema versions.
3. Apply semantic preconditions, uniqueness checks, and reference checks. Preserve genuine conflicts rather than guessing.
4. Assign proposed sequential IDs to genuinely new entities, and rewrite all typed references in the candidate state. Include alias mappings and accepted batch IDs in the same candidate transaction.
5. Create a candidate commit **P whose only parent is H**.
6. Publish P with a non-forced, fast-forward update through the controlled SCV/jj landing path.
7. If another writer advanced the branch, discard the proposed allocation plan, fetch the new head, and recompute. Do not text-merge two independently allocated sequences.
8. After a successful update, or after an uncertain network outcome, fetch again and verify that the allocation batch exists in accepted history. Only then expose the numeric IDs as settled.

The serialized remote branch update is the settlement point. Git provides the fast-forward race rejection; SCV provides allocator correctness and schema validation. [R7]

A lost acknowledgement must not allocate a second ID: look up the batch ID and original uid first. Persist the mapping, changed rows, and accepted-batch record atomically in one Git tree/commit.

Do not embed a commit's own final OID into a file in that commit. Store a settlement batch identifier inside the tree; the acknowledgement receipt can add the observed accepted commit OID after publication.

### 4.4 Performance implications

A 64-bit integer occupies eight bytes instead of sixteen bytes for a 128-bit identifier, before representation overhead. Textual savings depend on decimal length and framing. Parsing speedups require measurement; they are not established by this design.

The hot path should parse settled references directly as integers and load alias dictionaries separately. Even provisional references can be interned to dense local handles, so offline operation need not repeatedly compare long text IDs.

The greater likely performance opportunity in the inspected SCV metadata implementation is avoiding whole-database copying per insert and full-file rewrites per observation. Address ID width, batching, and mutation complexity together. [P2]

## 5. Semantic versioning and merge

### 5.1 Typed patches

A proposed logical batch contains:

```text
batch_id
schema_revision
database_namespace
actor_id + actor_incarnation
base_semantic_revision
causal_dependencies
operations[]
payload_digest
provenance / authorization metadata
```

Operations include `Create`, `UpdateFields`, `AddSetMember`, `RemoveObservedSetMember`, `AppendObservation`, `Tombstone`, `ResolveConflict`, and `BindExternalIdentity`.

Use canonical typed serialization with length framing for hashing. Do not hash an ambiguous concatenation of user-controlled strings separated by a character that may also appear inside those strings.

A batch ID is stable across retries. Reusing an ID with different content is corruption or an identity collision, not an update. Retain the local WAL for local crash recovery, but make the replicated operation protocol explicitly versioned and independently validated.

### 5.2 Schema policy, not parser guesses

Grammar identifies the structure. Schema metadata supplies table keys, set-versus-list semantics, references, and permitted merge rules. An arbitrary SDN list must not be treated as a set merely because concatenation seems convenient.

| Situation | Required handling |
|---|---|
| Different new entity UIDs | Preserve both, subject to domain uniqueness constraints |
| Same UID, same payload | Idempotent replay |
| Same UID, different create payload | Explicit conflict |
| Different fields of the same row | Merge when preconditions and constraints permit |
| Same scalar field edited concurrently | Preserve conflict by default |
| Comment or observation appended twice | Deduplicate by stable operation/provider identity |
| Set add/remove concurrency | Apply the declared observed-remove/add-wins/remove-wins policy with causal metadata |
| Delete versus offline update | Preserve a tombstone/conflict; do not silently resurrect |
| Derived counts or timing summaries | Recompute from deduplicated inputs |
| Two different UIDs with a matching natural key | Coalesce only under explicit equivalence policy; otherwise conflict |

SQLite Session's before-value checks are a useful model for detecting real update conflicts. [R4] The existing lifecycle field planner is a useful base for three-way policy, but write authorization must occur **before** planning. A field-authority parameter is not a substitute for role enforcement. [P3]

Maintain the actual last common field values or a retrievable base object, not just a digest. A digest alone cannot supply the base values required by three-way merge.

A remote settlement order does not turn two offline edits into causally ordered edits. Keep original dependencies/preconditions after settlement so the second editor's stale write is not silently treated as intentional replacement.

### 5.3 Manual textual editing

Allow editing of the textual projection, but convert the diff against its recorded projection revision into typed operations. Then validate keys, references, schema, and conflicts before publication. Do not treat arbitrary file changes as trusted database operations.

SCV must explicitly run its DB reconciliation before landing. A `.gitattributes` merge driver alone is insufficient for a jj-first workflow. Unresolved jj conflicts and unresolved DB constraints both block settlement. [R5]

## 6. Configuration-aware test data

### 6.1 Core entities

| Entity | Purpose |
|---|---|
| `TestDefinition` | Stable test identity plus immutable definition revision |
| `ConfigRevision` | Immutable, canonical effective configuration and its content digest |
| `ConfigSetRevision` | Frozen membership of a known supported/required configuration set |
| `ReproductionRevision` | Exact source/test/input/tool invocation and prerequisite references |
| `RunManifest` | Provider/source identity, code revision, attempted coverage, completion and artifact metadata |
| `Observation` | Actual outcome and measurements for one test/configuration/case/attempt |
| `ExpectationRule` | Versioned default and configuration-specific policy |
| `Evaluation` | Classification using a named expectation revision |
| `BugOccurrence` | Failure evidence linked to a bug, configuration, and reproduction |

An observation is conceptually keyed by:

```text
(test identity, test definition revision, source revision,
 configuration revision, case/input identity, run identity, attempt)
```

Do not overwrite a single `test.status` when different machines report different configurations. Do not call a test flaky merely because one configuration passes and another consistently fails.

### 6.2 Known configurations and user configurations

A known set is an immutable revision, such as `supported-hosts@17`, containing exact configuration references. Changing a named profile produces a new configuration revision. A run must not resolve a moving configuration name at query time.

A custom configuration records its effective values, not only `user-config` or a private filesystem path. It can reuse a known configuration as a base plus overrides, but the fully resolved result must have its own immutable digest.

Split configuration from incidental execution evidence. Relevant compiler/runtime/backend/flags/driver/firmware/architecture settings belong in the effective configuration. Timestamps, current load, private usernames, and random temporary paths normally do not define configuration identity. Resource measurements and volatile environment observations belong in the run evidence.

Maintain explicit redaction/normalization rules. Secrets are named dependencies, not values copied into the database. A custom result does not automatically enter the project's required matrix; promotion is a reviewed policy operation.

### 6.3 The two references requested

Every custom configuration failure must have:

```text
config_ref: exact ConfigRevision
reproduce_ref: exact ReproductionRevision
```

Prefer these references for all observations, with shared references inherited from a run manifest to avoid repetition. The database can store compact numeric aliases; the referenced revisions still carry integrity digests.

A reproduction record should include source repository identity, exact Git/SCV revision or immutable source-tree bundle, test identity and definition digest, argv as a typed array, input/fixture digests, seed, build/runtime tool references, effective configuration, relevant device/emulator state, and artifact locations with hashes.

For pre-commit work, record a base revision plus an immutable dirty-tree/patch bundle, or an SCV snapshot whose bytes have actually been shared. A jj change ID alone is not enough to reproduce a mutable change. Store evidence availability as `available`, `restricted`, `expired`, or `missing`; do not claim reproducibility when dependencies cannot be obtained.

### 6.4 PASS defaults and scoped failures

A proposed SDN-style policy could express:

```sdn
expectation:
    test_ref: 420
    config_set_ref: supported_hosts_v17
    default_expected: pass
    outside_set: unclassified

    exceptions:
        known_failure:
            config_ref: 12
            expected: fail
            failure_signature_ref: 39
            bug_ref: 1042
            reproduce_ref: 73

        user_configuration:
            config_ref: 912
            expected: fail
            failure_signature_ref: 41
            bug_ref: 1051
            reproduce_ref: 801
```

This is proposed schema syntax, not a claim that the current parser accepts the example unchanged. Actual failing runs are recorded separately. Observing a failure must not automatically install a failure expectation.

Use exact configuration overrides, explicit frozen-set defaults, and an explicit outside-set policy. If general predicates are later supported, require deterministic declared priority and reject overlapping equally authoritative contradictory rules. Do not guess which predicate is “more specific.”

| Actual outcome | Applicable expectation | Classification |
|---|---|---|
| Pass | Pass | PASS |
| Fail with the expected signature | Fail | XFAIL / known failure |
| Pass | Fail | XPASS / candidate stale expectation |
| Fail with a different signature | Fail | New unexpected failure |
| Timeout, crash, infrastructure error | Ordinary assertion failure expected | Unexpected failure or infrastructure error |
| No terminal observation | Any | NOT_RUN / INCOMPLETE / UNKNOWN |
| Fail on custom configuration outside required matrix | No policy | Unclassified custom failure; retained and visible |

Conditional expected failures and unexpected passes have an established precedent in pytest. [R6] Store actual outcomes unchanged. Expectation updates require review, reason, bug linkage, applicability, and optionally an expiry/review date.

Do not report an untested configuration as PASS merely because the default expectation is pass. Show coverage alongside results. A useful aggregate is `required matrix: 12 pass, 1 known failure, 1 not run; additional user configs: 1 failure`.

A manual “set pass” or “set fail” is an attributed assertion with evidence quality such as `reported`, not automatically a verified runner observation. A separate expectation-edit operation changes policy. The CLI and UI must make that distinction explicit.

Current-status queries select an exact source/test revision or a documented revision-selection policy before choosing results. A late-arriving result for old code must not overwrite the current result. Passing one configuration after a fix does not prove all failing configurations are fixed; unresolved or untested configurations remain visible.

## 7. CI synchronization

### 7.1 Preferred producer flow

At run start, freeze source revision, test-definition revision, configuration-set revision, and expectation-policy revision. During the run, collect actual observations locally. At completion, publish a single immutable run bundle or a bounded series of chunks plus a terminal manifest.

The producer should not mutate one shared textual row after every test. Build one batch, make its pending reference discoverable, and let the settlement role import it. Raw results retain their original configuration and source references even if the canonical policy changes while the run is executing.

Use a stable external observation identity such as:

```text
(provider_instance, source_repository, run_id, run_attempt,
 job_identity, test_case_identity, observation_revision)
```

Re-importing the same source item is a no-op. A payload mismatch under an already-seen immutable identity is an error. Retrying a genuinely rerun test has a new attempt identity and is retained separately.

### 7.2 Ingestion, not automatic expectation changes

CI has authority to publish observations and execution evidence. It does not automatically approve a new default, convert failures to expected failures, or close a bug on every passing run.

Use reviewed rules for candidate bug linking and regression detection. Keep automated suggestions distinct from accepted triage decisions. Compare timing cohorts only across policy-declared compatible configurations and source/test-definition contexts.

### 7.3 No dedicated listener required

Initially, use a local `sync` command, an existing CI post-run step, and GitHub-hosted jobs. GitHub-native issue/workflow events can trigger a job without hosting an HTTP endpoint. Periodic reconciliation scans discoverable batches/provider runs in case a trigger was missed.

Workflow concurrency prevents simultaneous workers in a configured group, but it is not a durable event queue. Current GitHub documentation includes `queue: max`, bounded to 100 pending jobs/runs, and cancellation on overflow; the default pending behavior is more restrictive. Persist pending work independently and drain it idempotently. [R9]

The settlement worker must still handle a competing authorized local integrator. Branch update validation, not workflow scheduling alone, protects allocation correctness.

Separate an untrusted test producer from a privileged data publisher. The latter parses bounded data using trusted, pinned code; it never executes code or reproduction commands supplied by the uploaded result. Scope credentials to the appropriate repository and operation. GitHub documents minimum token permissions and use of an App token when additional permissions are needed. [R12]

## 8. Local and remote bug-server interaction

### 8.1 Provider-neutral state

Use the local bug entity as the portable record. A provider binding stores:

```text
binding_id
local_entity_ref
provider_instance
remote_kind
remote_id
remote_revision_or_etag
last_common_state_ref
authority_policy_ref
sync_state
```

A GitHub issue number or a future server's numeric primary key is an external ID, not the local settled ID. Namespace bindings by provider instance and repository/project, so `issue 42` in two places cannot collide.

Treat the GitHub data repository as canonical shared state. A bug server can present a projection and submit edits through its adapter. This leaves local work useful when that server is unavailable.

### 8.2 Inbox/outbox protocol

An outbound edit is committed together with an outbox item. The adapter sends it to the provider, records the result, and writes an acknowledgement/binding update back through the same replicated protocol.

Inbound events are deduplicated, normalized, and applied against the last common state. Persist the imported operations before advancing the import cursor. Keep canonical shared receipts separately from disposable local retry state.

The existing `LifecycleOutboxEvent` envelope is the appropriate place for correlation ID, causation ID, idempotency key, provider delivery ID, and payload digest. Extend its durable state machine rather than defining a competing envelope. [P3]

Typical delivery states are `pending`, `leased`, `sent_unconfirmed`, `acknowledged`, `conflicted`, and `quarantined`. Delivery leases must not be confused with accepted identity allocation.

### 8.3 Conflict and replay behavior

If only the local field changed since the common base, push it. If only the remote field changed, import it. Equal changes converge. Incompatible edits to the same shared scalar produce a conflict, unless a reviewed ownership rule makes one side authoritative.

Comments normally append using stable comment/event identities. Label membership uses declared set semantics. A title, description, or workflow transition normally requires a three-way decision. A remote closed state and a concurrent local reopen should not be resolved by wall-clock last-write-wins.

Prevent loops with causation/provider IDs and comparison with the last exported projection. Do not suppress all events authored by a bot: that can hide legitimate changes from another integration.

There is no atomic transaction spanning Git and a general issue-server HTTP API. Aim for at-least-once delivery with idempotent effects. If a provider lacks a real idempotency key, use a stable correlation marker, serialized outbound ownership, read-back reconciliation, and an explicit uncertain state. Never promise exactly-once creation or blindly repeat a timed-out issue creation.

Missing access, a filtered API result, and actual deletion are different conditions. Do not interpret a permission failure as a remote deletion. Preserve unsupported provider fields/capabilities rather than silently dropping information.

### 8.4 Reconciliation

Webhooks are latency optimizations. GitHub does not automatically redeliver failed webhook deliveries, so periodic API reconciliation is necessary. [R10] Use pagination, overlapping update windows, stable IDs, persisted cursors, and an occasional broader repair scan. A timestamp alone is not an exactly-once cursor.

Future server adapters can consume APIs or supported changefeeds and emit the same `DbPatch` protocol. Do not bidirectionally copy SQLite/server database files or depend on an unversioned server schema.

## 9. Retention and repository size

### 9.1 Correction to the previous proposal

A new checkpoint in an ordinary Git branch does not reclaim the old snapshots or operations that remain reachable from branch history, tags, remote-tracking refs, reflogs, or jj references. Git garbage collection intentionally preserves reachable objects. [R8]

Likewise, a Merkle root can commit to a set of retained inputs and support inclusion verification with witnesses. It does not recover deleted operations or independently prove that a reducer computed the correct checkpoint. State reproducibility requires the inputs, a trusted checkpoint, or a separate proof mechanism.

### 9.2 Separate retention classes

| Class | Proposed policy |
|---|---|
| Bug decisions, configuration definitions, reviewed expectations | Retain semantic history; expected to be lower volume than raw runs |
| ID aliases and allocator high-water marks | Retain across normal compaction; never reset accepted identity |
| Ordinary raw test telemetry | Exact recent window, initially 28 days |
| Older routine test telemetry | Daily per-cohort summaries, with a declared aggregation revision |
| Unresolved failures and reproductions | Pin complete dependency closure until resolved plus a configured grace period |
| Release qualification evidence | Explicit retention pin |
| Local parsed indexes/current dashboards | Rebuildable; do not commit every refresh |
| Pending unsynchronized work | Never prune because its creation time is old |

Counts must be computed from deduplicated observation identities. Timing aggregation can retain mergeable sufficient statistics and a documented percentile sketch/histogram; averaging daily p95 values does not yield a correct global p95. Keep measurements separated by configuration/comparability cohort.

A full-suite run may use a compact default-pass encoding only when the manifest proves the planned coverage and completion, including explicit skipped, failed, missing, and incomplete cases. Missing data never implies pass.

### 9.3 Physical storage on the required backend

Recommended initial storage is a small, ordinary `simple-data` Git repository for durable semantic state, plus compressed raw evidence bundles outside that repository's permanent ancestry. Existing GitHub Actions artifacts are suitable for time-limited CI bundles and can be retrieved with `gh`; they have retention expiry and are not permanent storage. [R11]

Copy pinned bundles into an approved retained archive and record hashes, locations, and availability before expiry. A manifest alone does not keep an artifact alive.

For an all-Git raw-data requirement, use separate telemetry epoch repositories and fetch them on demand. Daily summaries stay in the canonical data repository. This isolates clone growth without forcing a rewrite of shared source or data history. Deleting old hosted refs does not guarantee immediate physical reclamation by GitHub.

If even the durable data repository eventually needs an epoch rollover, publish a new complete checkpoint with alias dictionary, allocator state, tombstone summary, and history catalog. Keep the prior epoch immutable and addressable separately. Old clients must resnapshot and rebase pending semantic operations. Never pretend an arbitrary old revision is exactly reconstructible from a daily aggregate.

Queries should report `exact`, `aggregated`, `restricted`, or `unavailable` resolution. An exact historical revision request must not silently return a day-end approximation.

Unlimited offline replay and arbitrary metadata deletion cannot both be guaranteed. Define a supported replay horizon; retain compact alias/tombstone knowledge and reject or explicitly rebase operations older than it. A long-offline client with an old delete/update dependency must not recreate a deleted entity.

## 10. Proposed command surface

These commands are proposed, not claims about existing executable functionality:

```text
scv db status
scv db fetch
scv db sync
scv db publish
scv db settle
scv db resolve
scv db history --resolution exact|daily
scv db compact --dry-run

scv test config capture
scv test expectation set
scv test result record
scv test reproduce

scv bridge import
scv bridge export
scv bridge reconcile
scv bridge status
```

`publish` shares a DB batch without publishing unrelated source work. `settle` requires appropriate authority and only accepts validated, conflict-free changes. `reproduce` resolves and validates dependencies before an explicitly trusted execution step. `compact` must show which exact queries/evidence would become unavailable before any deletion.

## 11. Implementation plan

| Phase | Work | Dependency and acceptance |
|---|---|---|
| 0. Freeze contracts and baseline | Inspect deployed jj/gh versions; inventory all replicated IDs and DB writers; measure load, insert, batch-save, pack size, and clone cost | No production migration; record real baselines and current failure behavior |
| 1. Identity and batch mutation | Tagged provisional/settled references, immutable aliases, allocator state, dense local handles, batched SDN writes | Concurrent offline creation has no identity collision; accepted IDs are never reused; no whole-DB copy per observation |
| 2. Semantic changes | Typed `DbPatch`, preconditions, deterministic schema/reducer versions, replay registry, set/tombstone rules | Duplicate delivery is a no-op; incompatible same-field edits remain conflicts; full and incremental reducers agree |
| 3. Git-backed settlement | Separate data workspace, inbox branches, candidate commit protocol, verified receipts, existing landing/write-lane integration | Two racing integrators cannot accept colliding IDs; crash/restart recovers without duplicate allocation |
| 4. Configuration and reproduction | Extend `RunnerTestDb`; introduce config/set/repro revisions, observation/expectation split, compatibility views | A test can pass on A, fail on B, and fail on user C with both references; NOT_RUN never becomes PASS |
| 5. CI producer/ingestor | Immutable run bundles, trusted settlement consumer, durable pending discovery, retries, provenance, scoped credentials | Reimport and reordered events preserve counts; missing chunks remain incomplete; CI cannot self-approve expected failures |
| 6. Provider bridges | Reuse lifecycle sync/outbox; add durable states, common-base objects, external bindings, GitHub Issues bridge first | Offline issue/comment work syncs; concurrent edits surface; timeout-after-create is reconciled rather than blindly retried |
| 7. Retention and archive | Exact recent window, daily rollups, evidence pins, artifact availability, epoch/resnapshot protocol | Checkpoint equals retained-state replay; pinned reproduction closure survives; old clients cannot resurrect tombstones |
| 8. Migration and rollout | Shadow export, differential checks, reader-path compatibility, one-time ownership migration, recovery drills | No silently missing entities or evidence; code/data publication remains independent; rollback restores a consistent state |

Parallel work lanes: identity/storage, semantic merge, test configuration/reproduction, Git transport, provider adapters, and fault-injection/performance tests. Shared schemas and serialization must be frozen before independently implementing producers and consumers. Transport/provider work may use fixtures early, but live completion must require real round-trip evidence.

### Suggested code integration

Reuse `src/lib/scv/lifecycle/sync.spl` and its model/store/codec neighbors for provider-neutral envelopes and bindings. Extend `src/lib/scv/metadata_db.spl` or a shared identity module for compact-reference mapping and batching. Extend the existing test-runner compatibility API for configuration and reproduction references. Put the new semantic DB protocol behind reusable library interfaces; keep `gh`/provider I/O out of the pure reducer.

The exact destination directories should follow the repository's current library categorization. Logical modules needed are `identity_map`, `db_patch`, `db_merge_policy`, `settlement`, `config_revision`, `reproduction`, `observation`, `expectation`, `bridge_delivery`, `retention`, and `evidence_catalog`. They are proposed modules, not existing paths asserted by this report.

Use bounded queues, explicit backpressure, batch operations, and async host I/O through existing Simple facilities. Do not hold a database/write lease while waiting indefinitely on a network API. Persist intent, release local locks as appropriate, and reconcile the response through a new controlled transaction.

## 12. Required correctness and failure tests

The acceptance suite should cover:

1. Two replicas insert from the same checkpoint; a third references both provisional IDs; settlement preserves all references.
2. Two integrators propose the same next sequence; only one candidate is accepted; the loser recomputes.
3. Network failure after successful push; retry finds the accepted allocation instead of creating another.
4. Crash before/after alias publication and local projection replacement; recovery yields either the old complete view or the new complete view.
5. Old replica updates a provisional alias after the entity has been settled, deleted, or merged; alias resolution and tombstones are honored.
6. A cloned actor counter reuses an operation identity with different content; ingestion rejects it.
7. Different-field edits merge; concurrent same-field edits conflict; replicated conflict resolution is idempotent.
8. A test passes on known A and fails on known B; custom C has a distinct config digest and both required references.
9. An expected assertion failure instead crashes or fails with another signature; it remains unexpected.
10. A known failure starts passing; XPASS is recorded without retroactively rewriting history.
11. A named config or test definition changes; older evidence remains bound to its immutable revision.
12. A partial CI upload lacks final coverage; no absent result becomes PASS.
13. The same result arrives through CI polling and a webhook; counts and timing samples are not doubled.
14. API create succeeds but the acknowledgement is lost; bridge recovery does not blindly duplicate the issue/comment.
15. Webhook delivery is lost and the worker is offline; reconciliation recovers accessible server changes.
16. User loses remote permission; the local bug is not treated as deleted.
17. An untrusted result/reproduction contains executable content; the privileged importer treats it only as data.
18. A 45-day-offline replica returns after 28-day raw retention; resnapshot/rebase preserves pending work without resurrection.
19. Daily rollup is recomputed with a late arrival; revision/provenance change explicitly, and exact historical availability is reported honestly.
20. Release-pinned evidence survives raw-artifact expiry through verified archive copies.

Property checks should include replay idempotence, deterministic checkpoint hashes for equivalent accepted operation sets, stable alias resolution, no accepted ID reuse, reference closure, and equality of incremental/full materialization. Benchmark identifier representations and batch strategies on representative actual data; report measured time, memory, Git pack growth, and network bytes rather than assumed speedups.

## 13. Final architecture choice

The best fit is **distributed local editing with centrally settled shared numbering**, not a centrally hosted database application. Number allocation is coordinated at the existing GitHub repository boundary; creation and editing remain offline-capable. The portable data model is shared by humans, CI, and server adapters, while provider IDs remain aliases and provider APIs remain replaceable interfaces.

Keep Git/jj as the backend now. Reuse SCV's existing identity/lifecycle/write-lane structure. Add a typed semantic protocol, configuration-bound immutable evidence, and durable synchronization. Optimize identifier representation and telemetry retention without sacrificing old-reference resolution or claiming that missing evidence proves a pass.

## Sources

All external sources were consulted on 2026-09-13. URLs are recorded for verification; the proposals above are engineering synthesis, not claims that any cited system implements this entire design.

- **R1 — Datomic transaction data, entity IDs and tempids:** `https://docs.datomic.com/transactions/transaction-data-reference.html`
- **R2 — Datomic Client API, transact result and tempid map:** `https://docs.datomic.com/client-api/datomic.client.api.html#var-transact`
- **R3 — git-bug official project:** `https://github.com/git-bug/git-bug`
- **R4 — SQLite Session introduction and conflict model:** `https://sqlite.org/sessionintro.html`
- **R5 — Jujutsu Git compatibility:** `https://docs.jj-vcs.dev/latest/git-compatibility/`
- **R6 — pytest conditional skip/xfail, failure restrictions, and XPASS:** `https://docs.pytest.org/en/stable/how-to/skipping.html`
- **R7 — Git push rules and fast-forwards:** `https://git-scm.com/docs/git-push`
- **R8 — Git garbage collection and reachability:** `https://git-scm.com/docs/git-gc`
- **R9 — GitHub Actions workflow concurrency:** `https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax`
- **R10 — GitHub failed webhook deliveries:** `https://docs.github.com/en/webhooks/using-webhooks/handling-failed-webhook-deliveries`
- **R11 — GitHub artifact retrieval and retention:** `https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts`
- **R12 — GitHub workflow token permissions:** `https://docs.github.com/en/actions/tutorials/authenticate-with-github_token`

Repository sources at `718e4dde2d6bc6238718300298345264c856790e`:

- **P1:** `https://github.com/ormastes/simple/blob/718e4dde2d6bc6238718300298345264c856790e/doc/03_plan/app/tools/scv_complete_impl_plan.md`
- **P2:** `https://github.com/ormastes/simple/blob/718e4dde2d6bc6238718300298345264c856790e/src/lib/scv/metadata_db.spl`
- **P3:** `https://github.com/ormastes/simple/blob/718e4dde2d6bc6238718300298345264c856790e/src/lib/scv/lifecycle/sync.spl`
- **P4:** `https://github.com/ormastes/simple/blob/718e4dde2d6bc6238718300298345264c856790e/src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`
- **P5:** `https://github.com/ormastes/simple/blob/718e4dde2d6bc6238718300298345264c856790e/doc/README.md`
