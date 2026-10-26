<!-- codex-research -->
# Local research: Simple distributed textual databases

**Date:** 2026-09-13  
**Status:** Source-inspected; not implementation or runtime evidence  
**Feature:** `simple_distributed_textual_databases`

## Scope and route

This extends, rather than replaces, `doc/01_research/app/tools/scv/simple_distributed_textual_databases_scv_jj_github_2026-09-13.md`. The primary knowledge route is developer tooling, with SCV, lifecycle, database, test-runner, transport-security, storage, and verification knowledge linked in `.spipe/simple_distributed_textual_databases/knowledge_selection.sdn`.

The requested target is provider-neutral: CI servers exchange immutable run bundles and semantic patches with the textual database; a configured Git server supplies the canonical settlement ref. GitHub is the first adapter, not the protocol definition.

## Verified current surfaces

| Surface | Verified current behavior | Consequence |
|---|---|---|
| `src/lib/scv/metadata_db.spl` | `ScvMetaDb` stores textual `SdnDatabase` snapshots with a WAL. `next_key()` derives a key from live row count, and insertion notes whole-DB copying. | Shared IDs require a durable allocator high-water mark; ingestion requires batching and indexed materialization. |
| `src/lib/scv/journal.spl` | Event batches have pending/committed markers and idempotent replay. | Reuse crash-recovery concepts, but do not confuse filesystem event batches with versioned semantic `DbPatch` records. |
| `src/lib/scv/lifecycle/model.spl` | `RemoteBinding` and `SyncConflict` already model provider identity, remote revision, authority policy, sync base, and conflict state. | Extend the lifecycle model instead of creating a second provider-binding stack. |
| `src/lib/scv/lifecycle/model.spl` identity types | `ChangeIdentity` and `RevisionIdentity` are the existing canonical SCV identity surfaces. | Do not renumber them; add compact aliases where useful and preserve canonical identity through migration. |
| `src/lib/scv/lifecycle/sync.spl` | `lifecycle_sync_field` performs three-way scalar planning. `LifecycleOutboxEvent` carries correlation, causation, idempotency, provider-delivery, and payload-digest fields. | Authorization must run before merge planning; canonical length-framed hashing and durable delivery states remain missing. |
| `src/lib/scv/lifecycle/store.spl` | Lifecycle records are written as individual `.scvl` files. | No crash-safe provider outbox worker or inbound cursor protocol is established by this store alone. |
| `src/lib/scv/sj_capsule.spl` | A mkdir-atomic exclusive lease protects a multi-step mutation transaction; readers consume immutable publication. | All DB/Git/jj mutation must remain in the SJ ownership lane, with no network wait while holding the local DB lease. |
| `src/lib/scv/jj_adapter.spl` and `src/app/sj_daemon/request_handler.spl` | jj 0.32 is invoked through argv/machine templates. The daemon executes under lease; a command-string split path loses quoting, and raw push policy is not yet the settlement protocol. | Use typed argv and capability probes; do not parse `.jj` internals or equate raw `jj git push` with admitted settlement. |
| `src/lib/scv/backend_git.spl` | Git integration is read-only tree/revision mapping and verification. | Fetch/CAS/publish/read-back settlement is new work. |
| `src/lib/scv/public_remote.spl` | Remote exchange is filesystem/manifests/fast-import oriented. | It is a useful immutable-batch seam, not a production Git-server adapter. |
| `src/lib/scv/network_remote.spl` | CAS and SSRF/auth shapes exist, while production HTTP/header/resume paths are declared future or test seams. | Do not claim live GitHub/GitLab network transport exists. |
| `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl` | `RunnerTestDb` tracks cohort/resource/timing/run data and mutates aggregate result state. | Add immutable config, reproduction, observation, expectation, evaluation, manifest, and artifact references behind this compatibility boundary. |
| `src/lib/scv/gc.spl` and `src/lib/scv/maintenance.spl` | SCV already has reachability/checkpoint/maintenance concepts for repository objects. | Extend closure and maintenance policy for semantic aliases, tombstones, accepted batches, and evidence catalogs; existing GC is not telemetry rollup/archive proof. |
| `src/app/tracking/main.spl` | Existing tracking tooling contains GitHub/task bridge-facing application logic. | Reuse provider projection/capability ownership where applicable; do not make application API passthrough the pure reducer or settlement authority. |
| `.github/workflows/pr-admission.yml` | Existing workflow logic ingests exact-head, digest-bound artifacts through trusted API calls. | Reuse this trust pattern for bounded CI run bundles; no SCV textual-DB ingestion workflow currently exists. |

## Remote migration review (2026-09-14)

The PR was rebased onto `origin/main` at `90d1874396b`. The intervening remote
history contained two SCV changes relevant to repository-backed state:

- `bcc6d5bc446` normalizes Windows verbatim paths before compile-snapshot
  ownership and containment checks.
- `90dc8c95778` fixes whitespace canonicalization in the event-maintained source
  inventory by using the supported free function.

Both changes are inherited by this PR. They do not alter the proposed textual
database entity, patch, settlement, or evidence schemas. Implementations must,
however, reuse platform-normalized path ownership checks and supported canonical
text primitives at filesystem/import boundaries rather than duplicating the
previous forms. No recent remote change introduced a competing database writer,
allocator, semantic patch protocol, or CI/server bridge.

## Current-to-target gap map

1. `EntityRef`/`IdentityMap`: no provisional-to-settled alias dictionary, namespace/authority epoch, durable per-kind allocator high-water mark, accepted-batch registry, or permanent negative identity knowledge exists.
2. `DbPatch`/`MergePolicy`: no canonical typed operation protocol with causal dependencies, base values, ACL evaluation, schema/reducer versions, domain-separated digest, or same-ID/different-content quarantine.
3. `SettlementCandidate`/`GitSettlementTransport`: no protected exact-old-OID publication, post-push acceptance verification, multi-remote fencing, rollback detection, or uncertain-ack recovery.
4. `CiObservationSource`: no provider-neutral push/pull/bundle adapter or stable run/job/shard/attempt identity feeding the textual DB.
5. Test evidence: mutable aggregate status does not preserve immutable observations or distinguish expectation policy and evaluation revision.
6. `ProviderBinding`/`BridgeDelivery`: model and envelope primitives exist, but durable canonical intent, local lease/retry state, read-back reconciliation, cursor ordering, and echo-loop prevention are incomplete.
7. `RetentionCatalog`: no typed dependency closure, exact/daily resolution contract, archive verification, resnapshot protocol, or confidentiality/deletion runbook exists for telemetry.

## Local architecture constraints

- SCV identities remain canonical; compact integers are aliases scoped by database namespace, authority epoch, and entity kind.
- SJ remains the only local mutation owner. Provider adapters produce validated patches and never directly edit a checkout/ref.
- The pure reducer contains no Git, jj, CI, GitHub, issue-provider, or network I/O.
- The existing database server is not the backend for this feature. CI and Git servers are intermittent external peers connected by typed adapters and immutable batches.
- A sibling jj/Git data workspace avoids reliance on submodules, merge drivers, `.jj` parsing, or live WAL/database-file replication.
- Production completion will require batch complexity, warm latency, RSS, Git pack growth, and network-byte evidence; integer-width speedups remain a hypothesis.

## Research risks to carry into requirements

- Fast-forward ancestry is not semantic admission or authorization.
- Multiple writable settlement remotes create split brain unless exactly one `(namespace, authority_epoch)` is fenced as allocator.
- Force-push, restore, or direct administrator updates can regress allocator state; settlement receipts and recovery policy must detect this.
- Untrusted CI bundles require strict size/path/archive/parser quotas and quarantine even if never executed.
- Webhooks and expiring artifacts cannot be the durable discovery queue.
- Permanent Git ancestry conflicts with guaranteed erasure of secrets/PII; admissible metadata and external encrypted evidence need explicit policy.
- Sequential allocation is order-dependent, so deterministic equality applies to the same accepted ordered log, not arbitrary equivalent operation sets.
