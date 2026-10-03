# Item 2 implementation and test-source wave

User steering: implement the complete selected scope and its test code first.
An unavailable admitted test runner is an execution gate, not permission to stop
writing the selected production owners. Authority A / Adapters A / Operating B /
Retention A and the 36 functional plus 15 nonfunctional requirements remain.

This is a source-progress record. **Execution is UNVERIFIED.** No authored test,
static diff check, provider fixture or source inventory is RED/GREEN, coverage,
crash durability, cross-platform qualification, or a measured scale result.

## Integrated source contracts

| Area | Production owner | Source behavior |
|---|---|---|
| Canonical protocol | `src/lib/scv/db_canonical.spl`, `db_patch.spl`, `db_patch_normalize.spl` | Tagged domain framing, minimal unsigned encoding, Unicode NFC, duplicate-key rejection, typed patches and content identities |
| Reducer | `db_reducer.spl`, `db_schema.spl`, `db_remove_wins.spl` | Scalar/list conflicts, field authority, observed add-wins and explicit causal remove-wins sets, constraints, original actor/counter collision detection and retained semantic bases |
| Snapshot | `db_snapshot.spl`, `db_snapshot_values.spl` | Strict complete versioned recovery with semantic digest verification, quotas and no trailing data; v2 includes actor/counter/base registry |
| Admission | `db_admission.spl` | Actual Ed25519 verification, independently pinned scope policy, key windows/revocation, CI append-only authority, repeated verification at effect boundary |
| Local storage | `src/app/scv/db/local_store.spl`, `local_apply.spl` | SJ-owned compare-and-publish, complete immutable generation, bounded no-follow reads, safe staging, fsync barriers and retry durability; authority/schema context bound in stored header |
| Offline identities | `offline_actor.spl` | Durable reservations conservatively rotate a random incarnation on every reservation, including reuse after restoring an old counter and old copied handle |
| Evidence | `db_evidence.spl`, `db_ci_ingest.spl` | Pinned config/expectation/reproduction revisions, provider identities, manifest coverage, provider DTO normalization and receipt-gated cursor transition rules |
| Evidence storage | `src/app/scv/db/evidence_store.spl` | External typed-envelope CAS, quota checks before IO, no-replace publication, actual byte readback and dependency-digest binding |
| GitHub discovery | `src/app/scv/db/github_provider.spl` | Bounded real gh API transport, scoped paginated runs and attempt jobs, tracked reruns, sanitized failure categories, injected transport tests and opt-in live read scenario |
| Bridge and retention | `db_bridge.spl`, `db_retention.spl` | Separate intent/delivery state, uncertain-effect reconciliation rules, exact retention boundary, closure pins, deduplicated sufficient-statistic rollups, honest resolution and resnapshot invariants |
| Settlement receipts | `db_receipt.spl` | Actual signed receipt bytes, pinned authority, hash-chain binding and allocator regression checks; Git ancestry remains an independent transport proof |
| Allocation projection | `db_allocation.spl`, `db_identity_snapshot.spl` | Admission before allocation, preserved canonical UIDs, contextual aliases, recursive typed-reference projection and complete allocator snapshot |

## Review findings addressed during coding

1. Local store paths previously followed aliases and read files without bounds.
   Reject existing directory/file aliases, stage securely, publish without
   replacement and bound HEAD/object reads. Path-based APIs still assume the
   trusted root is stable against hostile concurrent directory replacement.
2. Local snapshots previously lacked authority context. Persist a digest of
   repository, namespace, epoch and schema/reducer revisions; reopening under
   another context fails instead of silently reinterpreting rows.
3. Batch digests alone did not detect actor-counter reuse. Bind actor/counter
   to accepted digest and retained prior semantic revision; reject collisions.
4. Unknown base revisions previously passed admission. New nonreplay plans
   require a retained current/historical/genesis base.
5. A copied actor handle plus rolled-back bytes could reuse an offline UID.
   Reserve a fresh incarnation before acknowledgement and retain retirement
   evidence. This trades per-reservation files/entropy for correctness until a
   proven process-owned noncopyable counter owner exists; no scale claim follows.

## Remaining integration and execution gates

Finish candidate publication coordination, durable signed receipt/index recovery,
identity alias resolution through admission, metadata and restricted-evidence
integration, durable CI cursor/manifests, provider effects/outbox recovery,
conflict lifecycle and complete resnapshot/catalog orchestration. The added
modules do not by themselves establish every requirement's end-to-end oracle.

Keep broad fail-fast system scenarios until their full oracles are implemented.
Run new source tests with an admitted pure-Simple runner, then full selected
acceptance, required runtime/MCP checks, generated-manual validation, host
qualification and Operating B measurements. Do not describe later regression
execution as an earlier test-first RED/GREEN cycle.

The current path facade still fails closed on Windows canonical identity;
supported-host success tests must succeed, not accept that limitation as PASS.
SJ's existing stale lease recovery and actual process crash boundaries need
separate integration evidence. The private work PR remains a draft until those
release gates are satisfied; no protected branch or release tag is updated.
