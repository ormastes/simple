# Paged retention owner: proposed authority and storage contract

Status: design addendum only. Retention B source is **not implemented** by this
document. The selected requirements and thresholds are unchanged: REQ-030 through
REQ-035, with Operating B and NFR-002, NFR-005, NFR-007 through NFR-010. This is an
implementation refinement of selected Retention A, not a new requirement option.
No generic codec, returned receipt structure, local catalog update, or dry-run
result constitutes deletion authorization. Native execution and scale evidence
remain unavailable at this checkpoint.

## Existing source and concrete gaps

The bounded reference owner in `src/app/scv/db/retention_store.spl` supports local
catalog/pin/rollup/deletion-intent recovery. Its catalog is capped at 256 entries,
pins and cohorts; it materializes evidence into a bounded 32 MiB read set and
rewrites the catalog during deletion. `DbDailyRollup` retains identity and input
arrays. Those contracts do not provide a million-observation retention owner.

The separate streaming hydration implementation reads SCVE1 using the existing
incremental SHA-256 implementation, verifies the original semantic evidence
digest, and supports disk-backed closure observation without loading keys.
Closure receipts describe bytes observed during a scan; they do not establish a
durable pin or authorize unlink. Restricted ciphertext remains opaque. Native
hydration is currently implemented for Windows/Linux; other hosts fail closed.

Reusable infrastructure includes immutable page objects, authenticated local
paged reduction, indexed lookups, SJ-held generation CAS, signed settlement
receipts, actual Git/index readback, and the trusted low-level
`db_evidence_delete_held` effect. That effect explicitly depends on its owner for
retention authorization. It is not a cross-replica deletion gate.

The current settlement queue constructs monolithic state/identity snapshots.
Protected publication of an authoritative paged manifest and its exact page
closure is a prerequisite still missing from this proposal's destructive path.
Existing local pending work also does not establish a globally acknowledged
evidence pin. A local lease cannot substitute for either missing guarantee.

## Reserved semantic records

Retain the existing UID, alias, accepted-batch and actor-counter machinery. Do
not introduce a separate local catalog whose HEAD appears to grant Git authority.
All records use the existing physical `db_record_key(RowItem(ref))` representation
and normal typed fields. The following entity kinds are reserved; generic
producer admission must reject every operation targeting them. A specialized
owner must reconstruct the exact signed transition before calling trusted
internal paged infrastructure.

| Reserved kind | Exact ordered unique fields | Content contract |
|---|---|---|
| `retention_object` | `[digest]` | Content size, dependency-set digest, classification, created day, availability state |
| `retention_edge` | `[source_digest, target_digest]` | Immutable dependency edge tied to verified source envelope |
| `retention_pin` | `[root_digest, reason, principal]` | Exact closure revision, reason, principal and authorized expiry |
| `retention_observation` | `[stable_identity]` | Immutable normalized input digest, payload digest, cohort/day, outcome and duration |
| `retention_cohort` | `[day, cohort_digest, aggregation_revision]` | Current immutable rollup reference |
| `retention_rollup` | `[cohort_uid, generation]` | Counts, sum/min/max, mergeable histogram, input-set Merkle root and previous revision |
| `retention_reservation` | `[object_digest]` | Policy revision, base catalog root, rollup coverage, mark root, store identity and fencing generation |
| `retention_deletion` | `[reservation_uid, store_id]` | Actual unlink/absence observation and durability receipt provenance |

Keys use existing canonical typed values and declared unique-index ordering.
Schemas and merge constraints are structural policy: enabling this model or
changing its constraints requires an explicit compatible protocol selection or
migration. Existing reference/projection formats must not silently change.

Rollups must not carry corpus-sized identity arrays. The immutable observation
index provides collision detection and deduplication; the rollup input-set root
binds the exact indexed cohort membership. A repeated stable identity with a
different immutable input is a conflict, not a second count. Late input creates a
new generation and input-set root. Histograms and sufficient statistics merge;
daily percentiles are never averaged. These are proposed contracts, not claims
that the current array-based reducer already implements them.

## Proposed interfaces and transaction boundaries

Provisional interfaces for the implementation review:

```simple
db_retention_plan_at(captured_view, intent, policy, bounded_actual_proofs)
    -> Result<DbRetentionTransition, text>

db_retention_apply_owned(root, expected_head, signed_patch, intent, policy)
    -> Result<DbPagedApplyResult, text>

db_retention_publication_readback(root, authority, receipt, index_config, plan_id)
    -> Result<DbRetentionPublishedReservation, text>
```

`DbRetentionTransition` contains the required operations and canonical provenance
digest. Planning is pure over verified actual page contents. The effect owner
reopens the captured generation, verifies the original patch signature, ACL,
metadata policy and actor-counter identity, then reconstructs and compares the
exact operations/provenance. Caller-supplied operations or a `verified` boolean
cannot bypass this reconstruction.

Dry-run planning uses bounded page scans and disk-backed mark/join work to prove
the complete current pin and active-root dependency closure. It binds its mark
root and catalog generation, verifies the 28-day minimum and exact rollup
coverage, and does not unlink. Quotas apply while emitting work and before IO;
there is no million-record in-memory array. Exact resource limits and measured
maintenance performance must be reviewed with the eventual implementation.

Publication readback must independently fetch the actual accepted Git tree,
authenticate the signed settlement receipt, verify the three receipt-index paths
and protected index authority, and read/hash the precise paged manifest/pages
containing the reservation, rollup and pin-mark root. A digest supplied by the
caller or a local page manifest alone is insufficient. The returned structure is
data: a deletion owner must independently establish the same facts and current
fencing state before acting; possession of the structure is never authorization.

Network/readback work remains outside SJ. Before a bounded unlink batch, the
owner acquires the actual SJ lease and checks the expected local generation,
checkpoint barrier, current reservation, age, closure and rollup coverage. It
persists deletion intent before the effect and records actual deletion receipts
afterward. Restart recovery must not invent success from missing local state.
This local sequence is necessary but does not close the remote concurrency race.

## Canonical fencing and restoration: prerequisites and open decisions

A new remote pin can arrive after a fresh Git readback but before a local unlink.
SJ serializes only one checkout. Therefore a canonical reservation must fence
affected object availability across every participating admission path. While
reserved, new pins and evidence references whose closure reaches that object
must be rejected, including indirect dependency paths. A reservation cannot be
cancelled by simply clearing its row after a deleter has read it.

The following protocol choices remain open and must be frozen before destructive
implementation:

1. **Pending work protection.** Producer acknowledgment must first establish
   canonical evidence protection, or an enrolled-replica pending-inventory barrier
   must account for every relevant producer. The barrier's enrollment, expiry,
   revocation and unreachable-replica behavior require an explicit contract.
   Unreachable work must not be age-pruned or silently excluded.
2. **Fencing generation and delete grant.** Specify the authoritative store owner,
   monotonic fencing generation, replay/cancellation behavior and stale-worker
   rejection. A signed historical reservation alone cannot authorize a later
   delete after restoration.
3. **Restoration.** Actual digest-verified dependency closure must be restored and
   durable before canonical availability changes. The protocol must fence or
   retire all previous delete grants before admitting new pins/references. Key
   availability and restricted evidence permissions remain separate; ciphertext
   existence does not imply decryptability.
4. **Protected paged publication.** Define the exact canonical manifest/page
   projection, required protected remote/index capabilities, fetched content
   verification and interrupted-publication recovery. Local Git fixtures do not
   prove live provider protection.
5. **Reservation lifecycle.** Define whether repeated retention cycles reuse a
   reservation entity with monotonic generation or create immutable grant records
   behind a unique object head. Preserve historical receipts and prohibit stale
   grants in either case.

Until these prerequisites are implemented, destructive entry points must report
typed `PUBLICATION_REQUIRED` or `FENCE_REQUIRED` outcomes and perform no unlink.
No stub returning those errors should be presented as a completed retention B
owner. Query resolution remains honest: actual verified bytes may establish
`exact`; verified compatible rollup coverage may establish `aggregated`;
restricted data reports `restricted`; missing proof or bytes reports
`unavailable`. A manifest alone is never evidence that bytes still exist.

## Minimum cohesive implementation slice and agent outline

The first source slice can implement reserved codecs/schema and index checks,
exact signed local transitions, indexed observation deduplication/cohort rollup
updates, pin-aware disk-backed dry-run manifests and honest resolution queries.
It must explicitly stop short of cross-replica deletion. No retention B source is
added by this checkpoint.

| Owner lane | Proposed files/scope | Required review boundary |
|---|---|---|
| Core semantic owner | `db_retention_paged_records.spl`, `db_retention_paged_plan.spl`; additive generic reserved-kind guard | Exact typed indices, original signed operations, structural policy pin and bounded proof coverage |
| Application owner | `retention_paged_store.spl`, `retention_paged_mark.spl`; actual page IO and disk work | Captured roots, cumulative quotas, no flattened corpus and no fabricated deletion authority |
| Publication/fence owner | Paged candidate projection/readback and deletion-grant protocol, files to be frozen | Protected remote/index facts, pending-work barrier, stale-worker/restoration races |
| Tests/reviewer | Focused unit and real-filesystem integration specs plus selected system scenarios | Independent source review; native correctness, crash and performance receipts remain separate |
| Integration owner | Root lane: design alignment, shared interfaces and commit integration | Preserve other active lanes and distinguish implemented source from evidence |

Sidecar implementation: N/A at this checkpoint. The root integration owner is the
merge owner; a reviewer independent of the corresponding implementation lane
must assess deletion fencing before any destructive path is enabled.

## Acceptance source cases

- Identical observation replay leaves counts unchanged; changed content under the
  same stable identity fails atomically. Wrong unique-field ordering is rejected.
- Late input creates a new immutable rollup generation/input root. Unequal daily
  sample counts merge into the correct histogram/statistics without averaging
  percentiles; count/duration overflow fails closed.
- Diamond dependencies deduplicate closure; missing/corrupt evidence, depth,
  object-count and cumulative byte limits reject during bounded traversal.
- A day-27 object is exact at day 28; a day-0 dependency reachable from it remains
  protected. Unresolved, release, pending and reproduction pins cover all edges.
- A new pin/reference racing a reservation is either accepted before reservation
  and included in its mark proof, or rejected by canonical fencing afterward.
- Forged publication structures, wrong accepted tree, missing/disagreeing index
  entries, stale manifests and unprotected remote capability all prevent unlink.
- Restart at intent/effect/receipt boundaries preserves receipts and never turns
  ambiguous remote effects into success. A checkpoint barrier blocks mutation.
- Restoration retires old delete grants before new references are admitted; a
  delayed worker cannot remove restored bytes. This case remains blocked until
  the fencing/restoration protocol is resolved.
- Restricted evidence is verified as opaque ciphertext without loading keys;
  ordinary hydration and metadata rules preserve the existing confidentiality
  boundary. Rollup existence is never returned as exact raw evidence.
- Million-observation dry run, 10k updates and 100 MiB hydration retain the
  unchanged NFR thresholds and require actual host/runtime receipts. Source
  fixtures alone do not satisfy throughput, latency or RSS acceptance.
