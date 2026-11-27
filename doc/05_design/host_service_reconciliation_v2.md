# Persistent startup reconciliation in the existing host ledger

Status: eight reconciliation scenarios and three Windows private-receipt
scenarios authored, NOT_RUN. This is the actual
startup transition; installed service root and persistent SDK routing remain
separate composition work. No complete Windows host service is claimed here.

`host_service_reconcile_v2(owner,container)` requires the actual held host journal
writer and continuity=false. It calls common Container service inventory refresh
AFTER writer acquisition; the factory snapshot cannot bridge an earlier writer
race. Only the Windows service-incarnation mode enters this route. Native boot
stays empty and the ledger carries the explicitly opaque full-scope hash.

The complete native inventory is prevalidated before journal mutation: distinct
full native IDs/operation IDs, exact old scopes, retained common request and plan
hash, request digest, workload/attempt, and sufficient existing physical charges.
Unaccounted objects, duplicate identities, a native object with admitted-only
journal state, missing provenance or resource mismatch block readiness. No object
is adopted or deleted. Every observed object, including terminal state, remains
charged through its retained reservation.

Absent rows that never committed begin, or previously recorded the exact
prepared-abort outcome, are cancelled/released. A completed row preserves release
only when the shared capacity evidence dispatcher revalidates the exact archived
qualified wait, signed cleanup intent and native absence (or helper reap), and
the journal's immutable outcome digest matches that proof. Missing or corrupt
proof recharges the row; a Released flag alone is insufficient. Executing recovery
becomes outcome-unknown; absence from inventory alone never releases it. Unknown
rows stay charged. Historical released allocations can sum above capacity, so quarantined
open validates shape but does not grant availability. The final reconciled ledger
must pass the real capacity check before readiness; unresolved overcapacity stays
blocked.

A private immutable startup receipt records full scope, inventory digest, actual
journal authority/revision/sequence and every row classification. It is read back
and synchronized before constructing the common typed quarantine acknowledgment.
Only successful common acknowledgment allows continuity=true. Failed calls return
the updated owner after any cancellation. The filename hashes the complete
canonical receipt, binding the refreshed inventory and actual journal commit.
A retry after partial publication or cancellation preserves older turn receipts
and publishes a distinct current receipt when the facts changed. An older receipt
is never loaded as permission to activate the current owner.

On Windows, publication uses `windows_private_file_v1` generation-owned native
root/file capabilities. The actual handle owner validates service ownership,
protected DACL privacy and no-reparse ancestry. Complete bounded stage bytes are
sealed/flushed and read back before native no-replace publication. The stage
handle closes before opening the final entry, including collisions, through the
same private directory owner. Final bytes and current security must match.
The retained journal root and receipt directory revalidate native root/ancestor
privacy again after final-file verification, before cleanup and acknowledgment.
This uses the existing native query exposed by facade commit `eb6ab9bd17c`.
No Windows chmod/stat permission check is used. Corrupt or unsafe final entries
remain blocked without overwrite or repair. Interrupted stages remain evidence.

Every native failed-admission file/root token and failed close is retained in
`HostServicePrivateCleanupV2`. The reconciliation turn returns this cleanup with
the updated ledger/container and no admission. Its persistent caller retains the
whole turn and uses `host_service_reconcile_retry_v2`, which attempts cleanup
before another inventory/readiness attempt. A pending cleanup never becomes a
successful acknowledgment. This is an internal trusted owner boundary; no
serialized cleanup or caller-supplied ready flag is accepted.

Linux scripted-Windows-adapter tests retain the POSIX receipt implementation for
state-machine verification only. Those tests do not qualify Windows privacy.
The separate native Windows specs require an administrator-provisioned private
parent and a foreign-read ACL negative fixture; missing fixtures fail.

The selected WAL profile is `process-crash-v1`; archive fsync does not upgrade
journal power-loss guarantees. Every fresh service startup must inventory again.
Empty journal sequence0 binds an empty commit digest honestly. No invented hash,
request boolean or copied nonce enables the Container owner.

Startup scanning is bounded by4096 journal rows and4096 inventory entries. Current
matching is bounded nested scanning performed once at startup, not per request;
large-history latency/RSS remains unmeasured. Future optimization must preserve
complete duplicate/charge checks. Specs use real journals and the actual Windows
adapter's explicit scripted inventory seam, not native platform qualification.

All local verification processes share CPU affinity `0-4` (five cores total).
No compiler, native test or engine execution was run for this source checkpoint.
