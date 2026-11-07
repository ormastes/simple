# Persistent startup reconciliation in the existing host ledger

Status: source reviewed, seven scenarios authored, NOT_RUN. This is the actual
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

Only absent rows that never committed begin, or previously recorded the exact
prepared-abort outcome, are cancelled/released. Executing recovery becomes
outcome-unknown; absence from inventory alone never releases it. Unknown rows stay
charged. Historical released allocations can sum above capacity, so quarantined
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

The selected WAL profile is `process-crash-v1`; archive fsync does not upgrade
journal power-loss guarantees. Every fresh service startup must inventory again.
Empty journal sequence0 binds an empty commit digest honestly. No invented hash,
request boolean or copied nonce enables the Container owner.

Startup scanning is bounded by4096 journal rows and4096 inventory entries. Current
matching is bounded nested scanning performed once at startup, not per request;
large-history latency/RSS remains unmeasured. Future optimization must preserve
complete duplicate/charge checks. Specs use real journals and the actual Windows
adapter's explicit scripted inventory seam, not native platform qualification.
