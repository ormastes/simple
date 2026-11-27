# Host helper stream consumption and settlement

Status: IMPLEMENTATION / AWAITING_VERIFICATION. This owner composes the existing
host physical-capacity journal, SimpleContainerAPI and native group stream owner.
It adds no journal, process registry, supervisor or stdout reader.
This checkpoint requires an exclusive same-process host writer. It does not
implement an independently running host service gateway: smux must not open a
second HostLocalRoot writer. Prepare/consume/settle RPC authentication, a terminal
consume-proof verifier, and independently authenticated broker evidence remain
required for that composition. A typed lease, owner, or ACK is never serialized
as authority. Existing Linux broker file recovery assumes a trusted protected
root; it is not cryptographic attestation against a process that can write it.

## Ownership and entrypoints

`host_helper_open_output_v1` receives the current `HostCapacityOwnerV1`, common
container owner, execution request, exact runtime identity, output identity,
verified live `HostHelperLeaseV1` and trusted stream policy. It returns both
updated domain owners and at most one `HostHelperStreamRetainedV1`. The retained
value contains the verified helper lease, canonical outer output plan and one
actual `PipedProcessOwnedSpawnV2` outcome. Ready denotes an owned transfer in an
opening state, not confirmed engine execution or observed workload bytes.

Before calling the common output-open entrypoint, this owner checks the exact
executing journal operation, retained helper request and execution proof, and
the common plan/admission validator. It creates and synchronizes an exclusive
consumed-plan record under the existing journal root. An existing or uncertain
record never permits replay, even when its bytes match. The native exclusive
broker claim remains the independent final effect boundary for that exact root.
The record is metadata, not a serialized live lease or pipe handle.

Post-effect errors return the actual full native outcome. Failure to publish
correlation metadata cannot discard a Ready/CleanupRequired owner. A Rejected
outcome with no native owner remains charged until an explicit trusted absence
path is available; the implementation must not manufacture a reap certificate.

## Native correlation and release

`host_helper_settle_output_v1` receives the retained bundle. It validates the
canonical outer plan against the admitted helper and compares the final native
owner's normalized template digest with the retained template. The exact launch
deadline is compared separately because template normalization removes it.
Current grant freshness is irrelevant to cleanup and capacity settlement.

Settlement first requires the canonical durable cleanup proof. It then uses the
existing exact-owner `process_cleanup_piped_owned_v2(owner, nil)` recovery route,
which can retire the matching ticket or confirm it is already absent without
touching a successor generation. It does not retry a stale `Some(ref)` and does
not initiate cancellation when proof is missing. This supports smux's normal
sequence in which descriptor retirement precedes the host ACK.

The grouped lease is derived internally: group ID is the parent operation;
action and worker ID are the helper operation; lease ID is the prepared receipt
digest; generation, snapshot and cache identity come from the exact retained
plan. A caller cannot supply substitute correlation IDs or a reap receipt.
Canonical `group_process_stream_collect_reap_v2` supplies the actual native
terminal/known-unlaunched proof. Stream EOF, closed descriptors, elapsed grant
time and a provider boolean never establish process absence.

The cycle-free `host_helper_settlement_receipt_v1` module exposes
`host_helper_settlement_evidence_v1(root, original_operation) -> Result<text,text>`.
It reloads protected request/proof/consumption/native metadata and validates the
canonical native proof before returning outcome bytes. It imports neither the
capacity owner nor a live helper lease. The existing capacity owner's settlement
hook uses this same validator before completing the operation and on reopening.
Evidence is persisted before the journal outcome; any uncertainty stays charged.
The completed helper reservation records verified resource settlement. It is
not an assertion that engine attach or workload execution succeeded; native
known-unlaunched proof remains distinguishable from a collected child tree.

Success returns `HostHelperSettlementAckV1` with helper operation, outer request
digest, prepared receipt digest, native identity, tree proof digest, outcome
digest and actual returned journal revision/sequence. The ACK is produced only
after the capacity hook confirms the exact completed outcome. A failed turn
retains its bundle and the hook's returned owner; it never emits an ACK. Smux
matches the exact bundle before dropping its cleaned owner. Pipe handles are not
reconstructed from metadata during recovery.

`host_helper_recover_output_v1(owner, operation_id)` returns a
`HostHelperRecoveryTurnV1`, carrying the owner on every path and an optional
`HostHelperRecoveredStreamV1` containing the original operation, exact outer
plan, recovered canonical group owner and consumption digest. It restores no
pipe reference or live helper launch lease. The distinct
`host_helper_settle_recovered_output_v1` route shares evidence validation and
settlement with the live path; restored metadata cannot enter launch.

## Dependencies and acceptance

The common owner supplies canonical `container_output_plan_encode_v2/decode_v2`;
the daemon protocol supplies strict `group_process_stream_template_decode_v3`.
Restored plans remain data and cannot authorize launch. Host owns the surgical
same-journal release projection; this lane owns only new helper consumption,
settlement and receipt modules. All OS effects remain behind SimpleContainerAPI.
The currently implemented native receipt route is the existing Linux group
owner. Windows Job/ConPTY qualification and its common native-owner integration
remain a separate platform dependency; an OS name or restored record does not
advertise that capability.

Required cases include copied-lease/double consumption, partial archive failure,
request/proof/plan/template/deadline substitution, missing/unknown native proof,
actual no-child versus collected-child distinction, expired-grant cleanup,
receipt-before-outcome failure, stale journal owner, exact replay ACK and retained
owner after publication failure. Source-only and synthetic negative assertions
must not be described as native lifecycle execution. The selected journal
durability remains process-crash-v1; power-loss durability is not claimed.
