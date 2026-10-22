# Artifact owner retirement and fenced retry

Requirement: [REQ-IM-007](../../../../02_requirements/feature/incremental_build_metadata_20261008.md).
Executable: [artifact_owner_recovery_spec.spl](../../../../../test/03_system/compiler/incremental/artifact_owner_recovery_spec.spl).

Status: authored, execution and docgen UNRUN. These scenarios call production
recovery, broker receipt collection, service and coordinator APIs. The files
represent explicit protocol fixtures; no live process death is claimed.

## Recover and retry

1. Claim action A and retain its original dispatch lease. Leave independent B
   queued. Install a canonical collected-tree observation fixture for A's exact
   broker launch identity.
2. Recover A into a new owner instance and generation. Observe the service
   queued with the old lease retained as a fence, coordinator pending, memory
   reservation zero, and a durable `tree-reaped.sdn`. The input route stays
   leased/running with its original reservation.
3. Attempt an old-generation claim and old completion before retry. Neither may
   start or publish A.
4. Retry using a new generation and the same lease token. Retain the returned
   lease at dispatch. Submit the old lease, then omit the lease entirely. Both
   commits must fail and leave the successor running without a CAS publication.
5. Complete using the retained successor lease. Observe exactly the expected
   object, released reservation, and B still queued. A further recovery fails.

## Completion wins before recovery

Publish under the original lease first. Recovery must reject the completed
action before collecting a reap receipt and preserve its published object.

## Unproven retirement

Exercise five file states: absent terminal proof; live process with timeout;
incomplete descendant cleanup; terminal proof already retained for a different
lease; and a terminal observation carrying another launch identity. Every case
returns an error and preserves both owners and the reservation. Timeout alone
never grants recovery authority.

## Binding mismatch

Independently change worker, generation, snapshot, cache identity, lease token,
process identity, completed flag, or successor generation. Every rejection
must precede receipt collection. A separate case alters the coordinator token
and confirms that the service stays leased.

## Remaining qualification

The fixture suite does not prove actual cgroup/job retirement, OS process
identity retention, concurrent parent serialization, spawn/dispatch wiring,
durable parent journal replay, or performance. The caller must retain trusted
parent launch/binding state, serialize transitions, and persist a recovered
route before dispatch if its parent state is durable. Existing unrelated
bounded model tests remain separate evidence and are not rerun by this change.
