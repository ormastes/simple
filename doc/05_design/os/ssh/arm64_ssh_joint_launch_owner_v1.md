# ARM64 SSH Joint Launch Owner V1

## Safety boundary

The intended launch is a loader-owned transaction joining two independent
authorities: the global executable registry token and one session-owned SSH
request lease. Success must bind the exact canonical path, complete token
coordinate, verified ARM64 entry identity, pristine load consumer, and
`{session, channel, principal, request}` before scheduler adoption. Neither a
path, copied identity snapshot, SSH handle, nor lease alone authorizes launch.

The landed prerequisite `complete_launch_bound` makes binding validation plus
terminal SSH quarantine one indivisible session-owner operation. The loader
pure validator performs O(1) scalar comparisons and bounded text comparisons;
it rejects legacy no-entry identities, non-aarch64 targets, dirty consumers,
and every token/path/entry mismatch without mutation or image-size work.

## Loader reservation prerequisite

The registry now owns an opaque, nonce-bound
`Armed -> JointReserved -> {Armed, Committed, CloseInProgress}` transition.
Begin validates the exact token generation/nonce, canonical image identity,
verified ARM64 entry, and pristine consumer while holding the registry mutex.
It returns the already-defined bounded identity plus an opaque joint lease.
Abort requires that exact lease and restores Armed. Joint commit repeats every
bound input under the mutex before Committed handoff. Joint revoke moves the
same reservation directly to the existing close lease, so no Armed gap permits
a legacy commit or revoke race.

Legacy commit, retrieval, and token-only close reject JointReserved. Scheduler
adoption has a separate joint-reserved entry which submits the matching opaque
lease and all bound inputs to the registry commit before retrieval. Its legacy
entry is behavior-compatible and cannot consume JointReserved.

## Required owner transition and failure matrix

The future coordinator must begin the bounded loader reservation before it
consumes the SSH lease. Lock order is scheduler transaction, loader registry,
then SSH session owner; no callback may run under either raw mutex. Before SSH
consumption, any identity/path/consumer/binding rejection aborts the loader
reservation to Armed and leaves the SSH lease LaunchLeased.
After the SSH bound consume succeeds, loader commit/adoption failure must revoke
and close the exact reserved image while SSH remains Quarantined. Successful
adoption releases the retained image and leaves SSH Quarantined. Indeterminate
unlock poisons the complete singleton registry, making every slot inaccessible
even if the native unlock result followed an internal mutation. An ordinary
close failure enters the existing exact-slot CloseRetryable quarantine. Neither
case retries adoption.
Token, reservation, SSH lease, and terminal receipts are bounded handles; x86
and RISC-V entrypoints remain unchanged.

## Visibility

No public direct ARM64 spawn API is added. Reservation mint/abort/revoke and the
pure loader-half validator are package-private. Joint commit and scheduler
adoption accept an opaque lease that only the loader package can mint. The SSH
owner exposes only an opaque-lease-consuming bound transition. The future
coordinator must be the only cross-owner composition surface and must not
export architecture context, address space, file handle, or scheduler internals.
