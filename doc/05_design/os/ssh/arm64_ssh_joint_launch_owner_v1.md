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

## Current blocker: no reservable loader transition

It is not yet safe to publish the coordinator. The registry exposes an Armed
identity snapshot and the scheduler later commits the copyable token, but it
has no opaque `Armed -> JointReserved -> Committed` lease. Between snapshot
and SSH quarantine, another token holder could commit or revoke the registry
slot. Quarantining SSH first would then lose the request on a loader race;
adopting first could publish a task before the SSH owner reaches its terminal
state. A wrapper around the existing APIs cannot provide atomic success or
rollback and is therefore intentionally absent.

## Required owner transition and failure matrix

The next change must add a bounded opaque loader reservation whose mutex-held
begin operation returns the already-defined Armed identity, and a scheduler
adoption entry that accepts only that reservation. Lock order is scheduler,
loader registry, then SSH session owner; no callback may run under either raw
mutex. Before SSH consumption, any identity/path/consumer/binding rejection
aborts the loader reservation to Armed and leaves the SSH lease LaunchLeased.
After the SSH bound consume succeeds, loader commit/adoption failure must revoke
and close the exact reserved image while SSH remains Quarantined. Successful
adoption releases the retained image and leaves SSH Quarantined. Indeterminate
unlock or close results quarantine the loader slot and never retry adoption.
Token, reservation, SSH lease, and terminal receipts are bounded handles; x86
and RISC-V entrypoints remain unchanged.

## Visibility

No public direct ARM64 spawn API is added. The pure loader-half validator is
package-private, and the SSH owner exposes only an opaque-lease-consuming bound
transition. The future coordinator must be the only cross-owner composition
surface and must not export architecture context, address space, file handle,
or scheduler internals.
