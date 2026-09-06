# NVFS Operation Lease Owner V1

## Scope

Device-backed `NvfsPosixDriver` values are copyable. Identity validation alone
does not fence the interval between validation and DBFS I/O. This owner adds one
bounded process-canonical serialization domain for each committed device
identity binding.

## Ownership and lifecycle

The mutex-protected owner indexes the same slot as
`NvfsDeviceIdentityBindingV1`. A copied binding is only a lookup handle. Each
slot permits at most one active operation nonce, and one global active nonce
serializes the process-global NVFS file/open arrays across device slots. Thus
two driver copies cannot enter hosted NVFS/DBFS state concurrently. Operation end
consumes that exact nonce; replay is rejected.

Close changes `Active -> Draining` before inspecting the active nonce. New
operations then fail closed. A close attempt observing an operation returns
`Busy` while retaining `Draining`; after the operation ends, the same binding
may retry and enter `Closing`. A determinate DBFS busy preflight restores
`Active`, a determinate cleanup failure enters `Retryable`, successful exact
teardown enters `Free`, and indeterminate cleanup enters permanent
`Quarantined` state.

The driver registers the operation slot only after device identity activation.
Every filesystem operation runs through `_with_owned_operation`, which acquires
and consumes either the exact device-bound nonce or an unbound hosted nonce on
both success and ordinary error. Thus hosted and owned adapters cannot race the
same process-global file, descriptor, or NVMe allocation state.

## Bounds and performance

Capacity is fixed at 256, matching the identity owner. Hot-path begin/end and
close transitions use the binding's authenticated owner-slot hint and are
O(1). There is no per-operation array growth or payload copy. Only registration
performs a bounded duplicate scan.

## Connector integration

`nvfs_vfs_connect_owned_device` constructs the identity-bound driver, mounts it,
then opens the exact `NvfsMountSessionV1`. Every connector lookup validates the
stored session and interface before copied-driver dispatch. Close obtains an
operation fence, performs an exact side-effect-free DBFS busy preflight, closes
the session, and then finishes teardown. Session-close failure cancels both
close owners; determinate post-session teardown failure retains the bounded
slot for retry without replaying the session close. Success removes the slot.
