# SimpleOS VFS File-Object Owner Blocker

Status: implementation intentionally reverted; no backend I/O authorized.

## Required invariant

The canonical VFS boundary needs a bounded, O(1), opaque generational
`VfsFileObjectRef` that binds one live FAT32, DBFS, or NVFS backend instance and
open handle to its authoritative mount generation. Access/status state, scoped
pins, close transaction state, and terminal quarantine must remain inside that
owner. OFD/fd/syscall code may never receive a raw driver pointer or reusable
backend capability.

## Exact blockers

1. Simple structs are copyable values. A dispatch or close ticket containing
   backend identity can be retained after `unpin` or copied and presented to a
   driver multiple times. Validating the token before returning such a value
   does not enforce scoped use or exactly-once backend close.
2. A caller-constructed `(filesystem_instance_id, mount_id,
   mount_generation)` tuple is replayable and is not mount revalidation.
   Freshness must be sealed and checked by the existing canonical `MountTable`
   owner; a second epoch registry would create competing mount authority.
3. Indeterminate backend close cannot free or reuse a slot. The design must
   account for the fixed retained-quarantine budget and expose an owner-only,
   evidence-backed recovery transition, or explicitly accept permanent
   capacity loss. Replaying close is forbidden.
4. Lifecycle coverage must exercise the package-private owner itself: capacity,
   stale generation after reuse, mount revoke/remount, pin versus close, copied
   token rejection, confirmed close, indeterminate quarantine, and recovery.
   Pure validator/transition tests are insufficient evidence.

## Safe implementation shape

- Extend `MountTable` to mint an opaque epoch seal and revalidate it under the
  same mount lock/generation state used for open and unmount.
- Keep backend identity private. Backend read/write/seek/close must execute via
  an owner-controlled operation or callback while the owner validates a live
  nonce; never return backend identity as dispatch authority.
- Atomically consume close authority before entering a backend. A confirmed
  receipt advances generation. An indeterminate receipt enters a bounded
  quarantine whose recovery requires backend-instance-specific evidence that
  the old handle can no longer act.
- Only after those interfaces exist may the OFD owner store a
  `VfsFileObjectRef`; fd compatibility and syscalls remain later consumers.

## Rejected draft

The 2026-08-24 draft had bounded O(1) slots and fail-closed generation/nonce
exhaustion, but exposed copyable backend dispatch/close values and trusted a
caller epoch tuple. Independent static review rejected it. The source and its
spec/design were removed rather than leaving an attractive unsafe API.

No tests, builds, SPipe, benchmarks, optimizer, or runtime verification were
run for this blocker record.
