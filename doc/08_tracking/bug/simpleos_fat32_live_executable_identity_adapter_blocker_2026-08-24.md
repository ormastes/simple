# FAT32 live executable identity adapter blocker (2026-08-24)

## Status

Blocked fail-closed. The committed point-in-time identity owner must not be
wired to launch yet.

## Evidence

- `Fat32Filesystem.mutation_active` serializes public mutations routed through
  one live filesystem instance, but `open_at` and `resolve_path` do not enter
  that serialization domain. No mount-generation contract currently proves
  that every live FAT access is routed through the same instance.
- `open_at` and `resolve_path` do not enter any mutation owner. They may read a
  directory entry before a concurrent replacement and return a handle after
  that replacement.
- The raw directory scan now has a bounded fail-closed validator for ordinal
  sequence, LAST, type/cluster-zero, alias checksum, canonical short-field
  padding, UTF-16 scalar structure, terminator/padding, and the 255-code-unit
  bound. This closes malformed-name lookup, but the decoded result still does
  not retain a serialized raw-chain digest for
  `Fat32ExecutableObjectObservationV1`.
- `fat32_executable_identity_observe_v1` has its own mutex. That mutex is not
  shared with the FAT directory/FAT mutation paths, so observing a dirent and
  publishing its identity are separate linearization domains.
- `FileHandle` contains a locator and cluster/size snapshot but no mount,
  object-generation, or reservation seal. It cannot detect replacement before
  later reads, and an output leaf cannot remain reserved across compiler
  creation/write/flush/rename.

## Required prerequisite

Introduce one non-copyable, mount-scoped FAT operation owner before adding the
adapter. It must:

1. own a mount-scoped BPB/mount generation and serialization authority shared
   by every live directory lookup, open, and mutation path for that mount;
2. make lookup/open/create/write/flush/unlink/rename/atomic-replace enter that
   same owner rather than consult an object-local boolean;
3. retain the validated raw LFN-chain/alias digest from the bounded directory
   validator inside the same serialized observation used for launch;
4. atomically read the validated LFN chain and 8.3 dirent, publish the
   executable identity, and acquire a generation-bound open handle while the
   owner remains held;
5. provide a bounded output-leaf reservation whose owner-consumed release or
   commit receipt prevents create/rename/replacement races and cannot be copied
   into a second authority;
6. invalidate affected object generations during every directory mutation and
   invalidate the mount generation before releasing the device on unmount;
7. quarantine the mount if lock release, identity publication, reservation
   commit, or mutation invalidation has an unknown outcome.

The executable loader must continue rejecting FAT32 launch inputs until an
exact live handle proves the same mount generation, directory locator, raw
dirent/LFN digest, and object generation at byte-read time. A compiler output
path additionally requires an active output-leaf reservation from absence or
expected replacement through durable publication.

## Rejected shortcut

A package-level helper that locks only around `resolve_path` plus
`fat32_executable_identity_observe_v1` was considered and rejected. Existing
mutation callers would not share that lock, output compilation spans multiple
calls, and the resulting snapshot would still be a time-of-check/time-of-use
claim rather than exact live proof.
