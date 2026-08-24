# Stable File Snapshot V1

## Contract

`MountTable` is the sole mutable owner. `open_stable_snapshot(path, max_size)`
opens one backend handle and returns only an opaque generational lease plus the
captured size. Reads accept 1–65,536 bytes and return an independently owned
chunk. A read at or beyond the captured EOF returns an empty chunk. Callers
cannot obtain the backend or virtual file handle.

Every read revalidates the mount, namespace, and content generations before
dispatch. Any admitted mutation therefore makes the lease stale without
silently switching it to newer bytes. Staleness does not consume the lease:
the owner can still close it exactly once. Close consumes the registry entry
and underlying virtual handle even when backend close reports an error, so a
replay never dispatches a second backend close. An active lease keeps its
virtual handle live, and consequently blocks unmount with `Busy`.

The contract requires all access to the mounted `DriverInstance` to remain
behind the owning `MountTable`. Copying or separately mutating a backend after
mount is outside this authority and cannot be described as a stable snapshot.

## Ownership and bounds

The table owns at most 1,024 lease records. A lease is a scalar handle copied
across the API boundary; the registry record and backend handle never move.
Each read returns an owned array because caller-visible mutable `[u8]` reuse is
not yet proven by the shared driver trait. Files are admission-bounded to 1 GiB
and each operation to 64 KiB. No whole-file allocation is performed.

## Performance and memory analysis

Lease lookup is O(1); mount lookup is O(M), where M is bounded by 4,096. Lease
admission is O(L), where L is bounded by 1,024, and reuses generational slots.
DBFS/NVFS dispatch uses their bounded read-at seams. FAT32 allocates at most the
requested 64-KiB buffer plus the independently owned result prefix. Snapshot
state is fixed-size metadata per admitted lease, with no retained file bytes.

FAT32 cluster traversal is O(offset-clusters + requested-clusters) per call;
sequential chunking can therefore remain quadratic for large files. The API
does not claim a cursor cache because a mutation-safe cluster-chain cursor is
not yet an owned backend primitive. Runtime timing and peak-RSS evidence must
use the same 1 MiB, 64 MiB, and 1 GiB fixtures when an admitted Simple runtime
is available; this implementation does not fabricate those measurements.

## Failure semantics

Malformed, zero-length, oversize, overflowing, forged, retired, or replayed
requests fail before backend read dispatch. Directory and over-limit opens
close their temporary backend handle. Generation mismatch returns
`StaleHandle`; close remains valid afterward. Slot generations never wrap:
terminal slots retire permanently.
