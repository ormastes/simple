# SimpleOS stable VFS snapshot blocked by backend parity defects

Status: OPEN — prerequisite for live compiler-filesystem QEMU evidence

## Required outcome

The sole `MountTable` owner must provide a generation-bound stable read lease
for FAT32, DBFS, and NVFS with 1–65,536-byte caller-owned reads, exact EOF,
close/replay safety, mutation invalidation, and no whole-file allocation. This
is required before the guest may hash compiler/tool artifacts as evidence.

## Source-audited blockers

- `FsFat32Driver.pread` and `pwrite` ignore their explicit offset and delegate
  to cursor operations. They are not positioned operations.
- FAT32 cluster walking materializes/traverses the complete chain per read, so
  a sequential chunk scan can become O(file_size²).
- NVFS/NVFS-POSIX read-into paths allocate an owned chunk internally; DBFS is
  routed through `pread_bytes_handle`, but no provider definition was found.
- Simple `[u8]` is value/CoW and the current `FsDriver.pread` chain does not
  consistently declare mutable destination ownership, so caller-buffer reuse
  is not proven.
- `MountTable.positioned_write_bytes` does not advance `content_generation`.
  A generation-bound reader could therefore accept bytes changed through that
  route. Partial mutations followed by an error also require conservative
  invalidation.
- Direct backend mutation can bypass `MountTable` generations; stability is
  meaningful only when the VFS service is the serialized mutation owner.

## Acceptance evidence

Implement true explicit-offset binary read/write parity for FAT32, DBFS, NVFS,
and NVFS-POSIX; a mutable caller-buffer ABI or an honestly measured bounded
allocation contract; conservative generation advancement for every successful
or partial mutation; and a generational snapshot registry whose stale lease can
still be closed exactly once. Tests must cover NUL bytes, cross-cluster reads,
short EOF with suffix canaries, zero/64-KiB/oversize/overflow requests, stale
and forged leases, close replay, handle reuse, every mutation route, partial
failure, and serialized read/write interleavings. Retain identical 1 MiB,
64 MiB, and 1 GiB timing/RSS/allocation evidence when an admitted runtime is
available.

Do not enable the compiler-filesystem QEMU readiness gate with a cursor-backed,
whole-file, or host-synthesized substitute.
