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

## 2026-08-22 DBFS/NVFS positioned-read progress

`DbFsDriver.pread_bytes_handle` now exists and supplies byte-exact offset,
short-EOF, zero-length, negative-range, and overflow behavior to the stdlib
NVFS and NVFS-POSIX frontends.  This removes the missing-provider defect and
avoids the old text conversion, NUL truncation, per-character concatenation,
and EOF padding on binary reads.  The device implementation still must read a
prefix through the current device-owner API before selecting the requested
suffix; a future device read-at primitive is needed to make memory and I/O
strictly O(request length) for large offsets.

Caller-owned buffer reuse remains unproven and is deliberately not claimed:
`FsDriver.read`/`pread` accept `[u8]` by value, while only concrete
implementations annotate their local binding `mut`.  Existing value/CoW
semantics do not establish that those writes reach the caller.  The stable
snapshot API must therefore return owned bounded chunks until a language test
and shared trait signature prove a mutable caller-visible ABI.

## 2026-08-22 bounded read-at seam

DBFS, NVFS, and NVFS-POSIX now expose the additive
`pread_bounded_bytes_handle` contract.  It accepts 0–65,536 bytes, rejects
negative, oversize, and overflowing ranges, preserves exact short-EOF binary
results, and returns an owned array.  The existing unrestricted byte-return
APIs remain compatible.

For device-backed DBFS, the namespace owner now translates the requested file
offset through the inode's blob binding before entering the device owner.  The
device loop therefore reads only sectors intersecting the result:
O(ceil((intra_sector + result_bytes) / sector_size)) device reads and
O(result_bytes + sector_size) live owned memory, excluding geometric spare
capacity while the result array grows.  A structural integration oracle
places an 8-KiB binary file on a counting device, reads 16 bytes at offset
4 KiB, and requires fewer than three sector reads; the former prefix route
would require at least nine.  It also checks exact EOF, NUL-capable binary
values, overflow, 64-KiB/oversize boundaries, independent ownership, and
unchanged canaries.

Caller-visible mutable read-into remains deliberately unimplemented: current
shared `[u8]` value/CoW semantics do not prove that a callee's `mut` binding
updates caller storage.  No mutable reuse or zero-allocation claim is made.
The remaining stable-snapshot work is the MountTable-owned generation/lease
registry and serialized mutation invalidation described above.
