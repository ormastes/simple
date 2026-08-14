# ARM64 SimpleOS VirtIO-BLK durable-write gap

Claimed: 2026-08-14 by the ARM64 server-executable lane.

## Reproducer

The ARM64 filesystem-exec kernel mounts a real FAT32 image through the
VirtIO-MMIO block device. Source now contains bounded sector-write and
negotiated FLUSH paths, but the canonical database runtime closure cannot yet
consume the target file/locking owners and FAT32 replacement rename is not
atomic. Consequently a filesystem-launched database server still cannot
honestly acknowledge a commit that survives a fresh QEMU boot.

## Implemented source prerequisites

- Bounded single-sector `VIRTIO_BLK_T_OUT` submission in the ARM64
  block-device owner, with the caller bytes copied into device-owned DMA.
- Negotiated `VIRTIO_BLK_T_FLUSH`, required by the file-sync owner.
- Existing single-owner queue discipline; no user pointer or raw
  pointer may cross into the device after submission.
## Remaining required proof and implementation

- Verify write/read parity and a fresh-QEMU reboot using the same writable disk
  image.  A serial marker, host-side image edit, or second in-memory read is not
  persistence evidence.

The block driver is necessary but not sufficient. The live FAT32
`rename_at` path currently links the destination and then deletes the source,
explicitly rejects destination replacement, and documents that the operation
is non-atomic. The database commit protocol requires atomic replacement of the
old database by the fsynced temporary generation. The filesystem owner must
therefore add crash-safe atomic replace semantics (including recovery of an
interrupted metadata update) before the target adapter may report ready.

`src/os/apps/servers_user/database_persistence_adapter.spl` is the fail-closed
target capability boundary. Until durable file sync, atomic replace, and crash
recovery are all true, `servers_user` exits before publishing its HTTP or
database listener. This preserves `DbServerCapsule`'s canonical contract; it
does not replace it with a target-specific save path.

The remaining adapter work must also remove the hosted implementation
assumptions in `std.database.atomic`: its lock retry/stale-owner path currently
shells through `rt_process_run` to `date`, `sleep`, and `ps`. SimpleOS needs
owned monotonic-time, bounded-wait/yield, and task-liveness operations (or an
equally strong kernel-owned lock primitive). Providing fake timestamps,
unconditionally deleting a lock, or treating a successful close as fsync is
not acceptable recovery.

## Adjacent root-cause shape

Reject payloads other than exactly 512 bytes and reject write/flush completion
timeouts or nonzero VirtIO status.  This covers the adjacent corruption risks
from partial sectors and falsely successful device completion.

Also reject a rename implementation that only creates a second directory
entry and later unlinks the first, or that fails whenever the destination
already exists. Both shapes violate the atomic replacement commit point even
when the underlying sector writes eventually succeed.

## 2026-08-14 capability preflight correction

The offline ARM64 gate previously called the adapter helper with only the
runtime ABI bitset. That helper implicitly read FAT32 mounted-state globals,
which are correctly unpublished in a host-side process, so the gate reported
`ready=false` before QEMU could mount and recover the image.

The adapter projection now takes explicit typed FAT32 evidence. Production
still supplies `fat32_atomic_replace_caps()` and therefore remains fail-closed
until mount/recovery publishes truth. The offline structural gate calls
`fat32_atomic_replace_caps_probe` with the canonical Simple SARD descriptor and
the harness's exact 256 MiB/512-byte-sector/32-reserved-sector geometry. The
descriptor constructor mirrors the `make_os_disk.c` provisioner fields and
CRC32C. Focused coverage rejects corrupt CRC, journal start/count, and sector
size. The gate neither publishes mount globals nor manufactures a production
capability.
