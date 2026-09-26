<!-- codex-architecture -->
# SimpleOS NVFS root owner cutover

## Status

Proposed for the initial SimpleOS release. The selected requirements are
`doc/02_requirements/feature/simple_platform_unification.md` REQ-008,
REQ-009, REQ-010, REQ-012, REQ-017, and REQ-018. This document records a
source-level architecture decision; no guest qualification is implied.

## Context

Two current file routes diverge. `src/os/kernel/boot/nvfs_root_mount_transaction.spl`
publishes the NVFS/DBFS-backed root into the `MountTable` owned by
`src/os/services/vfs/vfs_boot_state.spl`. Its positioned binding API is in
`src/os/services/vfs/vfs_positioned_ops.spl`. In contrast,
`src/os/kernel/ipc/syscall_file.spl` syscall 30 still opens through the
kernel FAT32 mount and `FD_TYPE_FAT32`. The PID1 catalogue payload in
`src/os/services/vfs/vfs_service_main.spl` separately initializes NVMe and
mounts a private FAT32 root. `src/os/kernel/fd_io.spl` has an owned IPC VFS
client, but syscall 30 does not call it.

The existing `src/os/kernel/fs/positioned_fd_owner_v1.spl` already reserves a
descriptor, opens a MountTable binding, publishes an OFD, and rolls back a
failed publication. It is not called by the production file syscalls. The
current syscall gate deliberately rejects `/srv/data` protected opens with
ENOSYS for this reason; see
`doc/05_design/os/storage/server_data_namespace_syscall_gate_v1.md`.

## Decision

For the first release cutover, the kernel's canonical MountTable remains the
single writable NVFS root owner. The production file syscall path consumes
`positioned_fd_owner_v1` with a lifecycle key derived from the scheduler's
current TCB. It does not mint a key from a userspace PID or FD number. Read,
write, seek, sync, dup/fork, close, and exit cleanup must use that same OFD and
MountTable binding before syscall 30 may select the NVFS route.

The catalogue `vfs` endpoint remains a protocol service, but its production
backend must request operations from that single root owner through a
dedicated, bounded, catalogue-authorized kernel boundary. It must not call
public file syscalls 30–39, which already route to or may route through the
VFS service, and it must not remount the NVFS disk independently. The current
private FAT32 payload remains a development compatibility route until the
bridge and admission gates exist. No V1 wire number is frozen by this ADR;
the private boundary requires an ABI and capability review before coding.

```text
Simple app -> SOSIX/client -> named vfs service -> private root bridge
                                                  |
public file syscall -> task FD/OFD owner --------+-> one MountTable -> NVFS
```

Root publication must bind the admitted image/namespace identity, exact
`NvmeFilesystemLease`, mount generation, and positioned route. Service restart
may reconnect to that generation; it must not create a new writable mount.
Unmount or owner revocation invalidates both routes before storage release.

## Rejected initial shortcut

Mounting NVFS again inside `vfs_service_main.spl` would give kernel and
catalogue independent mutable DBFS/NVFS state over the same media. The
existing `NvfsMountSessionV1` records a process-local lease identity; it
does not transfer the kernel's live MountTable, device owner, or outstanding
OFDs across address spaces. A direct service remount is therefore not a
release cutover.

## Consequences and proof obligations

- Existing MountTable, OFD, descriptor, and task-lifecycle owners remain the
  authorities; no second scheduler, mount table, or FD table is introduced.
- O_CREAT/O_TRUNC and append require their own filesystem transaction or
  atomic append backend. `positioned_fd_open_existing_v1` intentionally
  rejects them. They cannot silently fall through to FAT32 on an NVFS root.
- A failed open, short copy, failed close, service crash, or reboot must leave
  a recoverable or terminal owner receipt and no alias to a retired binding.
- Qualified evidence must include two independent callers observing the
  same file, an exact generation on service restart, wrong-task and stale-FD
  rejection, no second mount, and cold-boot write/reboot/read persistence.
- Until those gates pass, neither `vfs` endpoint readiness nor a copied IPC
  round trip proves NVFS-backed POSIX I/O or SimpleOS release readiness.

## References

- `doc/04_architecture/os/simpleos/desktop/simpleos_shared_nvme_storage.md`
- `doc/03_plan/os/simpleos_nvfs_root_owner_cutover.md`
- `src/os/kernel/fs/positioned_fd_owner_v1.spl`
- `src/os/kernel/fs/active_fd_context_owner_v1.spl`
- `src/os/services/vfs/vfs_nvfs_root_transaction.spl`
