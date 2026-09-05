# SimpleOS syscall MountTable bypass

Status: blocked; unsafe integration draft reverted after static review.

File open/read/write/close/sync still use the FAT32-only syscall owner. It
cannot serve NVFS/DBFS and can mutate FAT32 without invalidating stable snapshot
or executable-admission generations.

An attempted backend-neutral `vfs_fd_table` integration was removed because an
independent static review found that it was not safe to ship:

- global alias/cursor mutation lacked checked serialization;
- bounded alias publication happened after dup/dup2/fork, so failure could
  leave live generic descriptors without a backend owner;
- descriptor lookup was O(4096) on every I/O hot path;
- `O_RDONLY`/`O_WRONLY` were not enforced at the new boundary;
- FAT32 ignores `O_TRUNC`, and its existing positioned write path ignores the
  supplied offset;
- moving open to MountTable regressed FAT32 `O_EXCL` handling;
- no backend provides a proven atomic end-relative `O_APPEND` contract.

The safe implementation must use one O(1), checked-serialized open-file-
description owner. It needs reserve/commit/rollback for dup and fork, and an
operation pin protocol so no blocking driver I/O occurs under an unsafe lock.
Close must quarantine and retry a failed backend retirement without permitting
generation reuse. Open access/status flags belong to that shared description.
FAT32 positioned I/O and open flags must be corrected before it joins the
backend-neutral syscall route.

Additional follow-up: path mutations (`mkdir`, `unlink`, `rename`,
`rmdir`, and path `stat`) in `src/os/kernel/ipc/syscall_file.spl` still use the
legacy FAT32 mount globals. Add canonical owner wrappers for the corresponding
`MountTable` operations before removing `fat32_fd_table.spl`. `SEEK_END` also
requires a MountTable-owned fstat-by-virtual-object API.

## FAT32 positioned/open prerequisite blocker audit

A pure-Simple draft for supplied `pread`/`pwrite` offsets, `O_EXCL`, `O_TRUNC`,
and `O_APPEND` was statically rejected and fully reverted. Correct append is
not a local cursor fix because FAT32 currently copies size/start-cluster state
into each open handle and does not maintain one durable object identity.

The replacement must land as one coherent owner design with all of these
properties:

- A mount epoch remains monotonic across unmount/remount. Unmount must reject or
  retire live opens without clearing generation history, so an old handle can
  never alias a new-volume handle.
- File identity cannot be only a start cluster: unlink can free and reuse that
  cluster while an old handle remains live. Use a generational directory-entry
  object identity (or defer unlink reclamation until the last open reference),
  and update identity location across rename.
- Logical size and first-cluster changes must persist to the owning directory
  entry transactionally. Close/reopen, path stat, independent append handles,
  and remount must observe the same value. Cache the validated directory-entry
  location at open so append does not scan the open table or directory.
- Truncate must propagate `follow_chain` and every FAT-entry write failure. It
  may publish the new size only after all required chain mutations and directory
  metadata succeed, with a rollback/recovery state for partial device failure.
- Positioned writes beyond EOF must zero every newly exposed byte, including
  reused cluster contents, before publishing the larger size.
- `pread`/`pwrite` must restore cursor state on success and failure; `pwrite`
  ignores `O_APPEND`, while ordinary append selects shared EOF and writes under
  the same serialized owner operation.

Required focused coverage before enabling the MountTable descriptor route:
independent append handles; `pwrite` on an append handle; exclusive create;
writable and read-only truncate; close/reopen and remount persistence; stale
pre-unmount handles; unlink-open-recreate cluster reuse; injected FAT and
directory-write failures; and sparse writes over non-zero recycled clusters.

No tests, builds, or runtime verification were run for this audit by explicit
instruction.
