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
