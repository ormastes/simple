# FAT32 capsule sync retains a mount operation on terminal flush paths

**Status:** source fix and focused regression in early draft; runtime and QEMU verification pending.

**Owner:** `src/os/kernel/fs/fat32_fd_table.spl`, reached through the default
SOSIX FAT32 positioned backend (`src/os/sosix/fs/fat32_positioned_vfs_backend.spl`).

`_fat32_fd_sync_object` acquired a mount operation, then returned without
releasing it when the device flush acknowledged `true` or refused with
`Ok(false)`. The capsule mount owner has 64 operation slots; repeated sync
could exhaust those slots and prevent mount close. The flush `Err` path did
release the operation, but its result was not checked.

The candidate now releases exactly once after every completed device flush,
before selecting the sync result. A release failure fails closed with
`FAT32_FD_ENOSYS`. The existing metadata-write error path still releases
before returning. No extra retained state or per-sync scan is introduced.

Focused regression: `src/os/kernel/fs/test/fat32_capsule_mount_owner_v1_spec.spl`
uses an authenticated capsule and descriptor. It requests 65 syncs in each
of the acknowledged, refused, and failed-flush modes (beyond the 64-slot
capacity), checks the returned statuses, and requires mount close to report
195 released operations. This is a bounded-resource behavior check, not a
measured latency or RSS result.

## Verification TODO

- Run the focused `.spl` spec with a source-current, admitted pure-Simple
  runtime; record executable hash, mode, exit status, and scenario count.
- Run the SOSIX FAT32 positioned-I/O acceptance gate and the SimpleOS QEMU
  bootstrap once the Linux bootstrap/Phase2 runtime is admitted.
- Compare relevant sync throughput and peak RSS against an immutable
  baseline/candidate pair before claiming no measured performance regression.
