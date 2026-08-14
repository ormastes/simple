# FAT32 database atomic replace and mount recovery are missing

- **Status:** open, release blocking for SimpleOS durable DB server
- **Owner:** filesystem atomic-replace/recovery owner
- **Observed:** `Fat32Filesystem.rename_at` links new then deletes old, rejects
  an existing destination, and explicitly disclaims pairwise atomicity.
  `Fat32Filesystem.mount`/`fat32_mount_publish` perform no journal recovery.
- **Impact:** canonical `std.database.atomic.atomic_write` cannot truthfully
  acknowledge a durable replacement on ARM QEMU or UNO Q FAT32 roots.  Device
  write/flush support alone is insufficient.
- **Required fix:** implement the provisioned dual-bank, checksummed,
  flush-ordered protocol in
  `doc/04_architecture/os/fat32_atomic_replace_recovery.md`, recover before
  mount publication, and expose its typed capability to
  `src/os/apps/servers_user/database_persistence_adapter.spl`.
- **Non-fixes:** relabeling `rename_at`, destination delete+rename, a lone
  marker file, close-as-sync, hosted fallback, or a reboot marker without a
  public-protocol read.
- **Closure evidence:** FAR-001..009 plus fresh-process QEMU power-cut/reboot
  matrix PASS; then equivalent physical UNO Q reboot evidence before the UNO
  cell may claim durable DB service.

## 2026-08-14 runtime-adapter progress (Codex)

Source wiring now reaches the filesystem protocol without changing the
canonical `DbServerCapsule`: the server store is `/SERVER.DB`,
`std.database.atomic` writes `/SERVER.TMP`, requires a successful
`rt_file_sync`, and only then invokes rename. The SimpleOS runtime supplies
exclusive create, bounded clock/sleep/task-liveness locking, path sync through
syscall 78, and rename ownership as the typed
`rt_simpleos_file_atomic_caps` bit set. The adapter intersects those bits with
`RecoverableReplaceV1`; it does not infer readiness from source presence or
ordinary FAT32 rename.

This resolves the runtime-adapter source gap only. The deployed self-hosted
test wrapper currently fails its bounded test-ABI probe, so compiled closure
and the required QEMU/physical reboot durability evidence remain pending. Keep
this record open until the original closure evidence above passes.
