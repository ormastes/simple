# SimpleOS path-based POSIX syscalls: fake success replaced with honest ENOSYS; real FAT32 backend exists but is not wired to the syscall path

Status: PARTIALLY FIXED 2026-08-06 (honesty landed; end-to-end wiring open)

## Summary

`src/os/kernel/ipc/syscall_file.spl` handles the path-based POSIX syscalls
(`open`, `stat`, `mkdir`, `readdir`, `unlink`, `rename`, `rmdir`). Before this
change, each of these built an `IpcMessage` and fired it at port 0.
`IpcMessage` carries no payload pointer, `send()` queues an empty payload and
returns 0 immediately, and no reply was ever awaited. The result: the path
bytes never left the kernel, the caller's `struct stat*` / dirent buffers were
never written, and the syscall still reported success (0). `open`'s return
value in particular happened to look like a valid fd because it returned the
send() result (0) — colliding with fd 0 (stdin) — rather than a newly
allocated descriptor.

## Fix landed here

The fake IPC sends are removed. Each handler now range/pointer-validates its
arguments (as before) and returns `-ENOSYS` (-38) instead of a fabricated 0.
`open` in particular can never return 0 on this path, so a caller can no
longer have its writes silently redirected to the console. This is a pure
honesty fix: no caller behaviour is being "improved," a previously-silent
failure is now a loud, correctly-signalled one.

`read`/`write`/`close`/`lseek` were already real: they route through
`os.kernel.fd_io.{posix_read, posix_write, posix_close, posix_lseek}`, which
talk to the FD table and the active POSIX fd backend (serial/pipe/socket/file
routes). They are unaffected by this change and unaffected by the open/stat/
mkdir/readdir/unlink/rename/rmdir gap below, EXCEPT that nothing can now
allocate a *file*-backed fd through this path (see "Known gaps").

## What actually exists today (verified, not assumed)

`os.kernel.fs.fat32.Fat32Filesystem` (`src/os/kernel/fs/fat32.spl`) is a real,
freestanding-safe FAT32 driver operating directly on a `BlockDevice`:
`mount`, `open`, `read`, `stat`, `resolve_path`, `open_at`, `stat_at`,
`allocate_cluster`, `append_cluster`, `_update_dirent`, `write`, `create_at`,
`mkdir_at`, `flush`, `close`. It does real cluster allocation, real
directory-entry writing (8.3 + LFN), and real nested-path resolution.

Evidence this is real, not a shim: `test/01_unit/os/kernel/fs/fat32_subdir_spec.spl`
(17 examples) and `test/01_unit/os/kernel/fs/fat32_write_path_spec.spl`
(25 examples), 42/42 passing. Sabotage-verified during this change: stubbing
`mkdir_at` to `return Ok(())` (skipping all real work) turned 18 of the 25
`fat32_write_path_spec.spl` examples red — including "creates a directory
whose . and .. entries resolve on re-read", "nests directories two deep",
"refuses to create a directory that already exists", "grows the directory by
a cluster when an entry chain does not fit". Restoring the real implementation
returned it to 25/25. The suite is not vacuous.

## Known gaps — why the syscall handlers still return ENOSYS

1. **No kernel-global mounted `Fat32Filesystem`.** Every
   `Fat32Filesystem(...)` construction site in the tree is inside
   `fat32.spl` itself (its `impl` block's static constructors and its own
   specs) — `grep -rn "Fat32Filesystem(" src/os/` proves it. No boot path
   ever constructs one and stores it as persistent state the way
   `g_cwd_table` does for cwd. `syscall_file.spl` therefore has a real
   `mkdir_at`/`stat`/`open_at`/`create_at` to call but no filesystem instance
   to call it on.
2. **The hosted VFS layer (`os.services.vfs`) is a dead end for this module.**
   `os.services.vfs.vfs_init` / `vfs_dispatch` do have real dispatch
   (`g_vfs_file_size`, `g_vfs_read_file_bytes`, and DriverInstance-level
   `write_file_bytes`/`delete_file`/`file_exists`), and `boot_fs.spl` (the
   *hosted* boot sequence, used to load `/sbin/init`) does call them. But
   `boot_fs_mount.spl`'s own header explicitly forbids importing
   `os.services.vfs.vfs_init` from the freestanding boundary, and
   `syscall_file.spl` lives in that freestanding boundary (it only imports
   `os.kernel.*`). Wiring `os.services.vfs` in here would cross an
   architectural line the codebase already draws on purpose.
3. **`posix_open` in `fd_io.spl` is a separate, already-dead path**, not an
   alternative fix. It builds a real IPC payload and sends it to a "VFS
   service" at port 1 (`VFS_OPEN`), then blocks on a reply. But
   `src/os/kernel/boot/init_services.spl:125` documents that this service is
   never spawned in production ("In a full system this would be
   `spawn_task(vfs_service_start)` ... the caller can invoke
   `vfs_service_start()` when ready to block"). Routing `_handle_file_open`
   through `posix_open` today would not fake success — it would hang the
   calling task forever waiting on a reply nobody sends. ENOSYS is the
   correct current answer, not a workaround.
4. **`readdir`, `unlink`, `rename`, `rmdir` have no primitive at any layer.**
   `Fat32Filesystem` does not implement them yet (`grep -n "fn.*unlink\|fn.*rmdir\|fn.*rename\|fn.*readdir" src/os/kernel/fs/fat32.spl` is empty).

## Required next step (for the next lane)

Mount a `Fat32Filesystem` into freestanding kernel-global state during boot
(mirroring the `g_cwd_table` lazy-init pattern in `syscall_file.spl`), expose
an accessor, and have `_handle_file_stat` / `_handle_file_mkdir` /
`_handle_file_open` (via `open_at`/`create_at`) call it directly instead of
returning ENOSYS. Map the returned `FileHandle` to a POSIX fd through the
existing fd table (`os.kernel.fd_table`) so `read`/`write`/`close` keep
working unchanged. `readdir`/`unlink`/`rename`/`rmdir` need new
`Fat32Filesystem` methods before they can move off ENOSYS at all.

## Related, separately-landed honesty fixes in this same change

- `src/os/libc/simpleos_posix_ext.c`: added real `pread`/`pwrite` (seek+io,
  with a stated non-atomicity caveat) and honest `fsync`/`fdatasync`
  returning `ENOSYS` rather than falsely claiming durability — traced end to
  end to two real gaps (FAT32 size-writeback and unreachable NVMe FLUSH).
- See also `doc/08_tracking/bug/simpleos_fs_stream_ops_lack_host_fallback_2026-08-06.md`
  for a distinct, already-filed bug about the FILE-stream layer
  (`fopen`/`fread`/`fwrite`) bypassing the host-fallback dispatch — different
  functions, different root cause, not fixed by this change.
