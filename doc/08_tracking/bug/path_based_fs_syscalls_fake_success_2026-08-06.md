# SimpleOS path-based POSIX syscalls: fake success replaced with honest ENOSYS; real FAT32 backend exists but is not wired to the syscall path

Status: PARTIALLY FIXED 2026-08-06 (honesty landed 2026-08-06 AM; kernel-global
mount + open/stat/mkdir/readdir/unlink/rmdir wiring landed 2026-08-06 PM;
boot-reachability and read/write-after-open still open — see "Update 2" below)

## Update 2 (2026-08-06, this lane): kernel-global mount + six handlers wired for real

Implemented exactly the "Required next step" this doc specified, plus the two
directory-removal primitives it flagged as missing at every layer:

**`src/os/kernel/fs/fat32.spl`**
- New kernel-global mount state, mirroring the `g_cwd_table` lazy-scalar
  pattern in `syscall_file.spl` and the `vmm_publish_kernel_pml4` pattern in
  `vmm_core.spl`: `fat32_mount_publish(fs, dev)`, `fat32_mount_ready()`,
  `fat32_mount_fs()`, `fat32_mount_dev()`, `fat32_mount_clear()` (test-only).
  `Fat32Filesystem`/`BlockDevice` are reference types, so the `Option`-typed
  globals hold a plain nullable pointer — the codegen landmine about
  `Option<struct>` reading nil on the hit path does not apply here, and no
  `if val` binding-if is used on them regardless.
- New `Fat32Filesystem.readdir_at(dev, path)` — enumerates a directory's live
  entries (root or nested), reusing the same LFN-accumulation / 8.3-decode
  logic `fat32_dir_find_entry` already had (factored into a new free function
  `fat32_dir_list_entries`).
- New `Fat32Filesystem.unlink_at(dev, path)` — frees the file's whole FAT
  cluster chain via the existing `read_cluster_chain`/`_write_fat_entry`
  primitives, then marks the 32-byte dirent's first byte `0xE5` via a new
  `_mark_dirent_deleted` helper (same root_dir_data cache-sync guard
  `_update_dirent` already used). Refuses a directory with `EISDIR` (new
  const, `-21`).
- New `Fat32Filesystem.rmdir_at(dev, path)` — same free+mark-deleted shape,
  gated on the directory holding only `.`/`..` (`ENOTEMPTY`, new const `-39`),
  `ENOTDIR` on a file.
- `rename_at` was NOT added — see "What's still ENOSYS" below.

**`src/os/kernel/boot/boot_fs_mount.spl`**
- `boot_fs_mount_fat32_from_device` now does more than validate the BPB: on a
  successful `parse_bpb`, it constructs a `Fat32Filesystem`, calls
  `.mount(dev)`, and on success calls `fat32_mount_publish(fs, dev)`. A
  `mount()` failure after a valid BPB now returns `Err(...)` instead of
  reporting mounted.

**`src/os/kernel/ipc/syscall_file.spl`** — six handlers went from
unconditional `-ENOSYS` to real:
- `_handle_file_open` — resolves the path against cwd, calls
  `Fat32Filesystem.open_at` (falling back to `create_at` on `ENOENT` when
  `O_CREAT` is set), allocates a real fd via `os.kernel.fd_table.fd_alloc`/
  `fd_set`. Never returns 0 on this path (no stdin collision).
- `_handle_file_stat` — calls `stat_at`, builds a real `struct stat` byte
  image (mode/nlink/size/mtime at the offsets documented in
  `src/os/libc/include/sys/stat.h`'s x86_64 natural-alignment layout: mode
  `u32@16`, nlink `u64@24`, size `i64@48`, mtime `i64@80`, 96 bytes total),
  writes it via `mmio_write8` per byte — the same primitive `_handle_getcwd`
  already used for a userspace write.
- `_handle_file_mkdir` — calls `mkdir_at`.
- `_handle_file_readdir` — arg layout grew a path-length slot (`arg0`=path
  ptr, `arg1`=path len, `arg2`=buf ptr, `arg3`=buf size — the original
  IPC-stub signature never needed a path length since it never copied path
  bytes). Calls `readdir_at`, encodes names as NUL-terminated runs, writes
  them into the caller buffer, returns the entry count. Returns `-ERANGE`
  rather than silently truncating when the encoding doesn't fit.
- `_handle_file_unlink` — calls `unlink_at`.
- `_handle_file_rmdir` — calls `rmdir_at`.

All six are gated on `fat32_mount_ready()` and return `-ENOSYS` — never a
fabricated success — when nothing has published a mount yet.

**Tests:** `test/01_unit/os/kernel/fs/fat32_mount_and_dir_ops_spec.spl` (new,
8/8 passing) covers the mount-publish accessors and the three new
`Fat32Filesystem` methods end to end against a synthetic in-memory FAT32
volume (same `MockDev` shape `fat32_write_path_spec.spl` established),
including negative paths (ENOENT after unlink, ENOTEMPTY on a non-empty
rmdir, EISDIR unlinking a directory, ENOTDIR on both readdir and rmdir of a
file) and a re-read-through-a-fresh-view discipline so a cache-only mutation
cannot pass. **Sabotage-verified this session:** stubbing `unlink_at` to
`return Ok(())` before doing any real work dropped the suite to 7/8
(the "fresh stat_at reports ENOENT" example went red); disabling `rmdir_at`'s
`ENOTEMPTY` check (`... and false`) also dropped it to 7/8 (the
non-empty-directory example went red). Both restored to 8/8. Existing
`fat32_write_path_spec.spl` (25/25) and `fat32_subdir_spec.spl` (17/17) still
pass unmodified — no regression in the primitives this change reuses.

## Why this doc does NOT claim `_handle_file_*` were exercised through the syscall layer dynamically

Attempted first: a spec importing `os.kernel.ipc.syscall_file` and driving
`_handle_file_open`/`_handle_file_stat`/etc. directly, using the exact
`pmm_alloc_page_raw` + `vmm_map_page` + `mmio_write8`/`mmio_read8` userspace-page
recipe `test/01_unit/os/kernel/ipc/syscall_spec.spl` already established for
other syscall handlers. It failed with `error: test-runner: no examples
executed`. Before concluding this was caused by the change in this lane, the
EXISTING, completely unmodified `syscall_spec.spl` was run against the same
deployed `bin/simple` (confirmed via `readlink -f bin/simple` to be the
bootstrap-seed binary, not the self-hosted one) and produced the IDENTICAL
`error: test-runner: no examples executed` / `1 total, 0 passed, 1 failed`.
A rerun of `syscall_spec.spl` AFTER this lane's `syscall_file.spl` edits
produced the byte-identical failure (same line position in the log), i.e. no
new/different failure was introduced. Meanwhile `fat32_write_path_spec.spl`
(no `os.kernel.ipc.*`/scheduler/vmm/pmm import) passed 25/25 on the exact same
binary. Conclusion: this is a pre-existing seed/harness limitation specific to
specs that pull in the full scheduler/vmm/pmm/ipc/syscall dependency graph,
not something this change caused or can fix within its own scope. The new
`_handle_file_*` bodies were verified by careful code review and by testing
every `Fat32Filesystem` primitive they call in isolation instead (see Tests
above) — a materially weaker guarantee than a dynamic syscall-layer test would
have been, stated here rather than glossed over.

## Wall discovered this lane: a fd from `_handle_file_open` does not make `read`/`write` reach FAT32

`_handle_file_open` allocates a real fd typed `FD_TYPE_FILE` (same type byte
`fd_io.spl` uses for the read/write routing table). But
`fd_io.posix_read`/`posix_write` route `FD_TYPE_FILE` through
`os.kernel.async_io_rw.sync_read`/`sync_write`, which call
`sosix_sync_read`/`sosix_sync_write` — a wholly separate subsystem from
`Fat32Filesystem`, unrelated to the mount published by this change. So: `open`
on a FAT32 path now does real disk I/O (path resolution, `open_at`/`create_at`,
fd allocation) and `stat`/`mkdir`/`readdir`/`unlink`/`rmdir` are fully real,
but a subsequent `read()`/`write()` syscall on the fd `open` returned will NOT
reach the FAT32 driver until `sosix_sync_read`/`sosix_sync_write` (or the
`FD_IO_ROUTE_FILE` dispatch ahead of them) is taught about the FAT32 backend.
This is a genuinely separate integration gap from the one this doc originally
tracked (that one was "no reachable Fat32Filesystem instance"; this one is
"two unrelated file-fd subsystems coexist under the same `FD_TYPE_FILE` tag").
Not fixed here — flagged so it isn't silently assumed solved.

## Wall discovered this lane: `boot_fs_mount_fat32_from_device` has no caller in the live boot sequence

`grep -rn boot_fs_mount_fat32_from_device src/os/` outside `boot_fs_mount.spl`
itself is empty — nothing in the real boot path calls it. This means the
`fat32_mount_publish` call added to it in this lane, while correct and now the
designated hook, is not YET reachable on real hardware/QEMU: on boot, nothing
publishes a mount, so `fat32_mount_ready()` stays false and all six wired
handlers correctly (honestly) return `-ENOSYS`, never a fake success. Wiring
something in the live boot sequence to call `boot_fs_mount_fat32_from_device`
(or `fat32_mount_publish` directly) with a real disk `BlockDevice` is the next
required step before these handlers do anything on the dev board. This gap
pre-dates this lane (`boot_fs_mount.spl`'s own module docstring already
describes itself as "the production boundary" without describing who crosses
it) and was not introduced or closed here — board-runnable rule requires
saying so explicitly rather than leaving it implicit.

## `rename` deliberately left ENOSYS

Unlike unlink/rmdir (mark-deleted — a single-byte dirent patch reusing
existing `_link_entry`/`resolve_path` machinery) or readdir (pure read
enumeration), a real rename must rewrite a directory entry's LFN + 8.3 slots
IN PLACE while preserving `start_cluster` and size. `Fat32Filesystem` has no
primitive for that — `_link_entry` only APPENDS new slots; nothing edits or
relocates an existing one. Fabricating rename as "create the new name, delete
the old" would be observably wrong the moment either half fails partway (a
caller could end up with both names or neither, where POSIX guarantees
atomicity). Left as `-ENOSYS` in `_handle_file_rename` rather than a fake or
partially-correct implementation.

## Original report (2026-08-06 AM), preserved below

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

## Required next step (for the next lane) — DONE 2026-08-06 (this lane), see "Update 2" above

~~Mount a `Fat32Filesystem` into freestanding kernel-global state during boot
(mirroring the `g_cwd_table` lazy-init pattern in `syscall_file.spl`), expose
an accessor, and have `_handle_file_stat` / `_handle_file_mkdir` /
`_handle_file_open` (via `open_at`/`create_at`) call it directly instead of
returning ENOSYS. Map the returned `FileHandle` to a POSIX fd through the
existing fd table (`os.kernel.fd_table`) so `read`/`write`/`close` keep
working unchanged. `readdir`/`unlink`/`rename`/`rmdir` need new
`Fat32Filesystem` methods before they can move off ENOSYS at all.~~ All of
this landed except `rename` (deliberately, see above) and the fd
read/write-after-open connection (a separate, newly-discovered gap, see
above) — the fd this lane's `open` allocates is real but `read`/`write` on it
still don't reach FAT32. The NEW required next steps are the two walls
documented above: (1) wire something in the live boot sequence to actually
call `boot_fs_mount_fat32_from_device`/`fat32_mount_publish`, and (2) teach
`fd_io.spl`'s `FD_TYPE_FILE` read/write route (or `sosix_sync_read`/
`sosix_sync_write`) about the FAT32 backend.

## Related, separately-landed honesty fixes in this same change

- `src/os/libc/simpleos_posix_ext.c`: added real `pread`/`pwrite` (seek+io,
  with a stated non-atomicity caveat) and honest `fsync`/`fdatasync`
  returning `ENOSYS` rather than falsely claiming durability — traced end to
  end to two real gaps (FAT32 size-writeback and unreachable NVMe FLUSH).
- See also `doc/08_tracking/bug/simpleos_fs_stream_ops_lack_host_fallback_2026-08-06.md`
  for a distinct, already-filed bug about the FILE-stream layer
  (`fopen`/`fread`/`fwrite`) bypassing the host-fallback dispatch — different
  functions, different root cause, not fixed by this change.
