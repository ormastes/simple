# Lane P3 — VFS unify (SimpleOS production harden)

Status: **increment 1 landed in working copy (uncommitted)**
Date: 2026-07-27
Plan row: `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md` line 34
Master plan: `doc/01_research/domain/simpleos_production_host_master_plan.md` §8 / §24.9

## Goal

One mount namespace + one open-file-description path. Convert the old
`VfsManager` and the direct FAT32 callers into shims with recorded deletion
conditions. Gate: all FS specs green through the single path.

## Increment 1 — what was done

Introduced the **handle to mount association** primitive and its contract spec.

- `src/os/kernel/fs/vfs_handle_table.spl` (NEW, 167 lines)
  `VfsHandleTable`: `register(mount_index, mount_path, driver_handle) -> u64`
  issuing globally unique VFS handles; `lookup/is_open/mount_index_of/
  mount_path_of/driver_handle_of/open_count`; `release`, `release_mount`
  (unmount drops its handles), `reindex_after_unmount` (mount vector renumber
  after `mounts.remove(i)`). Sized `VfsHandleLookup` result — no optional
  unwrap on the kernel path. Constant `VFS_HANDLE_NO_MOUNT = -1`.
- `test/01_unit/os/kernel/fs/handle_mount_association_spec.spl` (NEW)
  Two mock drivers, each with a private handle namespace starting at 1, so
  both issue driver handle `1`. Absolute oracle: each driver stamps its own
  name onto returned content (`winfs:beta-payload` vs `rootfs:alpha-payload`),
  so no assertion compares a value to itself.

### Spec verdict

```
timeout 240 /tmp/p3lane/bin/p3job run test/01_unit/os/kernel/fs/handle_mount_association_spec.spl
7 examples, 0 failures
```

Fail-once proof: replacing the `lookup` match condition with `if true`
(always return entry 0) produced `7 examples, 5 failures` — including
`expected rootfs:alpha-payload to equal winfs:beta-payload`. Source restored,
re-run green. Duplicate-owner guard re-run: `4 examples, 0 failures` +
`1 example, 0 failures` (no `*_v2.spl` / `new_vfs` name introduced).

Binary used: `bin/release/x86_64-unknown-linux-gnu/simple` copied to
`/tmp/p3lane/bin/p3job` (deployed `bin/simple` is a stale seed whose
`simple test` hangs).

Lint note (pre-existing tool defect, not lane code): `simple lint` on the new
module ends with `error: semantic: method get not found on type str (receiver
value: VfsHandleEntry)`. The untouched control file
`src/os/kernel/fs/win_vfs/win_vfs_mount.spl` produces the identical error with
its own class name substituted (`... receiver value: RegisterStatus`), so the
linter — not the source — is at fault. Worth a separate bug in the tooling lane.

## Phase-0 truth data — duplicate filesystem stacks

### Stack 1 — `Filesystem` trait + `VfsManager` (OS VFS service, u64 handles)

Owner files (`src/os/services/vfs/`, 8021 lines total):
`vfs.spl` (442, trait + VfsManager), `vfs_service.spl` (550),
`vfs_init.spl` (697), `vfs_boot_init.spl` (2199), `vfs_dispatch.spl` (461),
`vfs_write_ops.spl` (388), `vfs_async.spl` (154),
`vfs_block_adapters.spl` (702), `block_cache.spl` (257),
`nvfs_connector.spl` (250), `nvme_filesystem_mounts.spl` (142),
`pseudofs_mount.spl` (42), `q35_pure_nvme_perf_boot.spl` (633),
`arm_fs_exec_vfs.spl` (554), `arm_fs_exec_dirent.spl` (283),
`arm_fs_exec_alias.spl` (159), `c_nvme_block_adapter.spl` (62),
`riscv64_virtio_blk_adapter.spl` (37), `mod.spl` (9).

**66 files reference `VfsManager`** — 40 of them are `src/os/tools/shell/*`
tool binaries, 12 are `src/os/apps/{shell,file_explorer}`, the rest are
services (`devfs_filesystem`, `procfs_filesystem`, `dbfs_filesystem_ops`,
`llm/_McpOsServer/*`), `src/os/kernel/boot/boot_fs.spl` and
`src/os/kernel/fs/win_vfs/*`.

### Stack 2 — `FsDriver` / `MountTable` (stdlib tier, `FileHandle`/`DirHandle`)

`src/lib/nogc_sync_mut/fs_driver/` (28 files): `mount_table.spl`,
`instance.spl`, `ops.spl`, `extension.spl`, `types.spl`, `error.spl`,
`capability.spl`, `handle_guard.spl`, `direct_io.spl`, `driver_adapter.spl`,
`block_device.spl`, `mem_block_device.spl`, `ramfs.spl`, `nvfs_driver.spl`,
`nvfs_hosted_driver.spl`, `nvfs_posix_driver.spl`, `nvfs_arena.spl`,
`nvfs_superblock.spl`, `fat32_core.spl`, `fat32_cache.spl`,
`fat32_dir_ops.spl`, `fat32_parsers.spl`, `fat32_hardening.spl`,
`fat32_stub.spl`, `fat32_test_device.spl`, `fs_bench_harness.spl`,
`bytes_util.spl`, `__init__.spl`.
Mirrored (near-duplicate) trees exist at
`src/lib/nogc_async_mut/fs_driver/` (6 files) and the `db/dbfs_*` variants in
all three tiers. **39 files under `src/os/` reference this stack**, notably
`src/os/services/nvfs/**` (14), `src/os/services/vfs/**` (7 — the two stacks
are already spliced together inside the VFS service directory),
`src/os/kernel/boot/boot_fs*.spl`, `src/os/kernel/memory/memory_swap_*.spl`,
`src/os/drivers/usb/usb_msc.spl`, `src/os/port/*`.

### Stack 3 — direct FAT32

`src/os/kernel/fs/fat32.spl` (37 KB, `Fat32Filesystem`, own `FileHandle`,
`open/read/write/close` taking an explicit `BlockDevice`).
Direct callers outside the driver itself: `src/os/kernel/boot/boot_fs_mount.spl`,
`src/os/services/vfs/vfs_init.spl`, `src/os/services/vfs/vfs_write_ops.spl`,
`src/os/services/vfs/vfs_boot_init.spl`, plus
`src/os/services/fat32/shared_fat32_driver.spl`.
A *fourth* FAT32 implementation lives in stack 2
(`src/lib/nogc_sync_mut/fs_driver/fat32_core.spl` + 5 siblings).

## Callers that still bypass the mount table

1. **`VfsManager` itself — the "use first mount" defect.**
   `src/os/services/vfs/vfs.spl`: `write` L233-247, `close` L298-303,
   `read` L305-310, `seek` L312-317 all do `val mount = self.mounts[0]`.
   The source comment at L239-241 states the intent: *"A full implementation
   would maintain a handle-to-mount mapping."*
   `src/os/services/vfs/vfs_service.spl` repeats it at L212, L228, L238, L406.
   Consequence: with `/` and `/win` both mounted, both drivers issue handle 1
   and every read/write on the `/win` file hits the `/` driver.
2. **Stack 2's probe fallback.** `mount_table.spl` *does* carry an
   association (`OpenFileBinding` / `OpenDirBinding` = `mount_id` +
   `inner_handle`, `_file_binding` L274, `_dir_binding` L282), but every
   handle op falls through to a *try each mount in order, first Ok wins* loop
   (e.g. `read` L506-511, `readdir` L487-492, `close` L610-615, plus
   `write/pwrite/pread`). For an unbound handle that is the mounts[0] bug with
   extra steps, and it can silently succeed against the wrong filesystem.
3. **Direct FAT32 callers** (list above) hold a `Fat32Filesystem` + a
   `BlockDevice` and never consult any mount table.
4. **66 `VfsManager` consumers** (40 shell tools, 12 app files) call the
   path-based convenience methods, so they inherit whatever routing
   `VfsManager` does — they are not independent bypasses, but they are the
   blast radius of the fix and the reason the shim must keep the current
   signatures.

## BLOCKER — lane path ownership does not cover the defect

The plan grants P3 `src/os/kernel/fs/**` + `test/os/kernel/fs/**`, but
`src/os/kernel/fs/` contains only `fat32.spl` and `win_vfs/`. **The VFS the
lane exists to unify lives in `src/os/services/vfs/**`, which no lane in the
plan claims** (P4 owns `src/os/apps/**`). The mounts[0] fix therefore could
not be wired this increment — `vfs_handle_table.spl` is currently a tested
but unwired primitive.

Ask: extend lane P3's exclusive paths to `src/os/services/vfs/**` (and
`src/os/services/fat32/**`), or reassign that directory. Until then increment
2 cannot land.

## Resume plan

1. **(needs path grant)** Wire `VfsHandleTable` into `VfsManager`: add field
   `handles: VfsHandleTable`; `open()` registers `(mount_index, mount_path,
   driver_handle)` and returns the VFS handle in `FileDescriptor.node`;
   `read/write/close/seek` replace `self.mounts[0]` with
   `self.handles.lookup(handle)` → `self.mounts[look.mount_index].fs.<op>(
   look.driver_handle, ...)`, returning `Err("bad file descriptor")` on
   `found: false`; `close` calls `release`; `unmount` calls `release_mount`
   then `reindex_after_unmount`. Same four call sites in `vfs_service.spl`.
   `resolve_mount` must return the index alongside the entry (today it returns
   only `VfsMountEntry?`) — smallest change is a sized
   `ResolvedMount(found, index, entry)`.
2. Promote the spec to drive real `VfsManager` + two real drivers
   (`WinVfsDriver` at `/win`, ramfs at `/`), keeping the driver-name oracle.
3. Decide the convergence target before writing more association code:
   stack 2's `OpenFileBinding` is the same concept as `VfsHandleTable`. Either
   `VfsHandleTable` becomes the one implementation and `mount_table.spl`'s
   binding is retired, or the reverse — **do not leave both**. Whichever wins
   must also delete stack 2's probe-every-mount fallback, which is the same
   defect class.
4. Delete-condition list for the shims (for `production_status.sdn`):
   - `Filesystem` trait shim deletable once all 66 `VfsManager` consumers call
     the unified path.
   - `src/os/kernel/fs/fat32.spl` deletable once
     `src/lib/nogc_sync_mut/fs_driver/fat32_core.spl` covers boot_fs_mount +
     vfs_init/vfs_write_ops/vfs_boot_init, or vice versa — one FAT32 only.
   - `nogc_async_mut/fs_driver/` mirror deletable once the tier split is
     resolved.
5. Board-runnable check outstanding: the QEMU FS specs must be re-run on the
   real board path once increment 2 lands (per `.claude/rules/board-runnable.md`).

## Files changed this increment

- `src/os/kernel/fs/vfs_handle_table.spl` (new)
- `test/01_unit/os/kernel/fs/handle_mount_association_spec.spl` (new)
- `.spipe/simpleos_harden_p3_vfs/state.md` (new)

Nothing committed — changes left in the working copy per lane instruction.
