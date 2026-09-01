# NVFS stack: a family of functions that are CALLED and never DEFINED (2026-09-01)

## Summary

Bringing up an NVFS server round-trip lane (`scripts/check/check-simpleos-nvfs-server-roundtrip-ovmf.shs`,
the analogue of the green FAT32 lane) surfaced **four** functions that are
imported and called from product code and **defined nowhere in the tree**, plus
one real logic bug. Under `SIMPLE_ALLOW_FREESTANDING_STUBS=1` — which the FAT32
lane sets too, and which is NOT the forbidden `SIMPLE_ALLOW_STUB_FALLBACK` —
the native build *fabricates* these as stubs. The kernel links cleanly, boots,
and silently does the wrong thing. The build log says so, but only in aggregate:

    WARNING: fabricated-stub baseline has NO rows for entry
    'simpleos_nvfsrt_uefi.elf'; 80 symbol(s) fabricated unmeasured.

This is the `unregistered_extern_silent_nil_2026-08-01` class, one layer up: not
an extern with no runtime backing, but a *Simple* function with no definition.

## Status

| # | symbol | call sites | defined | state |
|---|--------|-----------:|---------|-------|
| 1 | `DbFsInode.content_generation` never set on create/rebuild | 8 | n/a | **FIXED** |
| 2 | `DbFsDriver.pwrite_bytes_handle` | 5 | nowhere | **FIXED** |
| 3 | `boot_nvme_production_handoff_provision_bound` | 3 | nowhere | **FIXED** |
| 4 | `vfs_state_mount_table_lease_restore_ready_v1` | 1 | nowhere | **OPEN** |
| 5 | `NvfsHostedDriver.new_on_owned_device` / `.close_owned_device` / `.begin_owned_device_close` | 5 | nowhere | **OPEN** |
| 6 | `src/os/port/mkfs_nvfs.spl` is unrunnable | — | — | **OPEN** |

## Evidence

### 1-2. Device-backed DBFS/NVFS could not store a byte (FIXED)

Every file create AND every write on a device-backed DBFS/NVFS root returned
`FsError::InvalidArg`. `DbFsInode.content_generation` was never set at any of the
8 create-or-rebuild sites in `src/lib/nogc_sync_mut/db/dbfs_driver/namespace_io.spl`,
so it defaulted to `0`; `_valid_entry_shape()` in `device_commit_owner.spl`
rejects `content_generation == 0`, so `_encode_snapshot()` failed on every
mutation. Separately `pwrite_bytes_handle` was called from
`nvfs_driver.spl` (x2), `nvfs_posix_driver.spl`, `mount_table_support.spl` and
`dbfs_filesystem_ops.spl`, and defined nowhere — which is why
`src/os/port/nvfs_image.spl`, the NVFS image builder, could not produce an image
at all (`semantic: method pwrite_bytes_handle not found on type DbFsDriver`).

Measured host-side via the rust seed on a `MemBlockDevice`, at both the base-4
NVFS arena layout and base-0:

    before:            base=4 OPEN_PATH_ERR=FsError::InvalidArg   base=0 same
    after create fix:  base=4 OPEN_OK, WRITE_ERR=FsError::InvalidArg
    after both fixes:  base=4 WRITE_OK                            base=0 WRITE_OK
    after pwrite fix:  STAGE_OK provider=nvfs-dbfs-backed-v1, 4194304-byte image

### 3. The production storage handoff was never provisioned (FIXED)

`boot_nvme_production_handoff_provision_bound` was imported at 2 sites and called
at 3 — including `_vfs_boot_init_pure_nvme_fat32`, the sole publication point on
the production FAT32 boot path — and defined nowhere.
`boot_nvme_production_handoff_provision` (the unbound variant, the only writer of
that module's state) has **zero** callers. So
`boot_nvme_production_handoff_ready()` was false on every boot, and
`boot_fs_mount_freestanding_production()` — the entry `os_main` uses — always
refused. In-guest under real OVMF pflash -> GRUB-EFI -> multiboot:

    [vfs-init] pure-Simple NVMe lease device provisioned for production mount
    [nvfsrt] nvme bring-up ok=true
    [boot-fs-mount] production storage rejected: pure NVMe lease device not provisioned

i.e. the whole stack came up (BAR mapped, controller identified, namespace
8192x512, both queues created, bounce buffer allocated), the function was called
and returned, and the next line still said not provisioned.

After the fix, same lane, same firmware path:

    [boot-fs-mount] NVFS filesystem mounted through canonical VFS root
    [nvfsrt] production mount ok=true
    [nvfsrt] fs-type=nvfs

That is an NVFS volume genuinely mounted in-guest at "/" through
`boot_nvfs_root_mount_transaction_v1` / `vfs_nvfs_root_mount_commit_v1` — and
NOT via the DBFS or FAT32 fallback, which the lane's `fs-type` rung exists to
distinguish.

### 4. NVFS root readiness is never published (OPEN — the current blocker)

`vfs_state_mount_table_lease_restore_ready_v1` is imported and called at
`src/os/services/vfs/vfs_nvfs_root_transaction.spl:14,175` and defined nowhere.
It is the point at which a committed NVFS root is supposed to publish VFS
readiness. Because it is a fabricated stub, `g_vfs_initialized` is never set on
the NVFS path — its only writers are in `vfs_boot_state.spl`, all on FAT32/virtio
paths — so `vfs_is_ready()` stays false after a *successful* NVFS mount:

    [nvfsrt] production mount ok=true
    [nvfsrt] fs-type=nvfs
    [nvfsrt] PROBE FAILED: vfs not ready after NVFS root mount

The design is internally inconsistent, which is the cleanest statement of the
bug: `vfs_nvfs_root_mount_stage_v1` REFUSES to stage when `vfs_is_ready()` is
already true (`vfs-nvfs-root: root-already-ready`), so it treats that flag as
"the root is claimed" — yet commit never makes it true. Every `g_vfs_*` hub
request therefore continues to see an unready VFS on a correctly mounted NVFS
root.

Fixing this needs the MountTable lease-owner API surface
(`vfs_state_mount_table_owner_handle_v1` / `..._lease_begin_v1` and their
restore counterpart) to be completed, not just a flag set — writing
`g_vfs_initialized = true` from the transaction would paper over a missing lease
restore and is deliberately NOT done here.

### 5. The NVFS connector's owned-device path cannot compile (OPEN)

`src/os/services/vfs/nvfs_connector.spl:172,179,183,188,208` call
`NvfsHostedDriver.new_on_owned_device`, `.close_owned_device` and
`.begin_owned_device_close`. `NvfsHostedDriver` is `NvfsPosixDriver`, which has
`new_on_device` only. None of the three exists anywhere in `src/`. So
`nvfs_vfs_connect_owned_device` — the only connector entry that binds NVFS to a
real device — is dead. The unit spec
`test/01_unit/os/services/vfs/vfs_nvfs_connector_spec.spl` exercises only
`nvfs_vfs_connect`, the in-memory variant, so it stays green over the gap.

### 6. `src/os/port/mkfs_nvfs.spl` is unrunnable (OPEN)

Two independent faults: `fn main(args: [text])` is never supplied its argument by
the runner (`error: semantic: function expects argument for parameter 'args',
but none was provided`, with or without `--`), and `process` is unresolved in
codegen (`GlobalLoad: unresolved identifier 'process'`). The NVFS lane stages its
volume by calling `build_nvfs_rootfs_image` from a generated no-arg program
instead; `mkfs_nvfs.spl` itself has never been runnable.

## What the lane proves today

`scripts/check/check-simpleos-nvfs-server-roundtrip-ovmf.shs` is honestly RED at
`FAIL — 10 check(s) checked, missing: L6 L7 L8 L9 L10`. Green: L1 (OVMF ->
GRUB-EFI -> multiboot), L2 (guest entered carrying this run's nonce), L3
(pure-Simple NVMe lease device up), L4 (production mount took a root), L5 (that
root is NVFS, not a fallback). The remaining rungs are blocked on item 4 alone.

## Why the nonce discipline mattered

Every one of these defects is invisible to a link check and to a banner. The
per-run nonce plus the pre-boot absence assertions are what forced each failure
to surface as a specific missing rung instead of a plausible-looking boot.
