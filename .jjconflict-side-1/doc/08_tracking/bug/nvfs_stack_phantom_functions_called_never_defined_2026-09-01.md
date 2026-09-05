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
| 4 | `vfs_state_mount_table_lease_restore_ready_v1` | 1 | nowhere | **FIXED** |
| 7 | `boot_nvfs_root_mount_transaction_v1` CALLED WITH NO IMPORT | 1 | its own file | **OPEN — see below** |
| 8 | `nvfs_posix_pread_bytes_owned` | 1 | nowhere | **OPEN** |
| 9 | the whole MountTable **mount-seal API**, DBFS *and* NVFS | 12+ | nowhere | **OPEN — the real blocker** |
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


---

# RE-MEASURED 2026-09-01 (later session) — items 4, 7, 8, 9

## Item 4 is FIXED, and it was never the blocker

`vfs_state_mount_table_lease_restore_ready_v1` is now implemented in
`src/os/services/vfs/vfs_boot_state.spl`, next to its plain-restore sibling. It
restores the lease AND publishes readiness under ONE uninterrupted lock hold —
which is what the transaction file's own header ("Commit restores the table and
readiness under one lock") always specified, and is the "restore counterpart"
the previous session correctly refused to fake by setting `g_vfs_initialized`
from the transaction. Validation, ordering and quarantine behaviour are byte-for
-byte the plain restore's; readiness is written only after the table value is
back, so a rejected restore can never leave the VFS marked ready. It also
publishes the same handoff identity the FAT32 path does
(`provider="simple-driver"`, `pure_simple=true`), because
`vfs_boot_storage_acceptance_reason` hard-rejects any other provider string.

**But fixing it moved no rung**, and the reason overturns this record's central
claim.

## L4 and L5 WERE NEVER GREEN — they were manufactured by a fabricated stub

`boot_fs_mount.spl` **calls `boot_nvfs_root_mount_transaction_v1` at line 209
with no `use` import for it.** Line 15 mentions the module in a comment; there
was no import statement. Under `SIMPLE_ALLOW_FREESTANDING_STUBS=1` the linker
therefore fabricated a weak body returning 0, and the build log said so
out loud, in the list this record never enumerated:

    FABRICATED-NEW simpleos_nvfsrt_uefi.elf boot_nvfs_root_mount_transaction_v1

A weak body returning 0 reads as a **non-error Result**. So
`boot_fs_mount_nvfs_from_lease_device` took the success branch — set
`_fs_mount_done = true`, set `_fs_mount_type = FsMountType.Nvfs`, and printed

    [boot-fs-mount] NVFS filesystem mounted through canonical VFS root

— while **nothing was staged, routed or committed at all**. No NVFS driver was
opened, `vfs_nvfs_root_mount_stage_v1` never ran, and
`vfs_nvfs_root_mount_commit_v1` never ran, which is the actual reason readiness
was never published and `vfs_is_ready()` was false after an apparently
successful mount. Item 4 was a symptom of item 7, not a peer of it.

This record's line "That is an NVFS volume genuinely mounted in-guest at '/'
through `boot_nvfs_root_mount_transaction_v1` / `vfs_nvfs_root_mount_commit_v1`"
is therefore **false**, and so is "L1-L5 are green". L1-L3 are real. **L4 and L5
are fabricated evidence** — exactly the failure mode the nonce discipline was
built to prevent, which slipped through because the fs-type rung distinguishes
NVFS from the DBFS/FAT32 *fallbacks* but cannot distinguish a real mount from a
stub that returns 0.

## Adding the missing import unmasks item 9: the mount-seal API does not exist

With `use os.kernel.boot.nvfs_root_mount_transaction.{...}` added, the module is
finally compiled instead of stubbed, and the build fails honestly:

    FAILED FILES (1):
      - src/os/services/vfs/vfs_nvfs_root_transaction.spl: hir: Unsupported
        feature: cannot infer field type while lowering
        vfs_nvfs_root_mount_stage_v1: struct 'ANY' field
        'backing_instance_identity'

The field is `ANY` because the method producing it does not exist. A census of
`src/**` finds **the entire MountTable mount-seal API undefined** — not the NVFS
half, the whole thing:

| symbol | definitions in `src/` |
|---|---|
| `NvfsRootMountSealV1` (struct) | 0 |
| `DbfsRootMountSealV1` / `DbfsRootMountSealInfoV1` | 0 |
| `StableFileSnapshotSealV1` | 0 |
| `ExecutableAuthorityRegistryV1` / `ExecutePathOpenV1` | 0 |
| `MountTable.acquire_nvfs_root_mount_seal` | 0 |
| `MountTable.revalidate_nvfs_root_mount_seal` | 0 |
| `MountTable.close_nvfs_root_mount_seal` | 0 |
| `MountTable.abort_nvfs_root_mount_seal` | 0 |
| `MountTable.remove_exact_nvfs_root_mount` | 0 |

`src/lib/nogc_async_mut/fs_driver/mount_table.spl` and its `_support` sibling
contain **zero occurrences of the string "seal"**. All six types are `use`-
imported from `std.fs_driver.mount_table`, which defines none of them.

So `vfs_nvfs_root_transaction.spl` — the file this record treated as working
product code — has never compiled, and cannot until that subsystem is written.
The DBFS root transaction (`vfs_dbfs_root_transaction.spl`) rests on the same
missing API, so this is not NVFS-specific.

## Item 8, which will block L8 even after item 9

`nvfs_posix_pread_bytes_owned` is imported at `vfs_init.spl:63` from
`std.fs_driver.nvfs_posix_driver` and called at `:187`. That module defines
`nvfs_posix_read_owned` and `nvfs_posix_write_owned` and **no pread**. It is a
byte-returning pread (`(driver, handle, offset, size) -> (driver,
Result<[u8], FsError>)`), deliberately distinct from the buf-filling
`read_owned`. It sits on the `g_root_nvfs_hosted` read path, which is nil in
this lane, so it is not the current blocker — but it is a real phantom.

## Honest verdict, this session

    FAIL — 10 check(s) checked, missing: L6 L7 L8 L9 L10   (exit 1)

unchanged as a rung count — but L4/L5 are now known to be stub-manufactured, so
the true standing is **L1-L3 real, L4-L10 not demonstrated**. With the import
added the lane instead reports, correctly:

    ERROR — nothing was checked: kernel build produced no
    build/os/simpleos_nvfsrt_uefi.elf: Build failed: native-build aborted:
    1 file(s) failed to compile   (exit 2)

## What closing this actually requires, in order

1. **Implement the MountTable mount-seal subsystem** (item 9) — the six types
   and the acquire/revalidate/close/abort/remove-exact methods, for DBFS and
   NVFS. This is new subsystem work, not the completion of a lease API, and it
   encodes a concurrency protocol (epoch + exact-backing-instance identity)
   that the call sites specify but no implementation exists for.
2. **Land the missing import** (item 7) together with step 1 — alone it breaks
   every build that reaches `boot_fs_mount`, so the two must land as one change.
   It was deliberately NOT landed in this session's commit for that reason: with
   the seal API still missing it turns a silently-wrong NVFS mount into a hard
   build failure for every lane that compiles `boot_fs_mount`, which would
   regress work outside this lane. The exact patch, verified to produce the
   honest ERROR verdict quoted above, is one line after the
   `fat32_boot_capsule_binding_owner_v1` import in
   `src/os/kernel/boot/boot_fs_mount.spl`:

       use os.kernel.boot.nvfs_root_mount_transaction.{boot_nvfs_root_mount_transaction_v1}

   Verified this session: with the import present the FAT32 lane
   (`check-simpleos-vfs-server-roundtrip-ovmf.shs`) still passes 8/8, so the
   breakage is confined to lanes that compile the NVFS mount path.
3. Implement `nvfs_posix_pread_bytes_owned` (item 8) before expecting L8.
4. Only then re-measure L6-L10.

## Gate hardening this incident argues for

The lane's rungs cannot currently tell a real mount from a stub returning 0. A
rung asserting that no load-bearing NVFS symbol appears in the build's
`FABRICATED-NEW` list would have caught item 7 on day one, and would have
prevented this record from asserting a green L4/L5. Do NOT baseline the 77
fabricated stubs to silence the warning — that converts the only surviving
signal into noise.
