# The share-history merge landed NVFS consumers without their API, and a weak stub hid it

- Date: 2026-09-01
- Status: FIXED (the missing definitions), with a follow-on blocker filed separately
- Commits that caused it: `e274cd33719` / `a8244005f9b` (`chore: merge all share-history
  worktree branches into main`), `e9da588ee61` / `2760e54e3de`
  (`fix(merge): repair 1136 unparseable .spl files from the share-history merge`)

## What happened

The merge took the NVFS root-transaction **consumers** from one side:

- `src/os/kernel/boot/nvfs_root_mount_transaction.spl`
- `src/os/services/vfs/vfs_nvfs_root_transaction.spl`
- `src/os/services/vfs/vfs_boot_state.spl` (its `DbfsRootMountSealV1` import, line 42)
- `src/os/kernel/abi/syscall_shim_positioned.spl`

and `src/lib/nogc_async_mut/fs_driver/mount_table.spl` plus
`src/os/sosix/fs/kernel_positioned_dispatch_v1.spl` from a side that never
carried the **API those consumers call**. The repair pass then shrank
mount_table.spl 945 -> 799 lines. Verified: `RootMountSeal` count is **0** at
every one of `e274cd33719`, `a8244005f9b`, `806422e0bd0`, `2760e54e3de`,
`e9da588ee61` — the seal API never reached `main` in any form, so restoring it
is new content, not a revert.

Left undefined anywhere in `src/`:

| symbol | consumers |
|---|---|
| `NvfsRootMountSealV1`, `NvfsRootMountSealInfoV1` | `vfs_nvfs_root_transaction.spl:18,27` |
| `DbfsRootMountSealV1`, `DbfsRootMountSealInfoV1` | `vfs_boot_state.spl:42`, `server_data_namespace_owner.spl:9` |
| `MountTable.acquire/revalidate/close_dbfs_root_mount_seal` | `vfs_boot_state.spl:273,283,292` |
| `MountTable.acquire/revalidate/close/abort_nvfs_root_mount_seal`, `remove_exact_nvfs_root_mount` | `vfs_nvfs_root_transaction.spl:58,110,112,121,146,164` |
| `sosix_fs_kernel_uninstalled_positioned_state_v1` | `syscall_shim_positioned.spl:21,38,44` |

Plus a dropped `use`: `boot_fs_mount.spl:209` called
`boot_nvfs_root_mount_transaction_v1` with no import at all.

## Why nothing caught it

The freestanding build FABRICATES an unresolved symbol as a weak body that
**returns 0**, and a zero `Result` reads as non-error. So the NVFS "mount"
succeeded, `fs-type=nvfs` printed, and a previous session reported this lane
GREEN. Every serial rung the gate scanned was satisfied by a build that mounted
nothing. Serial scanning is structurally incapable of catching this class.

## Fixes landed

- `src/lib/nogc_async_mut/fs_driver/mount_table.spl` — 6 seal structs, 2 binding
  arrays, 2 bounds constants, 8 seal methods, 4 exports. Shapes and names adopted
  verbatim from the `codex-nvfs-root-mount` lane, re-hosted onto main's
  `MountEntry`-shaped table.
- `src/lib/nogc_async_mut/fs_driver/mount_driver_dispatch.spl` — the 6 `_driver_*`
  identity/kind helpers (additive; no existing signature changed).
- `src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl` — 5 identity/lifecycle methods.
  Main's `pread_bytes_handle` / `pread_bounded_bytes_handle`, which the codex lane
  does not have, were deliberately KEPT: the two sides are each ahead on a
  different axis.
- `src/os/sosix/fs/kernel_positioned_dispatch_v1.spl` — the missing state function.
- `src/os/kernel/boot/boot_fs_mount.spl` — the dropped `use`.

## Guards added so it cannot recur silently

`scripts/check/check-simpleos-nvfs-server-roundtrip-ovmf.shs` gained two
fail-closed rungs and 6 fatal selftest fixtures (11 -> 17):

- **L11** `scan_build_log_fabrication` — zero tolerance for a FABRICATED/stubbed
  symbol on `NVFS_SEAL_SYMBOLS`; a MISSING build log is not a pass.
- **L12** `scan_source_definitions` — every such symbol really defined in `src/`,
  and `boot_fs_mount.spl` really carries the import.

RED-before / GREEN-after, exit codes captured directly into a variable (never
through a pipe): pre-fix tree exit **2** naming all 6 missing symbols plus
`missing-import:boot_fs_mount`; post-fix tree exit **0**, `PASS — 17 check(s)`.

## Remaining blocker — the gate is still honestly RED

`FAIL — 12 check(s) checked, missing: L4 L5 L6 L7 L8 L9 L10`. L1-L3 and L11-L12
are green: OVMF -> GRUB-EFI -> multiboot boots, the guest carries this run's
nonce, pure-Simple NVMe comes up, and nothing on the mount path is stubbed. The
mount itself now really runs and really refuses:

```
production mount ok=false err=... nvfs-root: driver-open-failed:code=0:base=4:blocks=8188
```

See `freestanding_match_over_fserror_yields_default_2026-09-01.md`. It was NOT
faked green.
