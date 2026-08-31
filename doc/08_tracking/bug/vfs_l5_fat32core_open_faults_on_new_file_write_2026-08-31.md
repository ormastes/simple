# L5 blocker: `Fat32Core.open` faults on the first write of a NEW file (2026-08-31)

**Status:** OPEN. This is the single remaining blocker on goal item 5
(`scripts/check/check-simpleos-vfs-server-roundtrip-ovmf.shs`).

## Where the lane now stands
With the gate's volume staged to the production contract (see
`make_os_disk_never_compiled_half_landed_helpers_2026-08-31.md` and the same
commit), **L3 and L4 went green**. Verbatim verdict:

```
FAIL — 8 check(s) checked, missing: L5 L6 L7 L8 (nonce=202608311911392483120, ...)
```

Serial transcript, in-guest under real OVMF pflash (no `-kernel`, no
`isa-debug-exit`):

```
[vfsrt] probe begin nonce=202608311911392483120
[vfsrt] initializing storage stack (VFS/NVMe/FAT32)
[vfsrt] vfs_boot_init_production ok=true          <- L3 GREEN (was RED)
[vfsrt] generic FAT32 mount ok (arbitrary paths writable)
[vfsrt] fs-server up ready=true                   <- L4 GREEN (was RED)
[vfsrt] ipc-port attempted (advisory)
[vfsrt] server write begin path=/VFSRT.TXT bytes=33
FAULT @ 0x000000000801cbb2
FAULT @ 0x000000000801b87d
FAULT @ 0x000000000801b975
...
```

`g_vfs_write_file_text` is ENTERED and never returns — no `ok=` line is ever
printed, so L5/L6/L7 cannot be reached and L8 (the host-side raw-image check)
has nothing to find.

## Localization — the faulting frames resolve exactly
`addr2line` against `build/os/simpleos_vfsrt_uefi.elf`:

| address | symbol |
|---|---|
| `0x801cbb2` | `nogc_async_mut.fs_driver.fat32_file_ops.Fat32Core.open` |
| `0x801b87d` | `nogc_async_mut.fs_driver.fat32_file_ops.Fat32Core.resolve_path` |
| `0x8019b9e` | `nogc_async_mut.fs_driver.fat32_directory_ops.Fat32Core.read_dir_entries` |

So the fault is in the **generic stdlib FAT32 driver** (`src/lib/nogc_async_mut/
fs_driver/fat32_*`) mounted by `_vfsrt_ensure_generic_root_fat32`, on the
`open`-for-create path for a name that does not yet exist. It is NOT in the boot
reader (`src/os/services/vfs/direct_fat32_boot_reader.spl`), which read every
system payload on this same volume without incident, and NOT in the NVMe driver.

## What is ruled out
- **Not the volume.** The same volume is read successfully seconds earlier:
  version probe, BROWSMF/HELLOSMF/CLANGSMF all read at 4096 bytes each, and the
  shared FAT32 root mounted (`[vfs-init] shared FAT32 root mounted after direct
  bootstrap`).
- **Not a nil weak stub.** `nm` on the kernel shows 50 weak symbols and **none**
  in the `rt_nvme*`/`rt_mmio*`/`rt_pci*` families, so this is real code faulting,
  not the x86_64 `auto_stubs.c` nil-stub hazard.
- **Not the gate.** `--selftest` is green (9 fixtures), and L1/L2/L3/L4 all pass
  on this exact run.
- **Not a flush-timing artifact.** L8 would be the symptom of that; here the
  write never completes at all.

## Next step for whoever picks this up
Read `Fat32Core.open`'s create path and `resolve_path`/`read_dir_entries` for a
non-existent leaf under a directory-cluster chain authored by
`scripts/os/make_os_disk.c`. The most likely shapes, in order: an unterminated
directory scan running off the end of the root cluster chain (the boot reader
walks the same clusters with its own, simpler code and survives), or an
out-of-range cluster read when the scan reaches the free-space region. Compare
the two readers' chain-termination conditions before changing either.
