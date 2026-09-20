# FAT32 RAM-backed test stub can never pass a real mount()

**Filed:** 2026-09-20
**Area:** `src/lib/nogc_async_mut/fs_driver/fat32_stub.spl`,
`src/lib/nogc_async_mut/fs_driver/mount_table.spl`

## Summary

`FsFat32Driver.new_ram_backed()` / `new_ram_backed_with_file(filename, content)`
build a `RamBlockDevice` for tests, but `RamBlockDevice.read_sector()`
(`fat32_stub.spl:551`) always returns a zero-filled sector unless something
previously called `write_sector` — it never reads from the device's own
`files: [RamFile]` field. `new_with_file()` (`fat32_stub.spl:544`) stores the
requested file/content into `files`, but nothing ever turns that into a real
FAT32 boot sector, FAT, or root-directory entry on the simulated block device.

Separately, `MountTable.mount()` (`src/lib/nogc_async_mut/fs_driver/mount_table.spl`)
never called the registered driver's `mount(opts)` at all — so for backends
that gate real operations on an internal `mounted` flag (FAT32, RamFS; see
`fat32_stub.spl` and `ramfs.spl`), every operation past `table.mount()` failed
closed with `FsError.InvalidArg` before ever reaching FAT32-specific logic.
That half is fixed in this change (`mount_table.spl` now calls
`_driver_mount(driver, opts)`, dispatched per-backend in
`mount_driver_dispatch.spl`), and is a real, independently useful fix — RamFS's
own `open_path()` is an unconditional stub, so it doesn't expose the gap, but
FAT32's real `open()`/`resolve_path()` do.

With that fix, `FsFat32Driver.mount(opts)` is now actually invoked, but it
still fails with `FsError.Corrupt`, because `Fat32Core.mount()`
(`fat32_core.spl:289`) requires a real, valid FAT32 boot sector
(`_has_boot_signature`, `_parse_bpb`, `_geometry_is_valid`) read via
`read_sector()` — which the RAM stub never writes. `new_ram_backed()`'s own
docstring calls it "a RAM-backed (empty) FsFat32Driver for tests", implying it
was expected to be usable without a real on-disk format, but no formatter ever
existed to back that claim.

## Reproduction

```
test/01_unit/lib/fs_driver/mount_table_execute_path_open_spec.spl
test/02_integration/storage/fs_driver_durability_conformance_spec.spl
  ("FAT32 fails closed until a durable sync implementation is provided")
```

Both mount a `FsFat32Driver.new_ram_backed()` / `new_ram_backed_with_file(...)`
through `MountTable.mount()` and then call `table.open(...)`. Before this
change: `FsError.InvalidArg` (driver never mounted at all). After this change:
`FsError.Corrupt` from `Fat32Core.mount()` (no real boot sector on the RAM
device).

## Fix needed

Either:
- give `RamBlockDevice` (or a new FAT32-specific RAM fixture) a real minimal
  FAT32 formatter that writes a valid BPB/FAT/root-directory image seeded from
  `files: [RamFile]`, so `Fat32Core.mount()` succeeds against it; or
- add a FAT32-specific "already mounted, skip real geometry parsing" test
  constructor that sets `mounted: true` plus the minimal fields
  `resolve_path`/`open` actually read (`root_cluster`, `bytes_per_sector`,
  `sectors_per_cluster`, ...), backed by an in-memory directory/FAT structure
  that `find_entry_in_dir` can walk without a real block device.

Both are more than a "smallest diff" fix belongs doing opportunistically;
scoping as a follow-up rather than expanding this change into a FAT32-image
formatter.

## Status

Out of scope for this change beyond the `MountTable.mount()` wiring fix above,
which is real, independently valid, and does not regress either spec (FAT32
was already red on both before this change). Both listed specs remain red,
now on `FsError.Corrupt` for the FAT32 cases specifically, with the exact
failure classified and reproducible per this doc.

**Value-semantics correction (verified with a throwaway probe spec, not
committed):** struct parameters are value types here, so a naive
`match driver: case DriverInstance.Fat32(d): d.mount(opts)` mutates only the
local `d` binding — the mutated `mounted` flag never reaches the `driver`
value the caller stores into `MountEntry`. Probed directly: after
`table.mount("/", DriverInstance.RamFs(...), ...)`, reading
`table.mounts[0].driver`'s `mounted` field back out came back `false` with the
naive dispatch, `true` after `_driver_mount` was changed to return the mutated
`DriverInstance` and `MountTable.mount()` was changed to store that returned
value (`mounted_driver`) into the entry instead of the original `driver`
argument. Both `mount_driver_dispatch.spl` and `mount_table.spl` reflect the
corrected version.
