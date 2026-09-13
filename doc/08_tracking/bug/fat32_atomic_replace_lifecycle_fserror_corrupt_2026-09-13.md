# FAT32 atomic-replace lifecycle test fails with `FsError::Corrupt`

- Status: OPEN (2026-09-13)
- Found by: BUGFIX-7 lane while fixing
  `trait_conformance_check_ignores_arity_2026-08-04` (a stale `BlockDevice`
  mock in the same spec file previously made the whole file fail to compile
  under `bin/simple test`'s armed trait-arity check, hiding this).
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed), sha256
  prefix `3d120a6f`, at commit `a6450c9d6f5`.
- Spec: `test/02_integration/storage/dbfs/fat32_no_regression_spec.spl`,
  scenario "routes atomic replace lifecycle operations through the shared
  mount table".

## Repro

```
bin/simple test test/02_integration/storage/dbfs/fat32_no_regression_spec.spl
✗ routes atomic replace lifecycle operations through the shared mount table
    semantic: called unwrap on Err: FsError::Corrupt
```

The scenario:

```spl
var driver = FsFat32Driver.new_ram_backed_with_file("OLD.BIN", "hello")
driver.mount(MountOptions.default()).unwrap()
var table = MountTable.new()
table.mount("/boot", DriverInstance.Fat32(driver), MountOptions.default()).unwrap()
table.rename("/boot/OLD.BIN", "/boot/NEW.BIN").unwrap()   # <- fails here
```

`table.rename(...)` (routed to the FAT32 driver's rename/atomic-replace path)
returns `Err(FsError::Corrupt)` instead of succeeding.

## Not investigated further

Out of scope for the lane that found it. This exercises real FAT32 directory
manipulation through `RamBlockDevice` (not the `MockFat32BlockDevice` fixed in
the sibling bug above), so the defect is most likely in the FAT32
rename/atomic-replace implementation itself
(`src/lib/nogc_async_mut/fs_driver/fat32_stub.spl` or a module it delegates
to), not in the mock. This scenario was previously unreachable under
`bin/simple test` because the arity-check fix in
`trait_conformance_check_ignores_arity_2026-08-04` made the whole spec file
fail to compile before any example ran (the file's `MockFat32BlockDevice` had
a 2-arg `read_sector` against the trait's declared 1-arg signature) — so this
may be a long-standing latent defect, not a new regression.
