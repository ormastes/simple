# FAT32 atomic-replace lifecycle test fails with `FsError::Corrupt`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: FIXED (2026-11-11, lane ne9 — verified on fresh seed 46fe8f6b6def;
  owning spec 5/5 in interpreter mode)
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


## 2026-11-11 — P3 ne9 triage: FIXED on fresh seed

Lane ne9 (batch 2026-11-11) re-ran the owning spec on the fresh seed
(build-commit `46fe8f6b6def`, `SIMPLE_LIB=src`, interpreter mode,
`--no-cache`):

- `test/02_integration/storage/dbfs/fat32_no_regression_spec.spl` —
  **5/5 PASS**. The tracked scenario "routes atomic replace lifecycle
  operations through the shared mount table" (the `FsError::Corrupt`
  repro of this doc) passes; the FAT32 rename/atomic-replace path is
  fixed. No `FsError::Corrupt`.
- One sibling scenario in the same file, "stays on the shared
  FsFat32Driver surface", failed on the first run for an unrelated
  reason: it scans its OWN source via
  `read_file("test/integration/storage/dbfs/fat32_no_regression_spec.spl")`,
  a path orphaned by the test-tree consolidation `4f51a7ee31fc`
  (`test/integration` -> `test/02_integration`). The stale self-scan
  path was corrected in the same commit; the full spec is now 5/5.
