# dbfs_no_regression_spec pre-existing RED at HEAD (2026-08-26)

## Symptom
`bin/simple test test/integration/storage/dbfs/dbfs_no_regression_spec.spl`
at HEAD (verified via `git show HEAD:...` restored in place, 2026-08-26):

```
Results: 5 total, 2 passed, 3 failed
```

Failing scenarios:
- `stat on DBFS root returns is_dir=true` — `unwrap on Err: FsError::InvalidArg` (stat of `"/data/"` trailing-slash form)
- `open on a DBFS path returns a valid handle` — `unwrap on Err: FsError::NotFound` (`/data/README.TXT`)
- `read on DBFS returns empty content rather than erroring` — `unwrap on Err: FsError::NotFound`

The failures originate inside the shared helpers
`test/fixtures/storage/dbfs/hosted_fs_no_regression_shared.spl`, so the FAT32
sibling spec (`test/integration/storage/dbfs/fat32_no_regression_spec.spl`)
likely shares the defect class.

## Handling
Left RED per testing rules (a correct spec failing documents a real defect;
never weaken assertions). sspec-maintain modernization fix for this file was
not applied — scoring fix would be meaningless on a failing spec.

## Unblock condition
DbFsDriver hosted mount must accept trailing-slash stat of the mount root and
resolve/open hosted file paths such as `/data/README.TXT` (or the spec's
fixture expectations must be reconciled with the driver's current hosted
behavior by the feature owner).
