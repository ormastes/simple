# fat32_no_regression_spec

> FAT32 Hosted Seam Specification

<!-- sdn-diagram:id=fat32_no_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_no_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_no_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_no_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fat32_no_regression_spec

FAT32 Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/fat32_no_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FAT32 Hosted Seam Specification

Verifies the currently implemented FAT32 mount-table surface:
  - shared FsFat32Driver can still be mounted alongside other filesystems
  - DBFS resolution does not fall through to the FAT32 sibling
  - this seam no longer imports or instantiates the legacy Fat32Driver

## Scenarios

### FAT32 hosted seam — mount table registration

#### shared FAT32 driver registers without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_fat32_mounted()
val boot_driver = mt.resolve_driver("/boot").unwrap()
expect(boot_driver.driver_name()).to_equal("Fat32Driver")
```

</details>

#### stays on the shared FsFat32Driver surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("test/integration/storage/dbfs/fat32_no_regression_spec.spl")
val legacy_type = "Fat32" + "Driver"
expect(source.contains("use os.services.fat32.fat32")).to_equal(false)
expect(source.contains(" " + legacy_type + ".new(")).to_equal(false)
expect(source.contains("=" + legacy_type + ".new(")).to_equal(false)
expect(source.contains("(" + legacy_type + ".new(")).to_equal(false)
expect(source.contains("FsFat32Driver.new(")).to_equal(true)
```

</details>

### FAT32 hosted seam — DBFS co-existence

#### FAT32 and DBFS can both be mounted simultaneously

1. mt mount
2. mt mount
   - Expected: boot_driver.driver_name() equals `Fat32Driver`
   - Expected: data_driver.driver_name() equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = MountTable.new()
val fat32 = make_fat32_driver()
mt.mount("/boot", DriverInstance.Fat32(fat32), MountOptions.read_only()).unwrap()
val dbfs = DbFsDriver.new_hosted()
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
val boot_driver = mt.resolve_driver("/boot").unwrap()
val data_driver = mt.resolve_driver("/data/file.txt").unwrap()
expect(boot_driver.driver_name()).to_equal("Fat32Driver")
expect(data_driver.driver_name()).to_equal("DbFsDriver")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
