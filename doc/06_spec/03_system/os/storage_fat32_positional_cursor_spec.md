# FAT32 Positional Cursor Preservation

> System-level regression check for FR-STORAGE-0002. FAT32 positional I/O uses

<!-- sdn-diagram:id=storage_fat32_positional_cursor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_fat32_positional_cursor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_fat32_positional_cursor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_fat32_positional_cursor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 Positional Cursor Preservation

System-level regression check for FR-STORAGE-0002. FAT32 positional I/O uses

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/storage_fat32_positional_cursor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-STORAGE-0002. FAT32 positional I/O uses
save/seek/operation/restore, so cursor restoration must preserve size changes.

## Scenarios

### FAT32 positional cursor preservation
_FAT32 open-file cursor restoration must not roll back metadata._

#### seek updates the open-file cursor

1. var driver = cursor driver
   - Expected: seek_r.is_ok() is true
   - Expected: file.position equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = cursor_driver()
val seek_r = driver.seek(FileHandle(id: 1), 0)
expect(seek_r.is_ok()).to_equal(true)
val file = driver.open_files[0]
expect(file.position).to_equal(0)
```

</details>

#### cursor restore keeps file size while restoring saved position

1. var driver = cursor driver
2. driver seek
3. driver open files remove
   - Expected: restore.is_ok() is true
   - Expected: file.position equals `10`
   - Expected: file.current_cluster equals `2`
   - Expected: file.size equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = cursor_driver()
driver.seek(FileHandle(id: 1), 0)
val current = driver.open_files[0]
driver.open_files.remove(0)
driver.open_files.push(OpenFile(
    start_cluster: current.start_cluster,
    current_cluster: current.current_cluster,
    position: current.position,
    size: 96,
    is_dir: current.is_dir,
    is_open: current.is_open
))
val restore = driver.restore_open_file_cursor(FileHandle(id: 1), 2, 10)
expect(restore.is_ok()).to_equal(true)
val file = driver.open_files[0]
expect(file.position).to_equal(10)
expect(file.current_cluster).to_equal(2)
expect(file.size).to_equal(96)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
