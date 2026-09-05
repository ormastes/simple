# Dbfs Remount Persistence Specification

> 1. first write handle

<!-- sdn-diagram:id=dbfs_remount_persistence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_remount_persistence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_remount_persistence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_remount_persistence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Remount Persistence Specification

## Scenarios

### DBFS device-backed remount persistence

#### file written on first mount survives a fresh driver instance

1. first write handle

2. first close handle
   - Expected: stat.is_file is true
   - Expected: stat.size equals `12`
   - Expected: got equals `durable dbfs`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = RamBlockDevice.new_empty()
val first = DbFsDriver.open_on_device(dev, 2048, 128).unwrap()
val fh = first.open_path(Path(raw: "/data.txt"), OpenFlags.create_write()).unwrap()
first.write_handle(fh, "durable dbfs").unwrap()
first.close_handle(fh).unwrap()

val second = DbFsDriver.open_on_device(dev, 2048, 128).unwrap()
val stat = second.stat_path(Path(raw: "/data.txt")).unwrap()
expect(stat.is_file).to_equal(true)
expect(stat.size).to_equal(12)
val fh2 = second.open_path(Path(raw: "/data.txt"), OpenFlags.read_only()).unwrap()
val got = second.read_handle(fh2, 12).unwrap()
expect(got).to_equal("durable dbfs")
```

</details>

#### directory listing replays persisted DBFS file names

1. first write handle

2. first write handle
   - Expected: found_a is true
   - Expected: found_b is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = RamBlockDevice.new_empty()
val first = DbFsDriver.open_on_device(dev, 4096, 128).unwrap()
val a = first.open_path(Path(raw: "/a.txt"), OpenFlags.create_write()).unwrap()
first.write_handle(a, "aaa").unwrap()
val b = first.open_path(Path(raw: "/b.txt"), OpenFlags.create_write()).unwrap()
first.write_handle(b, "bbb").unwrap()

val second = DbFsDriver.open_on_device(dev, 4096, 128).unwrap()
val dh = second.opendir_path(Path(raw: "/")).unwrap()
val entries = second.readdir_handle(dh).unwrap()
var found_a = false
var found_b = false
for entry in entries:
    if entry.name == "/a.txt":
        found_a = true
    if entry.name == "/b.txt":
        found_b = true
expect(found_a).to_equal(true)
expect(found_b).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_remount_persistence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DBFS device-backed remount persistence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
