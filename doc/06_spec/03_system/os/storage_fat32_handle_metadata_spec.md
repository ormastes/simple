# Storage Fat32 Handle Metadata Specification

> <details>

<!-- sdn-diagram:id=storage_fat32_handle_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_fat32_handle_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_fat32_handle_metadata_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_fat32_handle_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Fat32 Handle Metadata Specification

## Scenarios

### FsDriver handle metadata contract

#### file and directory handles are distinct opaque ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = FileHandle(id: 42)
val dir = DirHandle(id: 42)
expect(file.id).to_equal(dir.id)
expect(file.is_null()).to_equal(false)
expect(dir.is_null()).to_equal(false)
```

</details>

#### path stat and fstat share the same metadata shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stat = FileStat(
    inode: 7,
    size: 123,
    blocks: 1,
    block_size: 512,
    mode: 0o644,
    uid: 0,
    gid: 0,
    nlinks: 1,
    atime_ns: 0,
    mtime_ns: 0,
    ctime_ns: 0,
    birth_time_ns: 0
)
val path = Path(raw: "/FILE.TXT")
expect(path.raw).to_equal("/FILE.TXT")
expect(stat.inode).to_equal(7u64)
expect(stat.size).to_equal(123u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/storage_fat32_handle_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FsDriver handle metadata contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
