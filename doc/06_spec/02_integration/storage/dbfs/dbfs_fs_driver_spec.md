# dbfs_fs_driver_spec

> DBFS FsDriver Engine Specification

<!-- sdn-diagram:id=dbfs_fs_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_fs_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_fs_driver_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_fs_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_fs_driver_spec

DBFS FsDriver Engine Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_fs_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS FsDriver Engine Specification

Verifies DbfsFsDriver — the engine-backed driver that wires NsBTree
namespace lookups with arena-backed file data storage:
  1. open creates a file; stat returns is_file=true
  2. write then read round-trips content via arena
  3. readdir lists created files
  4. unlink hides the file from stat
  5. rename moves path and updates NsBTree
  6. mkdir creates directory; stat returns is_dir=true
  7. close + read on closed handle returns error

## Scenarios

### DbfsFsDriver — open and stat

#### open creates file; stat returns is_file=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/hello.txt"), OpenFlags.create_write()).unwrap()
expect(fh.id > 0).to_equal(true)
val info = drv.stat_path(Path(raw: "/hello.txt")).unwrap()
expect(info.is_file).to_equal(true)
expect(info.is_dir).to_equal(false)
```

</details>

#### stat on missing path returns NotFound

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val r = drv.stat_path(Path(raw: "/ghost.txt"))
expect(r.is_err()).to_equal(true)
```

</details>

#### stat on root returns is_dir=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val info = drv.stat_path(Path(raw: "/")).unwrap()
expect(info.is_dir).to_equal(true)
```

</details>

### DbfsFsDriver — write and read

#### write then read_handle round-trips content

1. drv write handle
   - Expected: got equals `hello dbfs engine`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/rw.txt"), OpenFlags.create_write()).unwrap()
drv.write_handle(fh, "hello dbfs engine").unwrap()
val fh2 = drv.open_path(Path(raw: "/rw.txt"), OpenFlags.read_only()).unwrap()
val got = drv.read_handle(fh2, 17).unwrap()
expect(got).to_equal("hello dbfs engine")
```

</details>

#### size after write reflects byte count

1. drv write handle
   - Expected: info.size equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/sized.txt"), OpenFlags.create_write()).unwrap()
drv.write_handle(fh, "abc").unwrap()
val info = drv.stat_path(Path(raw: "/sized.txt")).unwrap()
expect(info.size).to_equal(3)
```

</details>

#### empty file has size 0

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/empty.txt"), OpenFlags.create_write()).unwrap()
val info = drv.stat_path(Path(raw: "/empty.txt")).unwrap()
expect(info.size).to_equal(0)
```

</details>

### DbfsFsDriver — close

#### read on closed handle returns error

1. drv close handle
   - Expected: r.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/tmp.txt"), OpenFlags.create_write()).unwrap()
drv.close_handle(fh).unwrap()
val r = drv.read_handle(fh, 5)
expect(r.is_err()).to_equal(true)
```

</details>

#### close on invalid handle returns error

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val bad = FileHandle(id: 9999u64)
val r = drv.close_handle(bad)
expect(r.is_err()).to_equal(true)
```

</details>

### DbfsFsDriver — namespace via NsBTree

#### readdir lists all created files

1. drv open path

2. drv open path
   - Expected: entries.len() >= 2 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
drv.open_path(Path(raw: "/a.txt"), OpenFlags.create_write()).unwrap()
drv.open_path(Path(raw: "/b.txt"), OpenFlags.create_write()).unwrap()
val dh = drv.opendir_path(Path(raw: "/")).unwrap()
val entries = drv.readdir_handle(dh).unwrap()
expect(entries.len() >= 2).to_equal(true)
```

</details>

#### unlink hides file from stat

1. drv open path

2. drv unlink path
   - Expected: r.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
drv.open_path(Path(raw: "/bye.txt"), OpenFlags.create_write()).unwrap()
drv.unlink_path("/bye.txt").unwrap()
val r = drv.stat_path(Path(raw: "/bye.txt"))
expect(r.is_err()).to_equal(true)
```

</details>

#### rename moves file to new path

1. drv write handle

2. drv rename path
   - Expected: r_old.is_err() is true
   - Expected: r_new.is_ok() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/old.txt"), OpenFlags.create_write()).unwrap()
drv.write_handle(fh, "data").unwrap()
drv.rename_path("/old.txt", "/new.txt").unwrap()
val r_old = drv.stat_path(Path(raw: "/old.txt"))
expect(r_old.is_err()).to_equal(true)
val r_new = drv.stat_path(Path(raw: "/new.txt"))
expect(r_new.is_ok()).to_equal(true)
```

</details>

### DbfsFsDriver — mkdir

#### mkdir creates directory; stat returns is_dir=true

1. drv mkdir path
   - Expected: info.is_dir is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
drv.mkdir_path("/mydir", 0o755).unwrap()
val info = drv.stat_path(Path(raw: "/mydir")).unwrap()
expect(info.is_dir).to_equal(true)
```

</details>

#### mkdir twice returns AlreadyExists

1. drv mkdir path
   - Expected: r.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
drv.mkdir_path("/dup", 0o755).unwrap()
val r = drv.mkdir_path("/dup", 0o755)
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
