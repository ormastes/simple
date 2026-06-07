# dbfs_driver_spec

> DBFS FsDriver Seam Specification

<!-- sdn-diagram:id=dbfs_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_driver_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_driver_spec

DBFS FsDriver Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS FsDriver Seam Specification

Verifies DbFsDriver implements the FsDriver trait via MountTable:
  open, read, write, stat, readdir, mkdir, unlink, rename

## Scenarios

### DBFS FsDriver — mkdir and stat

#### mkdir creates directory; stat returns is_dir=true

1. mt mkdir
   - Expected: info.is_dir is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
mt.mkdir("/data/mydir", 0o755).unwrap()
val info = mt.stat("/data/mydir").unwrap()
expect(info.is_dir).to_equal(true)
```

</details>

#### stat on missing path returns error

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val r = mt.stat("/data/ghost")
expect(r.is_err()).to_equal(true)
```

</details>

### DBFS FsDriver — open, write, read

#### open with create_write creates file

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/hello.txt", OpenFlags.create_write()).unwrap()
expect(fh.id > 0).to_equal(true)
```

</details>

#### write then read round-trips content

1. mt write
   - Expected: got equals `hello dbfs`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/rw.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "hello dbfs").unwrap()
val fh2 = mt.open("/data/rw.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh2, 10).unwrap()
expect(got).to_equal("hello dbfs")
```

</details>

#### read on closed handle returns error

1. mt close
   - Expected: r.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/tmp.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
val r = mt.read(fh, 5)
expect(r.is_err()).to_equal(true)
```

</details>

### DBFS FsDriver — readdir

#### readdir on mounted dir returns created entries

1. mt mkdir

2. mt mkdir
   - Expected: entries.len() >= 2 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
mt.mkdir("/data/alpha", 0o755).unwrap()
mt.mkdir("/data/beta", 0o755).unwrap()
val dh = mt.opendir("/data").unwrap()
val entries = mt.readdir(dh).unwrap()
expect(entries.len() >= 2).to_equal(true)
```

</details>

### DBFS FsDriver — unlink and rename

#### unlink removes file; stat returns error

1. mt close

2. mt unlink
   - Expected: r.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/del.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
mt.unlink("/data/del.txt").unwrap()
val r = mt.stat("/data/del.txt")
expect(r.is_err()).to_equal(true)
```

</details>

#### rename moves file; old path gone, new path exists

1. mt close

2. mt rename
   - Expected: old_r.is_err() is true
   - Expected: new_r.is_ok() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/old.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
mt.rename("/data/old.txt", "/data/new.txt").unwrap()
val old_r = mt.stat("/data/old.txt")
val new_r = mt.stat("/data/new.txt")
expect(old_r.is_err()).to_equal(true)
expect(new_r.is_ok()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
