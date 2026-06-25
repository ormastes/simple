# dbfs_posix_shim_spec

> DBFS POSIX Shim Specification (D10)

<!-- sdn-diagram:id=dbfs_posix_shim_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_posix_shim_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_posix_shim_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_posix_shim_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_posix_shim_spec

DBFS POSIX Shim Specification (D10)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_posix_shim_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS POSIX Shim Specification (D10)

Verifies the POSIX-compat subset (D10):
  - random write via COW rewrites EXTENT_REF
  - rename-over-existing is atomic
  - unlink-while-open tombstones (data accessible until close)
  - truncate shrink and grow
  - out-of-scope ops return ENOTSUP (mmap shared-writable, hard links, O_DIRECT)

## Scenarios

### DBFS POSIX Shim — random write via COW

#### pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data

- mt write
- mt pwrite
   - Expected: got equals `AAAAACCCCC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/cow.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "AAAAABBBBB").unwrap()
mt.pwrite(fh, "CCCCC", 5).unwrap()
val fh2 = mt.open("/data/cow.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh2, 10).unwrap()
expect(got).to_equal("AAAAACCCCC")
```

</details>

#### pwrite does not corrupt bytes before the written offset

- mt write
- mt pwrite
   - Expected: got[0] equals `'X'`
   - Expected: got[8] equals `'Y'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/cow2.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "XXXXXXXXXX").unwrap()
mt.pwrite(fh, "YY", 8).unwrap()
val fh2 = mt.open("/data/cow2.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh2, 10).unwrap()
expect(got[0]).to_equal('X')
expect(got[8]).to_equal('Y')
```

</details>

### DBFS POSIX Shim — rename-over-existing

#### rename-over-existing is atomic (target replaced)

- mt write
- mt close
- mt write
- mt close
- mt rename
   - Expected: got equals `aaa`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh1 = mt.open("/data/a.txt", OpenFlags.create_write()).unwrap()
mt.write(fh1, "aaa").unwrap()
mt.close(fh1).unwrap()
val fh2 = mt.open("/data/b.txt", OpenFlags.create_write()).unwrap()
mt.write(fh2, "bbb").unwrap()
mt.close(fh2).unwrap()
mt.rename("/data/a.txt", "/data/b.txt").unwrap()
val fh3 = mt.open("/data/b.txt", OpenFlags.read_only()).unwrap()
val got = mt.read(fh3, 3).unwrap()
expect(got).to_equal("aaa")
```

</details>

### DBFS POSIX Shim — unlink-while-open tombstone

#### unlink while handle open: data accessible until close

- mt write
- mt unlink
   - Expected: got equals `ghost`
- mt close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/tomb.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "ghost").unwrap()
mt.unlink("/data/tomb.txt").unwrap()
# File is unlinked but handle still valid
val got = mt.read(fh, 5).unwrap()
expect(got).to_equal("ghost")
mt.close(fh).unwrap()
```

</details>

#### after close, unlinked file is not accessible

- mt unlink
- mt close
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/gone.txt", OpenFlags.create_write()).unwrap()
mt.unlink("/data/gone.txt").unwrap()
mt.close(fh).unwrap()
val r = mt.stat("/data/gone.txt")
expect(r.is_err()).to_equal(true)
```

</details>

### DBFS POSIX Shim — truncate

#### truncate shrinks file; stat shows new size

- mt write
- mt ftruncate
   - Expected: stat.size equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/trunc.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "0123456789").unwrap()
mt.ftruncate(fh, 5).unwrap()
val stat = mt.stat("/data/trunc.txt").unwrap()
expect(stat.size).to_equal(5)
```

</details>

#### truncate grows file; extended region reads as zeros

- mt write
- mt ftruncate
   - Expected: got[0] equals `\0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/grow.txt", OpenFlags.create_write()).unwrap()
mt.write(fh, "AB").unwrap()
mt.ftruncate(fh, 6).unwrap()
val fh2 = mt.open("/data/grow.txt", OpenFlags.read_only()).unwrap()
val got = mt.pread(fh2, 2, 4).unwrap()
expect(got[0]).to_equal("\0")
```

</details>

### DBFS POSIX Shim — out-of-scope ops return ENOTSUP

#### mmap_shared_writable returns ENOTSUP

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/mmap.txt", OpenFlags.create_write()).unwrap()
val r = mt.mmap_shared_writable(fh, 0, 4096)
expect(r.is_err()).to_equal(true)
```

</details>

#### link (hard link) returns ENOTSUP

- mt close
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_mounted()
val fh = mt.open("/data/src.txt", OpenFlags.create_write()).unwrap()
mt.close(fh).unwrap()
val r = mt.link("/data/src.txt", "/data/lnk.txt")
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
