# mount_table_nvfs_posix_dispatch_spec

> MountTable NVFS POSIX Dispatch Specification

<!-- sdn-diagram:id=mount_table_nvfs_posix_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mount_table_nvfs_posix_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mount_table_nvfs_posix_dispatch_spec -> std
mount_table_nvfs_posix_dispatch_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mount_table_nvfs_posix_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mount_table_nvfs_posix_dispatch_spec

MountTable NVFS POSIX Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

MountTable NVFS POSIX Dispatch Specification

Verifies that MountTable forwards mutating file operations through the
NvfsPosixDriver mount, not just longest-prefix resolution.

## Scenarios

### MountTable NVFS POSIX dispatch — mutating I/O

#### open + write + pread route through the /data NvfsPosix mount

- mt write
- mt close
   - Expected: mt.pread(reopened, 0, 5).unwrap() equals `hello`
- mt close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table()
val fh = mt.open("/data/hello.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "hello").unwrap()
mt.close(fh).unwrap()
val reopened = mt.open("/data/hello.txt", OpenFlags.read_only()).unwrap()
expect(mt.pread(reopened, 0, 5).unwrap()).to_equal("hello")
mt.close(reopened).unwrap()
```

</details>

#### rename stays within the NvfsPosix mount and preserves content

- mt write
- mt close
- mt rename
   - Expected: mt.pread(reopened, 0, 3).unwrap() equals `abc`
- mt close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table()
val fh = mt.open("/data/from.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "abc").unwrap()
mt.close(fh).unwrap()
mt.rename("/data/from.txt", "/data/to.txt").unwrap()
val reopened = mt.open("/data/to.txt", OpenFlags.read_only()).unwrap()
expect(mt.pread(reopened, 0, 3).unwrap()).to_equal("abc")
mt.close(reopened).unwrap()
```

</details>

#### ftruncate shrinks content through the NvfsPosix mount

- mt write
- mt ftruncate
- mt close
   - Expected: mt.pread(reopened, 0, 6).unwrap() equals `abc`
- mt close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table()
val fh = mt.open("/data/trunc.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "abcdef").unwrap()
mt.ftruncate(fh, 3).unwrap()
mt.close(fh).unwrap()
val reopened = mt.open("/data/trunc.txt", OpenFlags.read_only()).unwrap()
expect(mt.pread(reopened, 0, 6).unwrap()).to_equal("abc")
mt.close(reopened).unwrap()
```

</details>

#### unlink removes the NvfsPosix-backed file

- mt write
- mt close
- mt unlink
   - Expected: mt.stat("/data/dead.txt").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table()
val fh = mt.open("/data/dead.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "gone").unwrap()
mt.close(fh).unwrap()
mt.unlink("/data/dead.txt").unwrap()
expect(mt.stat("/data/dead.txt").is_err()).to_equal(true)
```

</details>

#### sibling non-/data paths still resolve to RamFs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_table()
val resolved = mt.resolve(Path(raw: "/hosts")).unwrap()
expect(resolved.mount_id.id).to_equal(1)
expect(resolved.relpath.raw).to_equal("hosts")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
