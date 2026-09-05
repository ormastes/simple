# storage_fat32_statfs_truncate_spec

> FR-STORAGE-0001 — FAT32 free-space and truncate primitives.

<!-- sdn-diagram:id=storage_fat32_statfs_truncate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_fat32_statfs_truncate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_fat32_statfs_truncate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_fat32_statfs_truncate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# storage_fat32_statfs_truncate_spec

FR-STORAGE-0001 — FAT32 free-space and truncate primitives.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/storage_fat32_statfs_truncate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FR-STORAGE-0001 — FAT32 free-space and truncate primitives.

## Scenarios

### FAT32 statfs and truncate primitives
_FAT32 free-space accounting and truncate helpers expose testable storage metadata._

#### counts free FAT entries across mounted data clusters

1. var driver = statfs driver
   - Expected: free.is_ok() is true
   - Expected: free.unwrap() equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = statfs_driver()
val free = driver.count_free_clusters()
expect(free.is_ok()).to_equal(true)
expect(free.unwrap()).to_equal(2u32)
```

</details>

#### truncate_chain can free a whole file chain

1. var driver = statfs driver
   - Expected: truncated.is_ok() is true
   - Expected: truncated.unwrap() equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = statfs_driver()
val truncated = driver.truncate_chain(2, 0)
expect(truncated.is_ok()).to_equal(true)
expect(truncated.unwrap()).to_equal(0u32)
```

</details>

#### truncate_chain extends an empty chain by allocating a cluster

1. var driver = statfs driver
   - Expected: extended.is_ok() is true
   - Expected: new_cluster >= 2u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = statfs_driver()
# Start with no chain (first_cluster < 2), ask for 100 bytes
val extended = driver.truncate_chain(0, 100)
expect(extended.is_ok()).to_equal(true)
# Should have allocated one of the free clusters (3 or 4)
val new_cluster = extended.unwrap()
expect(new_cluster >= 2u32).to_equal(true)
```

</details>

#### ftruncate updates in-memory file size via handle

1. var driver = statfs driver
   - Expected: trunc_rc.is_ok() is true
   - Expected: of.is_ok() is true
   - Expected: of.unwrap().size equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = statfs_driver()
# Manually set up an open file on cluster 2 (which has EOC)
use std.fs_driver.types.{FileHandle}
val fh = driver.alloc_file_handle(2, 512, false)
val trunc_rc = driver.truncate(fh, 0)
expect(trunc_rc.is_ok()).to_equal(true)
val of = driver.get_open_file(fh)
expect(of.is_ok()).to_equal(true)
expect(of.unwrap().size).to_equal(0i64)
```

</details>

#### truncate_chain shrinks a multi-cluster chain

1. var driver = statfs driver
2. assert true
3. assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = statfs_driver()
# cluster 5 has EOC, cluster 2 has EOC -- both are single-cluster chains
# truncate cluster 5 to 256 bytes (< 512 cluster size) should keep cluster 5
val shrunk = driver.truncate_chain(5, 256)
assert_true(shrunk.is_ok())
assert_equal(shrunk.unwrap(), 5u32)
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
