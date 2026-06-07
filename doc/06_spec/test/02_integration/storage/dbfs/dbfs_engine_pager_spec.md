# dbfs_engine_pager_spec

> DBFS Pager Specification

<!-- sdn-diagram:id=dbfs_engine_pager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_pager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_pager_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_pager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_pager_spec

DBFS Pager Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_pager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Pager Specification

Verifies the single-cache pager used by DbFsEngine:
  1. alloc_page returns a fresh writable page
  2. read_page round-trips data written via write_page
  3. dirty tracking: written page is dirty; clean after flush
  4. page eviction under capacity stays correct
  5. single-cache discipline: no calls into kernel page cache

## Scenarios

### DBFS Pager — alloc and write
_Basic page alloc + write contract._

#### alloc_page returns a unique PageId

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = DbfsPager.new(capacity: 16)
val id1 = p.alloc_page().unwrap()
val id2 = p.alloc_page().unwrap()
expect(id1 == id2).to_equal(false)
```

</details>

#### write_page then read_page round-trips data

1. data set byte
2. p write page
   - Expected: got.byte_at(0) equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
val data = PageData.zeroed()
data.set_byte(0, 0xAB)
p.write_page(id, data).unwrap()
val got = p.read_page(id).unwrap()
expect(got.byte_at(0)).to_equal(0xAB)
```

</details>

#### page size constant is 8192 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PAGE_SIZE_BYTES).to_equal(8192)
```

</details>

### DBFS Pager — dirty tracking
_Dirty/clean state transitions._

#### newly written page is dirty

1. p write page
   - Expected: p.is_dirty(id) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
p.write_page(id, PageData.zeroed()).unwrap()
expect(p.is_dirty(id)).to_equal(true)
```

</details>

#### page is clean after flush

1. p write page
2. p flush page
   - Expected: p.is_dirty(id) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
p.write_page(id, PageData.zeroed()).unwrap()
p.flush_page(id).unwrap()
expect(p.is_dirty(id)).to_equal(false)
```

</details>

#### unflushed pages appear in dirty_pages list

1. p write page
   - Expected: dirty contains `id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
p.write_page(id, PageData.zeroed()).unwrap()
val dirty = p.dirty_pages()
expect(dirty.contains(id)).to_equal(true)
```

</details>

### DBFS Pager — eviction
_LRU eviction does not corrupt content._

#### evicted and re-read page returns correct data

1. data set byte
2. p write page
3. p flush page
4. p write page
5. p flush page
   - Expected: got.byte_at(0) equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = DbfsPager.new(capacity: 4)
val id = p.alloc_page().unwrap()
val data = PageData.zeroed()
data.set_byte(0, 0x42)
p.write_page(id, data).unwrap()
p.flush_page(id).unwrap()
# Fill cache to force eviction of our page
var i: i64 = 0
while i < 8:
    val tmp = p.alloc_page().unwrap()
    p.write_page(tmp, PageData.zeroed()).unwrap()
    p.flush_page(tmp).unwrap()
    i = i + 1
val got = p.read_page(id).unwrap()
expect(got.byte_at(0)).to_equal(0x42)
```

</details>

### DBFS Pager — single-cache discipline
_Pager must not expose a kernel-cache path._

#### pager has no kernel_cache_write method

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Structural check: DbfsPager does not implement kernel_cache_write.
# Phase 5 must ensure the type does not expose this symbol.
val p = DbfsPager.new(capacity: 4)
val has_method = p.has_method("kernel_cache_write")
expect(has_method).to_equal(false)
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
