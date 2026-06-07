# fat32_cache_spec

> FAT32 Cache Specification

<!-- sdn-diagram:id=fat32_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fat32_cache_spec

FAT32 Cache Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/fat32_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FAT32 Cache Specification

Validates three cache layers added to the FAT32 driver:
  - FatSectorCache: sector buffer cache (Dict<u64, [u8]>)
  - ChainCache: cluster-chain cache (Dict<u32, [u32]>)
  - PathCache: path-to-DirEntry cache (Dict<text, DirEntry>)

## Scenarios

### FatSectorCache

### get

#### AC-1: returns nil on cache miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = FatSectorCache.new(8)
val result = c.get(42)
expect(result).to_be_nil()
```

</details>

#### AC-1: returns cached sector on cache hit

1. var c = FatSectorCache new
2. c put
   - Expected: is_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(8)
var data: [u8] = [1, 2, 3, 4]
c.put(10, data)
val result = c.get(10)
val is_nil = result == nil
expect(is_nil).to_equal(false)
```

</details>

### put

#### AC-1: stored sector is retrievable via get

1. var c = FatSectorCache new
2. c put
   - Expected: is_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(8)
var data: [u8] = [0xAB, 0xCD]
c.put(99, data)
val got = c.get(99)
val is_nil = got == nil
expect(is_nil).to_equal(false)
```

</details>

#### AC-1: different sectors stored independently

1. var c = FatSectorCache new
2. c put
3. c put
   - Expected: r1_nil is false
   - Expected: r2_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(8)
var d1: [u8] = [1]
var d2: [u8] = [2]
c.put(1, d1)
c.put(2, d2)
val r1 = c.get(1)
val r2 = c.get(2)
val r1_nil = r1 == nil
val r2_nil = r2 == nil
expect(r1_nil).to_equal(false)
expect(r2_nil).to_equal(false)
```

</details>

### invalidate

#### AC-4: invalidate removes specific sector from cache

1. var c = FatSectorCache new
2. c put
3. c invalidate


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(8)
var data: [u8] = [0xFF]
c.put(7, data)
c.invalidate(7)
val result = c.get(7)
expect(result).to_be_nil()
```

</details>

#### AC-4: invalidate does not affect other cached sectors

1. var c = FatSectorCache new
2. c put
3. c put
4. c invalidate
   - Expected: r4_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(8)
var d1: [u8] = [1]
var d2: [u8] = [2]
c.put(3, d1)
c.put(4, d2)
c.invalidate(3)
val r4 = c.get(4)
val r4_nil = r4 == nil
expect(r4_nil).to_equal(false)
```

</details>

### ChainCache

### get_chain

#### AC-2: returns nil on cache miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ChainCache.new(256)
val result = c.get_chain(5)
expect(result).to_be_nil()
```

</details>

#### AC-2: returns cached chain on hit

1. var c = ChainCache new
2. c put chain
   - Expected: is_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ChainCache.new(256)
var chain: [u32] = [5, 6, 7]
c.put_chain(5, chain)
val result = c.get_chain(5)
val is_nil = result == nil
expect(is_nil).to_equal(false)
```

</details>

### put_chain

#### AC-2: stored chain is retrievable

1. var c = ChainCache new
2. c put chain
   - Expected: is_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ChainCache.new(256)
var chain: [u32] = [10, 11, 12]
c.put_chain(10, chain)
val got = c.get_chain(10)
val is_nil = got == nil
expect(is_nil).to_equal(false)
```

</details>

### invalidate

#### AC-4: invalidation clears specific chain entry

1. var c = ChainCache new
2. c put chain
3. c invalidate


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ChainCache.new(256)
var chain: [u32] = [20, 21]
c.put_chain(20, chain)
c.invalidate(20)
val result = c.get_chain(20)
expect(result).to_be_nil()
```

</details>

#### AC-4: invalidation does not affect other chains

1. var c = ChainCache new
2. c put chain
3. c put chain
4. c invalidate
   - Expected: r40_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ChainCache.new(256)
var c1: [u32] = [30, 31]
var c2: [u32] = [40, 41]
c.put_chain(30, c1)
c.put_chain(40, c2)
c.invalidate(30)
val r40 = c.get_chain(40)
val r40_nil = r40 == nil
expect(r40_nil).to_equal(false)
```

</details>

### PathCache

### get

#### AC-3: returns nil on cache miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PathCache.new(512)
val result = c.get("/foo/bar")
expect(result).to_be_nil()
```

</details>

#### AC-3: returns cached entry on hit

1. var c = PathCache new
2. inode: Inode
3. c put
   - Expected: is_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = PathCache.new(512)
val entry = DirEntry(
    name: "bar",
    inode: Inode(id: 50),
    is_dir: false
)
c.put("/foo/bar", entry)
val result = c.get("/foo/bar")
val is_nil = result == nil
expect(is_nil).to_equal(false)
```

</details>

### put

#### AC-3: stored entry is retrievable

1. var c = PathCache new
2. inode: Inode
3. c put
   - Expected: is_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = PathCache.new(512)
val entry = DirEntry(
    name: "baz",
    inode: Inode(id: 60),
    is_dir: true
)
c.put("/baz", entry)
val got = c.get("/baz")
val is_nil = got == nil
expect(is_nil).to_equal(false)
```

</details>

### invalidate_prefix

#### AC-6: clears entries matching prefix

1. var c = PathCache new
2. c put
3. c put
4. c invalidate prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = PathCache.new(512)
val e1 = DirEntry(name: "a", inode: Inode(id: 1), is_dir: false)
val e2 = DirEntry(name: "b", inode: Inode(id: 2), is_dir: false)
c.put("/dir/a", e1)
c.put("/dir/b", e2)
c.invalidate_prefix("/dir")
val r1 = c.get("/dir/a")
val r2 = c.get("/dir/b")
expect(r1).to_be_nil()
expect(r2).to_be_nil()
```

</details>

#### AC-6: does not clear entries with non-matching prefix

1. var c = PathCache new
2. c put
3. c put
4. c invalidate prefix
   - Expected: r_other_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = PathCache.new(512)
val e1 = DirEntry(name: "x", inode: Inode(id: 10), is_dir: false)
val e2 = DirEntry(name: "y", inode: Inode(id: 20), is_dir: false)
c.put("/other/x", e1)
c.put("/dir/y", e2)
c.invalidate_prefix("/dir")
val r_other = c.get("/other/x")
val r_other_nil = r_other == nil
expect(r_other_nil).to_equal(false)
```

</details>

### FatSectorCache LRU

#### evicts least-recently-used sector when full

1. var c = FatSectorCache new
2. c put
3. c put
4. c put
5. c put
   - Expected: r4_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(3)
c.put(1, [0x01])
c.put(2, [0x02])
c.put(3, [0x03])
c.put(4, [0x04])
val r1 = c.get(1)
expect(r1).to_be_nil()
val r4 = c.get(4)
val r4_nil = r4 == nil
expect(r4_nil).to_equal(false)
```

</details>

#### get refreshes access time preventing eviction

1. var c = FatSectorCache new
2. c put
3. c put
4. c put
5. c get
6. c put
   - Expected: r1_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(3)
c.put(1, [0x01])
c.put(2, [0x02])
c.put(3, [0x03])
c.get(1)
c.put(4, [0x04])
val r1 = c.get(1)
val r1_nil = r1 == nil
expect(r1_nil).to_equal(false)
val r2 = c.get(2)
expect(r2).to_be_nil()
```

</details>

#### pinned sectors are not evicted

1. var c = FatSectorCache new
2. c put
3. c mark dirty
4. c put
5. c put
6. c put
   - Expected: r1_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = FatSectorCache.new(3)
c.put(1, [0x01])
c.mark_dirty(1)
c.put(2, [0x02])
c.put(3, [0x03])
c.put(4, [0x04])
val r1 = c.get(1)
val r1_nil = r1 == nil
expect(r1_nil).to_equal(false)
val r2 = c.get(2)
expect(r2).to_be_nil()
```

</details>

### ChainCache LRU

#### evicts least-recently-used chain when full

1. var c = ChainCache new
2. c put chain
3. c put chain
4. c put chain
5. c put chain
   - Expected: r4_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ChainCache.new(3)
c.put_chain(1, [1, 2])
c.put_chain(2, [2, 3])
c.put_chain(3, [3, 4])
c.put_chain(4, [4, 5])
val r1 = c.get_chain(1)
expect(r1).to_be_nil()
val r4 = c.get_chain(4)
val r4_nil = r4 == nil
expect(r4_nil).to_equal(false)
```

</details>

#### get_chain refreshes access time

1. var c = ChainCache new
2. c put chain
3. c put chain
4. c put chain
5. c get chain
6. c put chain
   - Expected: r1_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ChainCache.new(3)
c.put_chain(1, [1, 2])
c.put_chain(2, [2, 3])
c.put_chain(3, [3, 4])
c.get_chain(1)
c.put_chain(4, [4, 5])
val r1 = c.get_chain(1)
val r1_nil = r1 == nil
expect(r1_nil).to_equal(false)
val r2 = c.get_chain(2)
expect(r2).to_be_nil()
```

</details>

### PathCache LRU

#### evicts least-recently-used path when full

1. var c = PathCache new
2. c put
3. c put
4. c put
5. c put
   - Expected: rd_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = PathCache.new(3)
val e = DirEntry(name: "f", inode: Inode(id: 1), is_dir: false)
c.put("/a", e)
c.put("/b", e)
c.put("/c", e)
c.put("/d", e)
val ra = c.get("/a")
expect(ra).to_be_nil()
val rd = c.get("/d")
val rd_nil = rd == nil
expect(rd_nil).to_equal(false)
```

</details>

#### get refreshes access time

1. var c = PathCache new
2. c put
3. c put
4. c put
5. c get
6. c put
   - Expected: ra_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = PathCache.new(3)
val e = DirEntry(name: "f", inode: Inode(id: 1), is_dir: false)
c.put("/a", e)
c.put("/b", e)
c.put("/c", e)
c.get("/a")
c.put("/d", e)
val ra = c.get("/a")
val ra_nil = ra == nil
expect(ra_nil).to_equal(false)
val rb = c.get("/b")
expect(rb).to_be_nil()
```

</details>

### ClusterDataCache LRU

#### evicts least-recently-used cluster when full

1. var c = ClusterDataCache new
2. c put
3. c put
4. c put
5. c put
   - Expected: r4_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ClusterDataCache.new(3)
c.put(1, [0x01])
c.put(2, [0x02])
c.put(3, [0x03])
c.put(4, [0x04])
val r1 = c.get(1)
expect(r1).to_be_nil()
val r4 = c.get(4)
val r4_nil = r4 == nil
expect(r4_nil).to_equal(false)
```

</details>

#### pinned clusters are not evicted

1. var c = ClusterDataCache new
2. c put
3. c mark dirty
4. c put
5. c put
6. c put
   - Expected: r1_nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = ClusterDataCache.new(3)
c.put(1, [0x01])
c.mark_dirty(1)
c.put(2, [0x02])
c.put(3, [0x03])
c.put(4, [0x04])
val r1 = c.get(1)
val r1_nil = r1 == nil
expect(r1_nil).to_equal(false)
val r2 = c.get(2)
expect(r2).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
