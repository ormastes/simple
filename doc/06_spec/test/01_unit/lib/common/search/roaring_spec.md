# Roaring Specification

> <details>

<!-- sdn-diagram:id=roaring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=roaring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

roaring_spec -> std
roaring_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=roaring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Roaring Specification

## Scenarios

### RoaringBitmap basics

#### empty bitmap has zero cardinality and no members

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rb = RoaringBitmap.new()
expect(rb.cardinality()).to_equal(0)
expect(rb.is_empty()).to_equal(true)
expect(rb.contains(0)).to_equal(false)
expect(rb.contains(42)).to_equal(false)
```

</details>

#### membership matches a hand-written sparse id set

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Absolute oracle: exactly these ids are present, nothing else.
val rb = RoaringBitmap.of([5, 17, 100, 65535])
expect(rb.cardinality()).to_equal(4)
expect(rb.contains(5)).to_equal(true)
expect(rb.contains(17)).to_equal(true)
expect(rb.contains(100)).to_equal(true)
expect(rb.contains(65535)).to_equal(true)
# Absent ids (including a neighbour of a present id).
expect(rb.contains(6)).to_equal(false)
expect(rb.contains(0)).to_equal(false)
expect(rb.contains(65534)).to_equal(false)
```

</details>

#### add is idempotent and out-of-order input yields sorted ids

- var rb = RoaringBitmap new
- rb add
- rb add
- rb add
- rb add
- rb add
   - Expected: rb.cardinality() equals `3`
   - Expected: lists_equal(rb.to_sorted_ids(), [10, 20, 30]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rb = RoaringBitmap.new()
rb.add(30)
rb.add(10)
rb.add(20)
rb.add(10)
rb.add(10)
expect(rb.cardinality()).to_equal(3)
expect(lists_equal(rb.to_sorted_ids(), [10, 20, 30])).to_equal(true)
```

</details>

#### negative ids are ignored

- var rb = RoaringBitmap new
- rb add
- rb add
   - Expected: rb.cardinality() equals `1`
   - Expected: rb contains `7`
   - Expected: rb does not contain `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rb = RoaringBitmap.new()
rb.add(0 - 1)
rb.add(7)
expect(rb.cardinality()).to_equal(1)
expect(rb.contains(7)).to_equal(true)
expect(rb.contains(0 - 1)).to_equal(false)
```

</details>

### container promotion (sparse ARRAY -> dense BITMAP)

#### a sparse chunk stays an ARRAY container

- var rb = RoaringBitmap of
   - Expected: rb.chunks.len() equals `1`
   - Expected: rb.chunks[0].is_array() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rb = RoaringBitmap.of([1, 2, 3])
# one chunk (high key 0), still array
expect(rb.chunks.len()).to_equal(1)
expect(rb.chunks[0].is_array()).to_equal(true)
```

</details>

#### crossing 4096 entries promotes the chunk to BITMAP, exact membership

- var rb = RoaringBitmap new
- present push
- rb add
   - Expected: rb.chunks.len() equals `1`
   - Expected: rb.chunks[0].is_bitmap() is true
   - Expected: rb.cardinality() equals `present.len()`
   - Expected: rb.cardinality() equals `4100`
   - Expected: rb contains `0`
   - Expected: rb contains `4096`
   - Expected: rb contains `4099`
   - Expected: rb does not contain `4100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add ids 0..4099 (4100 entries) into one chunk via a counter loop.
# Independent oracle: a [bool] presence array over the same range.
var rb = RoaringBitmap.new()
var present: [bool] = []
var k = 0
while k < 4100:
    present.push(true)
    k = k + 1
var i = 0
while i < 4100:
    rb.add(i)
    i = i + 1
# Promotion happened: > ARRAY_MAX(4096) entries in one chunk.
expect(rb.chunks.len()).to_equal(1)
expect(rb.chunks[0].is_bitmap()).to_equal(true)
# Cardinality matches the independent oracle count exactly.
expect(rb.cardinality()).to_equal(present.len())
expect(rb.cardinality()).to_equal(4100)
# The EARLIEST member added before promotion is still present (proves
# promotion preserved state), as is a late one and a boundary one.
expect(rb.contains(0)).to_equal(true)
expect(rb.contains(4096)).to_equal(true)
expect(rb.contains(4099)).to_equal(true)
# Just past the set is absent.
expect(rb.contains(4100)).to_equal(false)
```

</details>

#### promoted bitmap materializes ascending ids matching the oracle

- var rb = RoaringBitmap new
- rb add
- oracle push
   - Expected: lists_equal(rb.to_sorted_ids(), oracle) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rb = RoaringBitmap.new()
var oracle: [i64] = []
var i = 0
while i < 4100:
    rb.add(i)
    oracle.push(i)
    i = i + 1
expect(lists_equal(rb.to_sorted_ids(), oracle)).to_equal(true)
```

</details>

### two-chunk span (ids crossing a high-16-bit boundary)

#### stores ids in separate chunks and reports exact membership

- var rb = RoaringBitmap of
   - Expected: rb.chunks.len() equals `3`
   - Expected: rb.cardinality() equals `4`
   - Expected: rb contains `100`
   - Expected: rb contains `65536`
   - Expected: rb contains `65537`
   - Expected: rb contains `131072`
   - Expected: rb does not contain `0`
   - Expected: rb does not contain `65535`
   - Expected: lists_equal(rb.to_sorted_ids(), [100, 65536, 65537, 131072]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 100 is in chunk 0 (high=0); 65536 and 131072 begin chunks 1 and 2.
var rb = RoaringBitmap.of([100, 65536, 65537, 131072])
expect(rb.chunks.len()).to_equal(3)
expect(rb.cardinality()).to_equal(4)
expect(rb.contains(100)).to_equal(true)
expect(rb.contains(65536)).to_equal(true)
expect(rb.contains(65537)).to_equal(true)
expect(rb.contains(131072)).to_equal(true)
# 0 shares chunk 0 with 100 but is absent; 65535 is the last of chunk 0.
expect(rb.contains(0)).to_equal(false)
expect(rb.contains(65535)).to_equal(false)
# Ascending materialization spans the boundary correctly.
expect(lists_equal(rb.to_sorted_ids(), [100, 65536, 65537, 131072])).to_equal(true)
```

</details>

### set algebra: and / or / andnot vs independent oracle

#### overlapping sparse sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = [1, 3, 5, 7, 9]
val lb = [3, 4, 5, 6, 9, 10]
val ra = RoaringBitmap.of(la)
val rb = RoaringBitmap.of(lb)
# Absolute expected lists, cross-checked with the independent oracle.
expect(lists_equal(ra.and(rb).to_sorted_ids(), [3, 5, 9])).to_equal(true)
expect(lists_equal(ra.and(rb).to_sorted_ids(), oracle_and(la, lb))).to_equal(true)
expect(lists_equal(ra.or(rb).to_sorted_ids(), [1, 3, 4, 5, 6, 7, 9, 10])).to_equal(true)
expect(lists_equal(ra.or(rb).to_sorted_ids(), oracle_or(la, lb))).to_equal(true)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), [1, 7])).to_equal(true)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), oracle_andnot(la, lb))).to_equal(true)
```

</details>

#### andnot is directional (A\\B != B\\A on overlap)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = [1, 2, 3]
val lb = [2, 3, 4]
val ra = RoaringBitmap.of(la)
val rb = RoaringBitmap.of(lb)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), [1])).to_equal(true)
expect(lists_equal(rb.andnot(ra).to_sorted_ids(), [4])).to_equal(true)
```

</details>

#### disjoint sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = [1, 2, 3]
val lb = [10, 11, 12]
val ra = RoaringBitmap.of(la)
val rb = RoaringBitmap.of(lb)
expect(ra.and(rb).cardinality()).to_equal(0)
expect(lists_equal(ra.and(rb).to_sorted_ids(), [])).to_equal(true)
expect(lists_equal(ra.or(rb).to_sorted_ids(), [1, 2, 3, 10, 11, 12])).to_equal(true)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), [1, 2, 3])).to_equal(true)
```

</details>

#### identical sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = [4, 8, 15, 16, 23, 42]
val ra = RoaringBitmap.of(la)
val rb = RoaringBitmap.of(la)
expect(lists_equal(ra.and(rb).to_sorted_ids(), la)).to_equal(true)
expect(lists_equal(ra.or(rb).to_sorted_ids(), la)).to_equal(true)
expect(ra.andnot(rb).cardinality()).to_equal(0)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), [])).to_equal(true)
```

</details>

#### empty operand

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = [1, 2, 3]
val ra = RoaringBitmap.of(la)
val empty = RoaringBitmap.new()
expect(ra.and(empty).cardinality()).to_equal(0)
expect(lists_equal(ra.or(empty).to_sorted_ids(), la)).to_equal(true)
expect(lists_equal(ra.andnot(empty).to_sorted_ids(), la)).to_equal(true)
expect(lists_equal(empty.andnot(ra).to_sorted_ids(), [])).to_equal(true)
```

</details>

#### set ops span two high-16-bit chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# la, lb each straddle chunk 0 and chunk 1; results must too.
val la = [5, 65540, 65541]
val lb = [5, 65541, 65542, 131072]
val ra = RoaringBitmap.of(la)
val rb = RoaringBitmap.of(lb)
expect(lists_equal(ra.and(rb).to_sorted_ids(), [5, 65541])).to_equal(true)
expect(lists_equal(ra.and(rb).to_sorted_ids(), oracle_and(la, lb))).to_equal(true)
expect(lists_equal(ra.or(rb).to_sorted_ids(), [5, 65540, 65541, 65542, 131072])).to_equal(true)
expect(lists_equal(ra.or(rb).to_sorted_ids(), oracle_or(la, lb))).to_equal(true)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), [65540])).to_equal(true)
expect(lists_equal(ra.andnot(rb).to_sorted_ids(), oracle_andnot(la, lb))).to_equal(true)
```

</details>

#### dense vs dense intersection across promotion (independent oracle)

- var ra = RoaringBitmap new
- var rb = RoaringBitmap new
- ra add
- rb add
- oracle push
   - Expected: ra.chunks[0].is_bitmap() is true
   - Expected: lists_equal(ra.and(rb).to_sorted_ids(), oracle) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two dense chunks (both promoted to BITMAP). A = evens 0..8198,
# B = multiples of 3 in 0..8198. Independent oracle = multiples of 6.
var ra = RoaringBitmap.new()
var rb = RoaringBitmap.new()
var oracle: [i64] = []
var n = 0
while n < 8200:
    if n - (n / 2) * 2 == 0:
        ra.add(n)
    if n - (n / 3) * 3 == 0:
        rb.add(n)
    if n - (n / 6) * 6 == 0:
        oracle.push(n)
    n = n + 1
# Both promoted (evens count 4100 > 4096).
expect(ra.chunks[0].is_bitmap()).to_equal(true)
expect(lists_equal(ra.and(rb).to_sorted_ids(), oracle)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/roaring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RoaringBitmap basics
- container promotion (sparse ARRAY -> dense BITMAP)
- two-chunk span (ids crossing a high-16-bit boundary)
- set algebra: and / or / andnot vs independent oracle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
