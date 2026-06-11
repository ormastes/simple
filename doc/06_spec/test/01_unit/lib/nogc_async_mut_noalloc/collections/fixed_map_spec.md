# Fixed Map Specification

> <details>

<!-- sdn-diagram:id=fixed_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_map_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Map Specification

## Scenarios

### FixedMap

### construction

#### creates empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
expect(map.is_empty()).to_equal(true)
expect(map.is_full()).to_equal(false)
expect(map.size()).to_equal(0)
```

</details>

### put and get

#### stores and retrieves values

1. map put
2. map put
   - Expected: map.get(42) equals `100`
   - Expected: map.get(7) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
map.put(42, 100)
map.put(7, 200)
expect(map.get(42)).to_equal(100)
expect(map.get(7)).to_equal(200)
```

</details>

#### returns 0 for missing keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
expect(map.get(99)).to_equal(0)
```

</details>

#### updates existing key

1. map put
2. map put
   - Expected: map.get(42) equals `999`
   - Expected: map.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
map.put(42, 100)
map.put(42, 999)
expect(map.get(42)).to_equal(999)
expect(map.size()).to_equal(1)
```

</details>

#### returns false when map is full

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(2)
expect(map.put(1, 10)).to_equal(true)
expect(map.put(2, 20)).to_equal(true)
expect(map.put(3, 30)).to_equal(false)
```

</details>

### contains

#### returns true for existing key

1. map put
   - Expected: map contains `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
map.put(42, 100)
expect(map.contains(42)).to_equal(true)
```

</details>

#### returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
expect(map.contains(42)).to_equal(false)
```

</details>

### remove

#### removes existing key

1. map put
2. map put
   - Expected: map.remove(42) is true
   - Expected: map does not contain `42`
   - Expected: map.get(7) equals `200`
   - Expected: map.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
map.put(42, 100)
map.put(7, 200)
expect(map.remove(42)).to_equal(true)
expect(map.contains(42)).to_equal(false)
expect(map.get(7)).to_equal(200)
expect(map.size()).to_equal(1)
```

</details>

#### returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
expect(map.remove(42)).to_equal(false)
```

</details>

### multiple entries

#### handles multiple entries with different keys

1. map put
2. map put
3. map put
4. map put
5. map put
   - Expected: map.size() equals `5`
   - Expected: map.get(1) equals `10`
   - Expected: map.get(3) equals `30`
   - Expected: map.get(5) equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(32)
map.put(1, 10)
map.put(2, 20)
map.put(3, 30)
map.put(4, 40)
map.put(5, 50)
expect(map.size()).to_equal(5)
expect(map.get(1)).to_equal(10)
expect(map.get(3)).to_equal(30)
expect(map.get(5)).to_equal(50)
```

</details>

### size tracking

#### tracks size through put and remove

1. map put
   - Expected: map.size() equals `1`
2. map put
   - Expected: map.size() equals `2`
3. map remove
   - Expected: map.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(16)
expect(map.size()).to_equal(0)
map.put(1, 10)
expect(map.size()).to_equal(1)
map.put(2, 20)
expect(map.size()).to_equal(2)
map.remove(1)
expect(map.size()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FixedMap
- construction
- put and get
- contains
- remove
- multiple entries
- size tracking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
