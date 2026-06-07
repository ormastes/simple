# Object Pool Specification

> <details>

<!-- sdn-diagram:id=object_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=object_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

object_pool_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=object_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Pool Specification

## Scenarios

### ObjectPool

#### creates an empty pool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = ObjectPool.new(4)
expect(pool.count()).to_equal(0)
```

</details>

#### acquires a slot and returns index 0

1. var pool = ObjectPool new
   - Expected: idx equals `0`
   - Expected: pool.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(4)
val idx = pool.acquire("bullet")
expect(idx).to_equal(0)
expect(pool.count()).to_equal(1)
```

</details>

#### gets the tag of an acquired slot

1. var pool = ObjectPool new
   - Expected: pool.get_tag(idx) equals `enemy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(4)
val idx = pool.acquire("enemy")
expect(pool.get_tag(idx)).to_equal("enemy")
```

</details>

#### reports active status correctly

1. var pool = ObjectPool new
   - Expected: pool.is_active(idx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(4)
val idx = pool.acquire("item")
expect(pool.is_active(idx)).to_equal(true)
```

</details>

#### releases a slot by index

1. var pool = ObjectPool new
2. pool release
   - Expected: pool.count() equals `0`
   - Expected: pool.is_active(idx) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(4)
val idx = pool.acquire("bullet")
pool.release(idx)
expect(pool.count()).to_equal(0)
expect(pool.is_active(idx)).to_equal(false)
```

</details>

#### reuses released slots

1. var pool = ObjectPool new
2. pool acquire
3. pool release
   - Expected: idx2 equals `0`
   - Expected: pool.get_tag(idx2) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(4)
val idx0 = pool.acquire("a")
pool.acquire("b")
pool.release(idx0)
val idx2 = pool.acquire("c")
expect(idx2).to_equal(0)
expect(pool.get_tag(idx2)).to_equal("c")
```

</details>

#### returns -1 when pool is full

1. var pool = ObjectPool new
2. pool acquire
3. pool acquire
   - Expected: idx equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(2)
pool.acquire("a")
pool.acquire("b")
val idx = pool.acquire("c")
expect(idx).to_equal(-1)
```

</details>

#### releases all slots by tag

1. var pool = ObjectPool new
2. pool acquire
3. pool acquire
4. pool acquire
5. pool release by tag
   - Expected: pool.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(8)
pool.acquire("bullet")
pool.acquire("enemy")
pool.acquire("bullet")
pool.release_by_tag("bullet")
expect(pool.count()).to_equal(1)
```

</details>

#### clears all slots

1. var pool = ObjectPool new
2. pool acquire
3. pool acquire
4. pool acquire
5. pool clear
   - Expected: pool.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(4)
pool.acquire("a")
pool.acquire("b")
pool.acquire("c")
pool.clear()
expect(pool.count()).to_equal(0)
```

</details>

#### increments generation on reuse

1. var pool = ObjectPool new
2. pool release
3. pool acquire
   - Expected: pool.slots[0].generation equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ObjectPool.new(2)
val idx = pool.acquire("first")
pool.release(idx)
pool.acquire("second")
expect(pool.slots[0].generation).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/object_pool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ObjectPool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
