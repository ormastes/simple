# Handle Pointers Specification

> Handle pointers provide safe, reusable references to i64 values via a slot table with generation counters. Freed slots are reused, but stale handles are detected via generation mismatch.

<!-- sdn-diagram:id=handle_pointers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=handle_pointers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

handle_pointers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=handle_pointers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Handle Pointers Specification

Handle pointers provide safe, reusable references to i64 values via a slot table with generation counters. Freed slots are reused, but stale handles are detected via generation mismatch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #820-825 |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/handle_pointers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Handle pointers provide safe, reusable references to i64 values via a slot
table with generation counters. Freed slots are reused, but stale handles
are detected via generation mismatch.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Handle | Index + generation pair for safe reference |
| Generation | Version counter incremented on free |
| Pool | Pre-allocated slot table with free list |
| Slot reuse | Freed indices are recycled |

## Scenarios

### Handle - create and deref

#### creates handle for value

1. handle pool new
   - Expected: handle_deref(h) equals `42`
   - Expected: handle_is_valid(h) is true
2. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(16)
val h = handle_alloc(42)
expect(handle_deref(h)).to_equal(42)
expect(handle_is_valid(h)).to_equal(true)
handle_pool_reset()
```

</details>

### Handle - deref safely

#### dereferences handle

1. handle pool new
   - Expected: v equals `100`
2. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(16)
val h = handle_alloc(100)
val v = handle_deref(h)
expect(v).to_equal(100)
handle_pool_reset()
```

</details>

### Handle - validate live

#### validates live handle

1. handle pool new
   - Expected: handle_is_valid(h) is true
2. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(16)
val h = handle_alloc(100)
expect(handle_is_valid(h)).to_equal(true)
handle_pool_reset()
```

</details>

### Handle - detect stale

#### detects freed handle

1. handle pool new
2. handle free
   - Expected: handle_is_valid(h) is false
3. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(16)
val h = handle_alloc(100)
handle_free(h)
expect(handle_is_valid(h)).to_equal(false)
handle_pool_reset()
```

</details>

### Handle - generation invalidation

#### old handle invalid after slot reuse

1. handle pool new
2. handle free
   - Expected: handle_is_valid(h1) is false
   - Expected: handle_is_valid(h2) is true
   - Expected: handle_deref(h2) equals `20`
3. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(16)
val h1 = handle_alloc(10)
handle_free(h1)
val h2 = handle_alloc(20)
expect(handle_is_valid(h1)).to_equal(false)
expect(handle_is_valid(h2)).to_equal(true)
expect(handle_deref(h2)).to_equal(20)
handle_pool_reset()
```

</details>

### Handle - slot reuse

#### reuses freed slot index

1. handle pool new
2. handle free
   - Expected: idx1 equals `idx2`
   - Expected: handle_deref(h2) equals `200`
3. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(4)
val h1 = handle_alloc(100)
val idx1 = h1.index
handle_free(h1)
val h2 = handle_alloc(200)
val idx2 = h2.index
expect(idx1).to_equal(idx2)
expect(handle_deref(h2)).to_equal(200)
handle_pool_reset()
```

</details>

### Handle - multiple handles

#### manages multiple concurrent handles

1. handle pool new
   - Expected: handle_is_valid(h1) is true
   - Expected: handle_is_valid(h2) is true
   - Expected: handle_is_valid(h3) is true
   - Expected: handle_pool_size() equals `3`
2. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(16)
val h1 = handle_alloc(1)
val h2 = handle_alloc(2)
val h3 = handle_alloc(3)
expect(handle_is_valid(h1)).to_equal(true)
expect(handle_is_valid(h2)).to_equal(true)
expect(handle_is_valid(h3)).to_equal(true)
expect(handle_pool_size()).to_equal(3)
handle_pool_reset()
```

</details>

### Handle - invalid deref

#### returns -1 for freed handle

1. handle pool new
2. handle free
   - Expected: v equals `-1`
3. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(4)
val h = handle_alloc(42)
handle_free(h)
val v = handle_deref(h)
expect(v).to_equal(-1)
handle_pool_reset()
```

</details>

### Handle - double free

#### second free returns false

1. handle pool new
   - Expected: ok1 is true
   - Expected: ok2 is false
2. handle pool reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(4)
val h = handle_alloc(42)
val ok1 = handle_free(h)
val ok2 = handle_free(h)
expect(ok1).to_equal(true)
expect(ok2).to_equal(false)
handle_pool_reset()
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
