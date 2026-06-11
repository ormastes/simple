# Fixed Set Specification

> <details>

<!-- sdn-diagram:id=fixed_set_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_set_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_set_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_set_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Set Specification

## Scenarios

### FixedSet

### construction

#### creates empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
expect(s.is_empty()).to_equal(true)
expect(s.is_full()).to_equal(false)
expect(s.size()).to_equal(0)
expect(s.capacity()).to_equal(16)
```

</details>

### add

#### adds values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
expect(s.add(42)).to_equal(true)
expect(s.add(7)).to_equal(true)
expect(s.size()).to_equal(2)
```

</details>

#### returns true for duplicate values

1. s add
   - Expected: s.add(42) is true
   - Expected: s.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
s.add(42)
expect(s.add(42)).to_equal(true)
expect(s.size()).to_equal(1)
```

</details>

#### returns false when set is full

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(2)
expect(s.add(1)).to_equal(true)
expect(s.add(2)).to_equal(true)
expect(s.add(3)).to_equal(false)
```

</details>

### contains

#### returns true for existing value

1. s add
   - Expected: s contains `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
s.add(42)
expect(s.contains(42)).to_equal(true)
```

</details>

#### returns false for missing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
expect(s.contains(42)).to_equal(false)
```

</details>

### remove

#### removes existing value

1. s add
2. s add
   - Expected: s.remove(42) is true
   - Expected: s does not contain `42`
   - Expected: s contains `7`
   - Expected: s.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
s.add(42)
s.add(7)
expect(s.remove(42)).to_equal(true)
expect(s.contains(42)).to_equal(false)
expect(s.contains(7)).to_equal(true)
expect(s.size()).to_equal(1)
```

</details>

#### returns false for missing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
expect(s.remove(42)).to_equal(false)
```

</details>

### multiple elements

#### handles multiple elements

1. s add
2. s add
3. s add
4. s add
5. s add
   - Expected: s.size() equals `5`
   - Expected: s contains `1`
   - Expected: s contains `3`
   - Expected: s contains `5`
   - Expected: s does not contain `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(32)
s.add(1)
s.add(2)
s.add(3)
s.add(4)
s.add(5)
expect(s.size()).to_equal(5)
expect(s.contains(1)).to_equal(true)
expect(s.contains(3)).to_equal(true)
expect(s.contains(5)).to_equal(true)
expect(s.contains(99)).to_equal(false)
```

</details>

### size tracking

#### tracks size through add and remove

1. s add
   - Expected: s.size() equals `1`
2. s add
   - Expected: s.size() equals `2`
3. s add
   - Expected: s.size() equals `2`
4. s remove
   - Expected: s.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(16)
expect(s.size()).to_equal(0)
s.add(1)
expect(s.size()).to_equal(1)
s.add(2)
expect(s.size()).to_equal(2)
s.add(2)
expect(s.size()).to_equal(2)
s.remove(1)
expect(s.size()).to_equal(1)
```

</details>

### capacity

#### reports full correctly

1. s add
2. s add
   - Expected: s.is_full() is false
3. s add
   - Expected: s.is_full() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = FixedSet.new(3)
s.add(10)
s.add(20)
expect(s.is_full()).to_equal(false)
s.add(30)
expect(s.is_full()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_set_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FixedSet
- construction
- add
- contains
- remove
- multiple elements
- size tracking
- capacity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
