# Persistent List Specification

> <details>

<!-- sdn-diagram:id=persistent_list_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_list_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_list_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_list_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent List Specification

## Scenarios

### PersistentList

### empty list

#### has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
expect(l.len()).to_equal(0)
```

</details>

#### is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
expect(l.is_empty()).to_equal(true)
```

</details>

#### head is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
expect(l.head()).to_be_nil()
```

</details>

#### tail is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
val t = l.tail()
expect(t.len()).to_equal(0)
expect(t.is_empty()).to_equal(true)
```

</details>

### prepend

#### adds element to front

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty().prepend(1)
expect(l.len()).to_equal(1)
expect(l.head()).to_equal(1)
expect(l.is_empty()).to_equal(false)
```

</details>

#### preserves order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty().prepend(3).prepend(2).prepend(1)
expect(l.head()).to_equal(1)
expect(l.get(1)).to_equal(2)
expect(l.get(2)).to_equal(3)
expect(l.len()).to_equal(3)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l1 = PersistentList.empty().prepend(1)
val l2 = l1.prepend(2)
expect(l1.len()).to_equal(1)
expect(l1.head()).to_equal(1)
expect(l2.len()).to_equal(2)
expect(l2.head()).to_equal(2)
```

</details>

#### supports multiple branches from same base

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentList.empty().prepend(1)
val branch_a = base.prepend(10)
val branch_b = base.prepend(20)
expect(base.len()).to_equal(1)
expect(branch_a.len()).to_equal(2)
expect(branch_b.len()).to_equal(2)
expect(branch_a.head()).to_equal(10)
expect(branch_b.head()).to_equal(20)
```

</details>

### PersistentList__of

#### builds list preserving order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([10, 20, 30])
expect(l.len()).to_equal(3)
expect(l.head()).to_equal(10)
expect(l.get(1)).to_equal(20)
expect(l.get(2)).to_equal(30)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([42])
expect(l.len()).to_equal(1)
expect(l.head()).to_equal(42)
```

</details>

### from_array

#### builds list from array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.from_array([5, 10, 15])
expect(l.len()).to_equal(3)
expect(l.head()).to_equal(5)
expect(l.get(2)).to_equal(15)
```

</details>

#### empty array gives empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.from_array([])
expect(l.len()).to_equal(0)
expect(l.is_empty()).to_equal(true)
```

</details>

### get

#### returns element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([5, 10, 15])
expect(l.get(0)).to_equal(5)
expect(l.get(1)).to_equal(10)
expect(l.get(2)).to_equal(15)
```

</details>

#### returns nil for out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2])
expect(l.get(5)).to_be_nil()
```

</details>

#### returns nil for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2])
expect(l.get(-1)).to_be_nil()
```

</details>

### contains

#### finds existing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of(["a", "b", "c"])
expect(l.contains("b")).to_equal(true)
```

</details>

#### returns false for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of(["a", "b", "c"])
expect(l.contains("z")).to_equal(false)
```

</details>

#### works with integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3, 4, 5])
expect(l.contains(3)).to_equal(true)
expect(l.contains(6)).to_equal(false)
```

</details>

#### returns false for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
expect(l.contains(1)).to_equal(false)
```

</details>

### tail

#### returns rest of list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3])
val t = l.tail()
expect(t.len()).to_equal(2)
expect(t.head()).to_equal(2)
```

</details>

#### tail of single element is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([42])
val t = l.tail()
expect(t.len()).to_equal(0)
expect(t.is_empty()).to_equal(true)
```

</details>

#### chained tail calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3])
val t = l.tail().tail()
expect(t.len()).to_equal(1)
expect(t.head()).to_equal(3)
```

</details>

### head

#### returns first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([99, 88, 77])
expect(l.head()).to_equal(99)
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
expect(l.head()).to_be_nil()
```

</details>

### reverse

#### reverses the list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3])
val r = l.reverse()
expect(r.head()).to_equal(3)
expect(r.get(1)).to_equal(2)
expect(r.get(2)).to_equal(1)
```

</details>

#### preserves length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3, 4])
val r = l.reverse()
expect(r.len()).to_equal(4)
```

</details>

#### reverse of single element is same

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([42])
val r = l.reverse()
expect(r.head()).to_equal(42)
expect(r.len()).to_equal(1)
```

</details>

#### reverse of empty is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
val r = l.reverse()
expect(r.len()).to_equal(0)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3])
val r = l.reverse()
expect(l.head()).to_equal(1)
expect(r.head()).to_equal(3)
```

</details>

### to_array

#### converts to array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([10, 20, 30])
val arr = l.to_array()
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(10)
expect(arr[1]).to_equal(20)
expect(arr[2]).to_equal(30)
```

</details>

#### empty list gives empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
val arr = l.to_array()
expect(arr.len()).to_equal(0)
```

</details>

### concat

#### joins two lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l1 = PersistentList.of([1, 2])
val l2 = PersistentList.of([3, 4])
val joined = l1.concat(l2)
expect(joined.len()).to_equal(4)
expect(joined.head()).to_equal(1)
expect(joined.get(1)).to_equal(2)
expect(joined.get(2)).to_equal(3)
expect(joined.get(3)).to_equal(4)
```

</details>

#### concat with empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l1 = PersistentList.of([1, 2])
val l2 = PersistentList.empty()
val joined = l1.concat(l2)
expect(joined.len()).to_equal(2)
expect(joined.head()).to_equal(1)
```

</details>

#### empty concat with list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l1 = PersistentList.empty()
val l2 = PersistentList.of([3, 4])
val joined = l1.concat(l2)
expect(joined.len()).to_equal(2)
expect(joined.head()).to_equal(3)
```

</details>

#### does not modify originals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l1 = PersistentList.of([1, 2])
val l2 = PersistentList.of([3, 4])
val joined = l1.concat(l2)
expect(l1.len()).to_equal(2)
expect(l2.len()).to_equal(2)
expect(joined.len()).to_equal(4)
```

</details>

### map

#### applies function to each element

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3])
val doubled = l.map(_1 * 2)
expect(doubled.len()).to_equal(3)
expect(doubled.get(0)).to_equal(2)
expect(doubled.get(1)).to_equal(4)
expect(doubled.get(2)).to_equal(6)
```

</details>

#### preserves length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([10, 20, 30])
val result = l.map(_1 + 1)
expect(result.len()).to_equal(3)
```

</details>

#### empty list map is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
val result = l.map(_1 * 2)
expect(result.len()).to_equal(0)
```

</details>

### filter

#### keeps matching elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3, 4, 5])
val evens = l.filter(_1 % 2 == 0)
expect(evens.len()).to_equal(2)
expect(evens.get(0)).to_equal(2)
expect(evens.get(1)).to_equal(4)
```

</details>

#### returns empty when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 3, 5])
val evens = l.filter(_1 % 2 == 0)
expect(evens.len()).to_equal(0)
```

</details>

#### returns all when everything matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([2, 4, 6])
val evens = l.filter(_1 % 2 == 0)
expect(evens.len()).to_equal(3)
```

</details>

### fold

#### accumulates sum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3, 4])
val sum = l.fold(0, \acc, x: acc + x)
expect(sum).to_equal(10)
```

</details>

#### accumulates product

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([1, 2, 3, 4])
val product = l.fold(1, \acc, x: acc * x)
expect(product).to_equal(24)
```

</details>

#### returns init for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.empty()
val result = l.fold(42, \acc, x: acc + x)
expect(result).to_equal(42)
```

</details>

#### single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = PersistentList.of([5])
val result = l.fold(0, \acc, x: acc + x)
expect(result).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/persistent_list_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentList
- empty list
- prepend
- PersistentList__of
- from_array
- get
- contains
- tail
- head
- reverse
- to_array
- concat
- map
- filter
- fold

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
