# Combinators Specification

> <details>

<!-- sdn-diagram:id=combinators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=combinators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

combinators_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=combinators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Combinators Specification

## Scenarios

### Combinators

### pmap

#### applies identity function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pmap([1, 2, 3], \x: x)
expect(result).to_equal([1, 2, 3])
```

</details>

#### doubles each element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pmap([1, 2, 3], _1 * 2)
expect(result).to_equal([2, 4, 6])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pmap([], _1 + 1)
expect(result).to_equal([])
```

</details>

### pfilter

#### filters even numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfilter([1, 2, 3, 4, 5, 6], _1 % 2 == 0)
expect(result).to_equal([2, 4, 6])
```

</details>

#### filters with no matches returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfilter([1, 3, 5], _1 % 2 == 0)
expect(result).to_equal([])
```

</details>

#### filters with all matches returns all

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfilter([2, 4, 6], _1 % 2 == 0)
expect(result).to_equal([2, 4, 6])
```

</details>

### pfold

#### sums array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfold([1, 2, 3, 4], 0, \a, x: a + x)
expect(result).to_equal(10)
```

</details>

#### folds empty array returns init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfold([], 42, \a, x: a + x)
expect(result).to_equal(42)
```

</details>

#### multiplies array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfold([1, 2, 3, 4], 1, \a, x: a * x)
expect(result).to_equal(24)
```

</details>

### pzip

#### zips two equal-length arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pzip([1, 2, 3], [4, 5, 6])
expect(result.len()).to_equal(3)
expect(result[0]).to_equal([1, 4])
expect(result[1]).to_equal([2, 5])
expect(result[2]).to_equal([3, 6])
```

</details>

#### truncates to shorter array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pzip([1, 2], [10, 20, 30])
expect(result.len()).to_equal(2)
```

</details>

#### handles empty first array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pzip([], [1, 2, 3])
expect(result.len()).to_equal(0)
```

</details>

### pflat_map

#### flattens mapped arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pflat_map([1, 2, 3], [_1, _1 * 10])
expect(result).to_equal([1, 10, 2, 20, 3, 30])
```

</details>

#### handles empty inner arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pflat_map([1, 2, 3], \_: [])
expect(result).to_equal([])
```

</details>

### pgroup_by

#### groups by modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pgroup_by([1, 2, 3, 4, 5, 6], _1 % 2)
expect(result.len()).to_equal(2)
# First group is odd (1 % 2 == 1), second is even (2 % 2 == 0)
expect(result[0][0]).to_equal(1)
expect(result[0][1]).to_equal([1, 3, 5])
expect(result[1][0]).to_equal(0)
expect(result[1][1]).to_equal([2, 4, 6])
```

</details>

#### single group for constant key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pgroup_by([10, 20, 30], \_: "all")
expect(result.len()).to_equal(1)
expect(result[0][1]).to_equal([10, 20, 30])
```

</details>

### ppartition

#### splits into matching and non-matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ppartition([1, 2, 3, 4, 5], _1 > 3)
expect(result[0]).to_equal([4, 5])
expect(result[1]).to_equal([1, 2, 3])
```

</details>

#### all matching gives empty non-matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ppartition([10, 20], _1 > 0)
expect(result[0]).to_equal([10, 20])
expect(result[1]).to_equal([])
```

</details>

### ptake_while

#### takes elements while predicate holds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ptake_while([1, 2, 3, 10, 4, 5], _1 < 5)
expect(result).to_equal([1, 2, 3])
```

</details>

#### takes all if predicate always true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ptake_while([1, 2, 3], _1 > 0)
expect(result).to_equal([1, 2, 3])
```

</details>

#### takes none if first element fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ptake_while([10, 1, 2], _1 < 5)
expect(result).to_equal([])
```

</details>

### pdrop_while

#### drops elements while predicate holds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pdrop_while([1, 2, 3, 10, 4], _1 < 5)
expect(result).to_equal([10, 4])
```

</details>

#### drops all if predicate always true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pdrop_while([1, 2, 3], _1 > 0)
expect(result).to_equal([])
```

</details>

#### drops none if first element fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pdrop_while([10, 1, 2], _1 < 5)
expect(result).to_equal([10, 1, 2])
```

</details>

### pscan

#### returns intermediate accumulator values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pscan([1, 2, 3, 4], 0, \a, x: a + x)
expect(result).to_equal([1, 3, 6, 10])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pscan([5], 0, \a, x: a + x)
expect(result).to_equal([5])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pscan([], 0, \a, x: a + x)
expect(result).to_equal([])
```

</details>

### pany

#### returns true if any element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pany([1, 2, 3], _1 == 2)
expect(result).to_equal(true)
```

</details>

#### returns false if no element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pany([1, 2, 3], _1 == 10)
expect(result).to_equal(false)
```

</details>

#### returns false for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pany([], _1 == 1)
expect(result).to_equal(false)
```

</details>

### pall

#### returns true if all elements match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pall([2, 4, 6], _1 % 2 == 0)
expect(result).to_equal(true)
```

</details>

#### returns false if any element fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pall([2, 3, 6], _1 % 2 == 0)
expect(result).to_equal(false)
```

</details>

#### returns true for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pall([], _1 > 0)
expect(result).to_equal(true)
```

</details>

### pfind

#### returns first matching element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfind([1, 2, 3, 4], _1 > 2)
expect(result).to_equal(3)
```

</details>

#### returns nil when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfind([1, 2, 3], _1 > 10)
expect(result).to_be_nil()
```

</details>

### pfind_index

#### returns index of first match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfind_index([10, 20, 30], _1 == 20)
expect(result).to_equal(1)
```

</details>

#### returns -1 when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pfind_index([1, 2, 3], _1 == 99)
expect(result).to_equal(-1)
```

</details>

### pdistinct

#### removes duplicates preserving order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pdistinct([1, 2, 3, 2, 1, 4])
expect(result).to_equal([1, 2, 3, 4])
```

</details>

#### handles already unique array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pdistinct([5, 10, 15])
expect(result).to_equal([5, 10, 15])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pdistinct([])
expect(result).to_equal([])
```

</details>

### pchunk

#### splits into equal chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pchunk([1, 2, 3, 4, 5, 6], 2)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal([1, 2])
expect(result[1]).to_equal([3, 4])
expect(result[2]).to_equal([5, 6])
```

</details>

#### last chunk may be smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pchunk([1, 2, 3, 4, 5], 3)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal([1, 2, 3])
expect(result[1]).to_equal([4, 5])
```

</details>

#### chunk size larger than array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pchunk([1, 2], 10)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal([1, 2])
```

</details>

### Pipeline creation

#### creates empty pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new()
expect(p.len()).to_equal(0)
expect(p.is_empty()).to_equal(true)
```

</details>

#### Pipeline__of creates from steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.of([])
expect(p.is_empty()).to_equal(true)
```

</details>

### Pipeline map

#### applies map step

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().map(_1 * 2)
val result = p.run([1, 2, 3])
expect(result).to_equal([2, 4, 6])
```

</details>

#### has one step after map

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().map(_1)
expect(p.len()).to_equal(1)
```

</details>

### Pipeline filter

#### applies filter step

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().filter(_1 > 2)
val result = p.run([1, 2, 3, 4, 5])
expect(result).to_equal([3, 4, 5])
```

</details>

### Pipeline chaining

#### chains map then filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().map(_1 * 2).filter(_1 > 4)
val result = p.run([1, 2, 3, 4])
expect(result).to_equal([6, 8])
```

</details>

#### chains filter then map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().filter(_1 > 2).map(_1 * 10)
val result = p.run([1, 2, 3, 4])
expect(result).to_equal([30, 40])
```

</details>

#### has correct step count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().map(_1).filter(\_: true).map(_1)
expect(p.len()).to_equal(3)
```

</details>

### Pipeline take and drop

#### takes first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().take(3)
val result = p.run([10, 20, 30, 40, 50])
expect(result).to_equal([10, 20, 30])
```

</details>

#### drops first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().drop(2)
val result = p.run([10, 20, 30, 40, 50])
expect(result).to_equal([30, 40, 50])
```

</details>

#### take more than length returns all

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().take(100)
val result = p.run([1, 2])
expect(result).to_equal([1, 2])
```

</details>

### Pipeline flat_map

#### maps and flattens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().flat_map([_1, _1])
val result = p.run([1, 2, 3])
expect(result).to_equal([1, 1, 2, 2, 3, 3])
```

</details>

### Pipeline distinct

#### removes duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().distinct()
val result = p.run([1, 2, 1, 3, 2])
expect(result).to_equal([1, 2, 3])
```

</details>

### Pipeline chunk

#### splits into chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().chunk(2)
val result = p.run([1, 2, 3, 4])
expect(result.len()).to_equal(2)
expect(result[0]).to_equal([1, 2])
expect(result[1]).to_equal([3, 4])
```

</details>

### Pipeline run on empty

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pipeline.new().map(_1 * 2).filter(_1 > 0)
val result = p.run([])
expect(result).to_equal([])
```

</details>

### Pipeline immutability

#### builder returns new pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Pipeline.new()
val p2 = p1.map(_1 * 2)
expect(p1.len()).to_equal(0)
expect(p2.len()).to_equal(1)
```

</details>

#### original pipeline unchanged after chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = Pipeline.new().filter(_1 > 0)
val extended = base.map(_1 * 10)
expect(base.len()).to_equal(1)
expect(extended.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/immut/combinators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Combinators
- pmap
- pfilter
- pfold
- pzip
- pflat_map
- pgroup_by
- ppartition
- ptake_while
- pdrop_while
- pscan
- pany
- pall
- pfind
- pfind_index
- pdistinct
- pchunk
- Pipeline creation
- Pipeline map
- Pipeline filter
- Pipeline chaining
- Pipeline take and drop
- Pipeline flat_map
- Pipeline distinct
- Pipeline chunk
- Pipeline run on empty
- Pipeline immutability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
