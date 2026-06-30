# Types Specification

> <details>

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
types_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### MatchSpan

#### reports start/end and derives length without drift

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MatchSpan.of(3, 8)
expect(m.start()).to_equal(3)
expect(m.end()).to_equal(8)
expect(m.length()).to_equal(5)
```

</details>

#### at_len builds end = start + length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MatchSpan.at_len(10, 4)
expect(m.start()).to_equal(10)
expect(m.end()).to_equal(14)
expect(m.length()).to_equal(4)
```

</details>

#### contains is half-open [start, end)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MatchSpan.of(2, 5)
expect(m.contains(2)).to_equal(true)
expect(m.contains(4)).to_equal(true)
expect(m.contains(5)).to_equal(false)
expect(m.contains(1)).to_equal(false)
```

</details>

#### empty span has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MatchSpan.of(7, 7)
expect(m.is_empty()).to_equal(true)
expect(m.length()).to_equal(0)
```

</details>

### MatchPos

#### carries a typed index and compares by value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = MatchPos.at(12)
val b = MatchPos.at(12)
val c = MatchPos.at(13)
expect(a.value()).to_equal(12)
expect(a.equals(b)).to_equal(true)
expect(a.equals(c)).to_equal(false)
```

</details>

### Score

#### orders by raw fixed-point value (higher is better)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lo = Score.from_count(2)
val hi = Score.from_count(5)
expect(hi.is_greater_than(lo)).to_equal(true)
expect(lo.is_less_than(hi)).to_equal(true)
expect(hi.is_less_than(lo)).to_equal(false)
```

</details>

#### cmp returns -1 / 0 / +1 as a sort key

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Score.from_milli(1500)
val b = Score.from_milli(1500)
val c = Score.from_milli(2000)
expect(a.cmp(b)).to_equal(0)
expect(a.cmp(c)).to_equal(0 - 1)
expect(c.cmp(a)).to_equal(1)
```

</details>

#### max picks the higher score

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Score.from_count(3)
val b = Score.from_count(7)
expect(a.max(b).raw_value()).to_equal(7000)
```

</details>

#### from_count scales by FIXED_ONE (1000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Score.from_count(4).raw_value()).to_equal(4000)
```

</details>

### PostingList<Id> generic sorted-merge (AC-7)

#### intersect matches a hand-computed oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Oracle: [1,3,5,7,9] INTERSECT [3,4,5,6,9] == [3,5,9]
val a = PostingList.of([1, 3, 5, 7, 9])
val b = PostingList.of([3, 4, 5, 6, 9])
val r = a.intersect(b)
expect(r.len()).to_equal(3)
expect(r.at(0)).to_equal(3)
expect(r.at(1)).to_equal(5)
expect(r.at(2)).to_equal(9)
```

</details>

#### intersect of disjoint lists is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Oracle: [1,2,3] INTERSECT [4,5,6] == []
val a = PostingList.of([1, 2, 3])
val b = PostingList.of([4, 5, 6])
val r = a.intersect(b)
expect(r.is_empty()).to_equal(true)
expect(r.len()).to_equal(0)
```

</details>

#### union deduplicates and stays sorted vs oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Oracle: [1,3,5] UNION [2,3,4,6] == [1,2,3,4,5,6]
val a = PostingList.of([1, 3, 5])
val b = PostingList.of([2, 3, 4, 6])
val r = a.union(b)
expect(r.len()).to_equal(6)
expect(r.at(0)).to_equal(1)
expect(r.at(1)).to_equal(2)
expect(r.at(2)).to_equal(3)
expect(r.at(3)).to_equal(4)
expect(r.at(4)).to_equal(5)
expect(r.at(5)).to_equal(6)
```

</details>

#### union with empty is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Oracle: [10,20] UNION [] == [10,20]
val a = PostingList.of([10, 20])
val b: PostingList<i64> = PostingList.new()
val r = a.union(b)
expect(r.len()).to_equal(2)
expect(r.at(0)).to_equal(10)
expect(r.at(1)).to_equal(20)
```

</details>

#### me push builds a list then merges

- var a: PostingList<i64> = PostingList new
- a push
- a push
- a push
   - Expected: r.len() equals `2`
   - Expected: r.at(0) equals `4`
   - Expected: r.at(1) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: PostingList<i64> = PostingList.new()
a.push(2)
a.push(4)
a.push(8)
val b = PostingList.of([4, 8, 16])
# Oracle: [2,4,8] INTERSECT [4,8,16] == [4,8]
val r = a.intersect(b)
expect(r.len()).to_equal(2)
expect(r.at(0)).to_equal(4)
expect(r.at(1)).to_equal(8)
```

</details>

#### advance_to skip-cursor leaps to first id >= target

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = PostingList.of([1, 4, 9, 16, 25])
# first id >= 10 is 16, at index 3
expect(a.advance_to(0, 10)).to_equal(3)
# first id >= 1 is 1, at index 0
expect(a.advance_to(0, 1)).to_equal(0)
# nothing >= 100 -> len()
expect(a.advance_to(0, 100)).to_equal(5)
```

</details>

### Haystack / Pattern barrier

#### find_from locates the first matching byte at/after a cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = Haystack.new([65u8, 66u8, 67u8, 66u8, 68u8])
expect(h.find_from(0, 66u8)).to_equal(1)
expect(h.find_from(2, 66u8)).to_equal(3)
expect(h.find_from(0, 90u8)).to_equal(0 - 1)
```

</details>

#### matches_at verifies a pattern at a position

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = Haystack.new([97u8, 98u8, 99u8, 98u8, 99u8])
val p = Pattern.new([98u8, 99u8])
expect(h.matches_at(1, p)).to_equal(true)
expect(h.matches_at(3, p)).to_equal(true)
expect(h.matches_at(0, p)).to_equal(false)
```

</details>

#### Pattern skip table gives a shift >= 1 for any byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pattern.new([97u8, 98u8, 99u8])
# 'a'(97) last occurs at index 0 of len-3 -> shift = 3-1-0 = 2
expect(p.skip_for(97u8)).to_equal(2)
# unseen byte -> full pattern length
expect(p.skip_for(120u8)).to_equal(3)
```

</details>

### Embedding<D> fixed-point path

#### dot_fixed computes integer dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: Embedding<i64> = Embedding.from_fixed([1, 2, 3])
val y: Embedding<i64> = Embedding.from_fixed([4, 5, 6])
# 1*4 + 2*5 + 3*6 = 32
expect(x.dot_fixed(y)).to_equal(32)
```

</details>

#### l2_sq_fixed computes squared norm

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: Embedding<i64> = Embedding.from_fixed([3, 4])
# 9 + 16 = 25
expect(x.l2_sq_fixed()).to_equal(25)
expect(x.dimension()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MatchSpan
- MatchPos
- Score
- PostingList<Id> generic sorted-merge (AC-7)
- Haystack / Pattern barrier
- Embedding<D> fixed-point path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
