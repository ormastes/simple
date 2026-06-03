# Array List Ops Specification

## Scenarios

### std.array (list_utils migration)

### array_reverse

#### returns a list of same length

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_reverse([1, 2, 3])
expect(result.len()).to_equal(3)
```

</details>

#### handles empty list

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_reverse([])).to_equal([])
```

</details>

### array_take

#### takes first n elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_take([1, 2, 3, 4, 5], 3)).to_equal([1, 2, 3])
```

</details>

#### returns all if n > length

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_take([1, 2], 5)).to_equal([1, 2])
```

</details>

### array_drop

#### drops first n elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_drop([1, 2, 3, 4, 5], 2)).to_equal([3, 4, 5])
```

</details>

### array_chunk

#### splits into chunks of size

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = array_chunk([1, 2, 3, 4, 5], 2)
expect(chunks.len()).to_equal(3)
expect(chunks[0]).to_equal([1, 2])
expect(chunks[2]).to_equal([5])
```

</details>

### array_windows

#### creates sliding windows

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wins = array_windows([1, 2, 3, 4], 2)
expect(wins.len()).to_equal(3)
expect(wins[0]).to_equal([1, 2])
expect(wins[1]).to_equal([2, 3])
```

</details>

### array_interleave

#### interleaves two lists

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_interleave([1, 3, 5], [2, 4, 6])
expect(result).to_equal([1, 2, 3, 4, 5, 6])
```

</details>

### array_flatten

#### flattens nested lists

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_flatten([[1, 2], [3, 4], [5]])
expect(result).to_equal([1, 2, 3, 4, 5])
```

</details>

### array_intersperse

#### inserts separator between elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_intersperse([1, 2, 3], 0)
expect(result).to_equal([1, 0, 2, 0, 3])
```

</details>

### array_rotate_left

#### rotates list left

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_rotate_left([1, 2, 3, 4], 1)
expect(result).to_equal([2, 3, 4, 1])
```

</details>

### array_rotate_right

#### rotates list right

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_rotate_right([1, 2, 3, 4], 1)
expect(result).to_equal([4, 1, 2, 3])
```

</details>

### array_dedup

#### removes consecutive duplicates

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_dedup([1, 1, 2, 2, 3, 3])
expect(result).to_equal([1, 2, 3])
```

</details>

#### preserves non-consecutive duplicates

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_dedup([1, 2, 1, 2])
expect(result).to_equal([1, 2, 1, 2])
```

</details>

### array_dedup_all

#### removes all duplicates

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_dedup_all([1, 2, 1, 3, 2])
expect(result.len()).to_equal(3)
```

</details>

### array_is_sorted

#### checks if list is sorted

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([1, 2, 3])).to_equal(true)
expect(array_is_sorted([3, 1, 2])).to_equal(false)
expect(array_is_sorted([])).to_equal(true)
```

</details>

### array_equals

#### checks equality

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_equals([1, 2, 3], [1, 2, 3])).to_equal(true)
expect(array_equals([1, 2], [1, 3])).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/array_list_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.array (list_utils migration)
- array_reverse
- array_take
- array_drop
- array_chunk
- array_windows
- array_interleave
- array_flatten
- array_intersperse
- array_rotate_left
- array_rotate_right
- array_dedup
- array_dedup_all
- array_is_sorted
- array_equals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

