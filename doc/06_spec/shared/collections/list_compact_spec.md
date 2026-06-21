# List Compact Specification

> <details>

<!-- sdn-diagram:id=list_compact_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=list_compact_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

list_compact_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=list_compact_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# List Compact Specification

## Scenarios

### List<Option<T>>.compact()

### basic functionality

#### removes None values and unwraps Some values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [Some(1), nil, Some(2), nil, Some(3)]
val compacted = items.compact()
expect(_len(compacted)).to_equal(3)
expect(_get(compacted, 0)).to_equal(1)
expect(_get(compacted, 1)).to_equal(2)
expect(_get(compacted, 2)).to_equal(3)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = []
val compacted = empty.compact()
expect(_len(compacted)).to_equal(0)
```

</details>

#### handles list with all None values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_none = [nil, nil, nil]
val compacted = all_none.compact()
expect(_len(compacted)).to_equal(0)
```

</details>

#### handles list with all Some values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_some = [Some(1), Some(2), Some(3)]
val compacted = all_some.compact()
expect(_len(compacted)).to_equal(3)
expect(_get(compacted, 0)).to_equal(1)
expect(_get(compacted, 1)).to_equal(2)
expect(_get(compacted, 2)).to_equal(3)
```

</details>

### with different types

#### works with text values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = [Some("hello"), nil, Some("world"), nil]
val compacted = words.compact()
expect(_len(compacted)).to_equal(2)
expect(_get(compacted, 0)).to_equal("hello")
expect(_get(compacted, 1)).to_equal("world")
```

</details>

#### works with nested structures

1. Some
2. Some
3. Some
   - Expected: _len(compacted) equals `3`
   - Expected: _len(c0) equals `2`
   - Expected: _len(c1) equals `2`
   - Expected: _len(c2) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    Some([1, 2]),
    nil,
    Some([3, 4]),
    nil,
    Some([5])
]
val compacted = items.compact()
expect(_len(compacted)).to_equal(3)
val c0 = _get(compacted, 0)
val c1 = _get(compacted, 1)
val c2 = _get(compacted, 2)
expect(_len(c0)).to_equal(2)
expect(_len(c1)).to_equal(2)
expect(_len(c2)).to_equal(1)
```

</details>

### Ruby-style usage

#### chains with map and compact

1. fn map even
   - Expected: _len(result) equals `2`
   - Expected: _get(result, 0) equals `20`
   - Expected: _get(result, 1) equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5]
# Map to Option, filter evens - use helper fn instead of inline fn()
fn map_even(x):
    if x % 2 == 0:
        return Some(x * 10)
    return nil
val mapped = numbers.map(map_even(_1))
val result = mapped.compact()
expect(_len(result)).to_equal(2)
expect(_get(result, 0)).to_equal(20)
expect(_get(result, 1)).to_equal(40)
```

</details>

#### similar to Ruby's compact method

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ruby: [1, nil, 2, nil, 3].compact => [1, 2, 3]
# Simple: [Some(1), nil, Some(2), nil, Some(3)].compact() => [1, 2, 3]
val items = [Some(1), nil, Some(2), nil, Some(3)]
val result = items.compact()
expect(result).to_equal([1, 2, 3])
```

</details>

### performance characteristics

#### creates new list without modifying original

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [Some(1), nil, Some(2)]
val compacted = original.compact()
# Original unchanged
expect(_len(original)).to_equal(3)
# New list created
expect(_len(compacted)).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/collections/list_compact_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- List<Option<T>>.compact()
- basic functionality
- with different types
- Ruby-style usage
- performance characteristics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
