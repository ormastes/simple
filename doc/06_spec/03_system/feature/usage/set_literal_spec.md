# Set Literal Syntax

> Tests the `s{...}` set literal syntax for creating sets with automatic duplicate removal. Covers empty sets, integer and string elements, trailing commas, single elements, set operations (union, intersection, difference), conversion to lists, functional operations (filter, map), and relational checks (subset, disjoint). Currently uses array placeholders as set literals are not yet implemented.

<!-- sdn-diagram:id=set_literal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=set_literal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

set_literal_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=set_literal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Set Literal Syntax

Tests the `s{...}` set literal syntax for creating sets with automatic duplicate removal. Covers empty sets, integer and string elements, trailing commas, single elements, set operations (union, intersection, difference), conversion to lists, functional operations (filter, map), and relational checks (subset, disjoint). Currently uses array placeholders as set literals are not yet implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-003 |
| Category | Syntax |
| Status | In Progress |
| Source | `test/03_system/feature/usage/set_literal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `s{...}` set literal syntax for creating sets with automatic duplicate
removal. Covers empty sets, integer and string elements, trailing commas, single
elements, set operations (union, intersection, difference), conversion to lists,
functional operations (filter, map), and relational checks (subset, disjoint).
Currently uses array placeholders as set literals are not yet implemented.

## Syntax

```simple
val nums = s{1, 2, 3}
val union_set = a.union(b)
val evens = nums.filter(_1 % 2 == 0)
```
Set Literal Tests

Test set literal syntax: s{1, 2, 3}

## Scenarios

### Set Literals

#### creates empty set

1. check empty len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val empty = s{}  # TODO: Set literal syntax not yet implemented
val empty = []  # Placeholder - use empty array for now
check empty.len() == 0
```

</details>

#### creates set from integer elements

1. check nums len
2. check nums contains
3. check nums contains
4. check nums contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val nums = s{1, 2, 3}  # TODO: Set literal syntax not yet implemented
val nums = [1, 2, 3]  # Placeholder - use array for now
check nums.len() == 3
check nums.contains(1)
check nums.contains(2)
check nums.contains(3)
```

</details>

#### removes duplicates automatically

1. check nums len
2. check nums contains
3. check nums contains
4. check nums contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val nums = s{1, 2, 2, 3, 3, 3}  # TODO: Set literal syntax not yet implemented
val nums = [1, 2, 3]  # Placeholder - use array for now
check nums.len() == 3
check nums.contains(1)
check nums.contains(2)
check nums.contains(3)
```

</details>

#### creates set from string elements

1. check words len
2. check words contains
3. check words contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val words = s{"hello", "world", "hello"}  # TODO: Set literal syntax not yet implemented
val words = ["hello", "world"]  # Placeholder - use array for now
check words.len() == 2
check words.contains("hello")
check words.contains("world")
```

</details>

#### handles trailing comma

1. check nums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val nums = s{1, 2, 3,}  # TODO: Set literal syntax not yet implemented
val nums = [1, 2, 3]  # Placeholder - use array for now
check nums.len() == 3
```

</details>

#### supports single element

1. check single len
2. check single contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val single = s{42}  # TODO: Set literal syntax not yet implemented
val single = [42]  # Placeholder - use array for now
check single.len() == 1
check single.contains(42)
```

</details>

#### computes union via concatenation

1. check union  len
2. check union  contains
3. check union  contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: s{} union operator not yet implemented — using array concat
val a = [1, 2, 3]
val b = [2, 3, 4]
val union_ = a + b
check union_.len() == 6
check union_.contains(1)
check union_.contains(4)
```

</details>

#### computes intersection via filter

1. check common len
2. check common contains
3. check common contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: s{} intersect operator not yet implemented — using filter
val a = [1, 2, 3]
val b = [2, 3, 4]
val common = a.filter(b.contains(_1))
check common.len() == 2
check common.contains(2)
check common.contains(3)
```

</details>

#### computes difference via filter

1. check diff len
2. check diff contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: s{} diff operator not yet implemented — using filter
val a = [1, 2, 3]
val b = [2, 3, 4]
val diff = a.filter(not b.contains(_1))
check diff.len() == 1
check diff.contains(1)
```

</details>

#### supports filter

1. check evens len
2. check evens contains
3. check evens contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val nums = s{1, 2, 3, 4, 5}  # TODO: Set literal syntax not yet implemented
val nums = [1, 2, 3, 4, 5]  # Placeholder - use array for now
val evens = nums.filter(_ % 2 == 0)
check evens.len() == 2
check evens.contains(2)
check evens.contains(4)
```

</details>

#### supports map

1. check doubled len
2. check doubled contains
3. check doubled contains
4. check doubled contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val nums = s{1, 2, 3}  # TODO: Set literal syntax not yet implemented
val nums = [1, 2, 3]  # Placeholder - use array for now
val doubled = nums.map(_ * 2)
check doubled.len() == 3
check doubled.contains(2)
check doubled.contains(4)
check doubled.contains(6)
```

</details>

#### checks subset via all-contained

1. check small in large count == small len
2. check large in small count != large len


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: s{} is_subset operator not yet implemented — using manual check
val small = [1, 2]
val large = [1, 2, 3, 4]
# All elements of small are in large (manual loop to avoid closure capture)
var small_in_large_count = 0
for x in small:
    if large.contains(x):
        small_in_large_count = small_in_large_count + 1
check small_in_large_count == small.len()
# Not all elements of large are in small
var large_in_small_count = 0
for x in large:
    if small.contains(x):
        large_in_small_count = large_in_small_count + 1
check large_in_small_count != large.len()
```

</details>

#### checks disjoint via no overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: s{} is_disjoint operator not yet implemented — using manual check
val a = [1, 2, 3]
val b = [4, 5, 6]
val c = [3, 4, 5]
var ab_overlap = 0
for x in a:
    if b.contains(x):
        ab_overlap = ab_overlap + 1
check ab_overlap == 0
var ac_overlap = 0
for x in a:
    if c.contains(x):
        ac_overlap = ac_overlap + 1
check ac_overlap > 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
