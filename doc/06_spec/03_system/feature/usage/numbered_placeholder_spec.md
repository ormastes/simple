# Numbered Placeholder Lambda Expressions

> Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit parameter ordering in lambda shorthand. Covers basic single-parameter usage with map and filter, method calls on numbered placeholders, compound arithmetic expressions, edge cases (empty collections, single elements), and chaining filter/map operations with numbered placeholders.

<!-- sdn-diagram:id=numbered_placeholder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numbered_placeholder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numbered_placeholder_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numbered_placeholder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numbered Placeholder Lambda Expressions

Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit parameter ordering in lambda shorthand. Covers basic single-parameter usage with map and filter, method calls on numbered placeholders, compound arithmetic expressions, edge cases (empty collections, single elements), and chaining filter/map operations with numbered placeholders.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/numbered_placeholder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit
parameter ordering in lambda shorthand. Covers basic single-parameter usage with map
and filter, method calls on numbered placeholders, compound arithmetic expressions,
edge cases (empty collections, single elements), and chaining filter/map operations
with numbered placeholders.

## Scenarios

### Numbered Placeholder Lambda

#### basic numbered placeholders

#### uses _1 as single param

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.map(_1 * 10)
expect(result).to_equal([10, 20, 30])
```

</details>

#### uses _1 in filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_1 > 3)
expect(result).to_equal([4, 5])
```

</details>

#### uses _1 with addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [10, 20, 30]
val result = data.map(_1 + 5)
expect(result).to_equal([15, 25, 35])
```

</details>

#### two numbered params

#### uses _1 and _2 in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [10, 20, 30]
val result = nums.map(_1 * 2)
expect(result).to_equal([20, 40, 60])
```

</details>

#### numbered with method calls

#### calls method on _1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hi", "hello", "hey"]
val result = words.filter(_1.len() > 2)
expect(result).to_equal(["hello", "hey"])
```

</details>

#### numbered in compound expressions

#### uses _1 in modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5, 6]
val result = data.filter(_1 % 2 == 0)
expect(result).to_equal([2, 4, 6])
```

</details>

#### uses _1 in compound arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.map(_1 * 3 + 1)
expect(result).to_equal([4, 7, 10])
```

</details>

#### edge cases

#### numbered on empty collection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = []
val result = data.filter(_1 > 0)
expect(result).to_equal([])
```

</details>

#### numbered on single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [42]
val result = data.map(_1 + 8)
expect(result).to_equal([50])
```

</details>

#### numbered with collection methods

#### works with any

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.any(_1 > 2)
expect(result).to_equal(true)
```

</details>

#### works with all

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [2, 4, 6]
val result = data.all(_1 % 2 == 0)
expect(result).to_equal(true)
```

</details>

#### chaining numbered placeholders

#### chains filter then map with numbered

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val filtered = data.filter(_1 > 2)
val result = filtered.map(_1 * 2)
expect(result).to_equal([6, 8, 10])
```

</details>

#### chains map then filter with numbered

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val mapped = data.map(_1 * 2)
val result = mapped.filter(_1 > 5)
expect(result).to_equal([6, 8, 10])
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
