# Placeholder Lambda Expressions

> Placeholder lambdas let the programmer write concise anonymous functions by using `_` as a stand-in for each successive parameter. The compiler desugars `_ * 2` into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec covers the full surface area: comparison operators, arithmetic (including unary negation), method access on the placeholder (`_.len()`), chaining of `filter` and `map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`, `all`). Edge cases for empty and single-element collections are also tested.

<!-- sdn-diagram:id=placeholder_lambda_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=placeholder_lambda_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

placeholder_lambda_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=placeholder_lambda_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Placeholder Lambda Expressions

Placeholder lambdas let the programmer write concise anonymous functions by using `_` as a stand-in for each successive parameter. The compiler desugars `_ * 2` into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec covers the full surface area: comparison operators, arithmetic (including unary negation), method access on the placeholder (`_.len()`), chaining of `filter` and `map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`, `all`). Edge cases for empty and single-element collections are also tested.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-009 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/placeholder_lambda_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Placeholder lambdas let the programmer write concise anonymous functions by using
`_` as a stand-in for each successive parameter. The compiler desugars `_ * 2`
into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec
covers the full surface area: comparison operators, arithmetic (including unary
negation), method access on the placeholder (`_.len()`), chaining of `filter` and
`map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`,
`all`). Edge cases for empty and single-element collections are also tested.

## Syntax

```simple
# Filter with comparison placeholder
val evens = [1, 2, 3, 4, 5].filter(_ % 2 == 0)   # => [2, 4, 6]

# Map with arithmetic placeholder
val doubled = [1, 2, 3].map(_ * 10)                # => [10, 20, 30]

# Unary negation placeholder
val negated = [1, 2, 3].map(-_)                    # => [-1, -2, -3]

# Method call on placeholder
val long = ["hi", "hello", "hey"].filter(_.len() > 3)  # => ["hello"]

# Chained placeholders
val result = [1, 2, 3, 4, 5].filter(_ > 2).map(_ * 2)  # => [6, 8, 10]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Placeholder `_` | Each `_` in an expression becomes a new auto-named lambda parameter |
| Desugaring | `_ op expr` is rewritten to `\__pN: __pN op expr` before evaluation |
| Method access | `_.method()` desugars to `\__p0: __p0.method()` for member calls |
| Chaining | Successive `.filter(_)` and `.map(_)` calls each introduce independent lambdas |

## Scenarios

### Placeholder Lambda

#### filter with comparison

#### filters with less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ < 3)
expect result == [1, 2]
```

</details>

#### filters with greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ > 3)
expect result == [4, 5]
```

</details>

#### filters with less than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ <= 3)
expect result == [1, 2, 3]
```

</details>

#### filters with greater than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ >= 3)
expect result == [3, 4, 5]
```

</details>

#### filters with equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 2, 1]
val result = data.filter(_ == 2)
expect result == [2, 2]
```

</details>

#### filters with not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 2, 1]
val result = data.filter(_ != 2)
expect result == [1, 3, 1]
```

</details>

#### map with arithmetic

#### maps with multiply

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.map(_ * 10)
expect result == [10, 20, 30]
```

</details>

#### maps with add

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.map(_ + 100)
expect result == [101, 102, 103]
```

</details>

#### maps with subtract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [10, 20, 30]
val result = data.map(_ - 5)
expect result == [5, 15, 25]
```

</details>

#### maps with negate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.map(-_)
expect result == [-1, -2, -3]
```

</details>

#### chaining

#### chains filter then map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ > 2).map(_ * 2)
expect result == [6, 8, 10]
```

</details>

#### chains map then filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.map(_ * 2).filter(_ > 5)
expect result == [6, 8, 10]
```

</details>

#### string operations

#### filters strings by length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val words = ["hi", "hello", "hey", "howdy"]
val result = words.filter(_.len() > 3)
expect result == ["hello", "howdy"]
```

</details>

#### complex expressions

#### uses placeholder in modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5, 6]
val result = data.filter(_ % 2 == 0)
expect result == [2, 4, 6]
```

</details>

#### uses placeholder in compound expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data.map(_ * 2 + 1)
expect result == [3, 5, 7, 9, 11]
```

</details>

#### with different collection methods

#### works with any

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data.any(_ > 2)
expect result == true
```

</details>

#### works with all

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [2, 4, 6]
val result = data.all(_ % 2 == 0)
expect result == true
```

</details>

#### works with all returning false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [2, 3, 6]
val result = data.all(_ % 2 == 0)
expect result == false
```

</details>

#### empty collections

#### filter on empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = []
val result = data.filter(_ > 0)
expect result == []
```

</details>

#### map on empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = []
val result = data.map(_ * 2)
expect result == []
```

</details>

#### single element

#### filter matching single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [42]
val result = data.filter(_ == 42)
expect result == [42]
```

</details>

#### filter non-matching single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [42]
val result = data.filter(_ == 0)
expect result == []
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
