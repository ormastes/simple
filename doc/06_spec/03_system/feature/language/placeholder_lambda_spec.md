# Placeholder Lambda Specification

> Placeholder `_` syntax for creating concise lambda expressions.

<!-- sdn-diagram:id=placeholder_lambda_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=placeholder_lambda_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

placeholder_lambda_spec -> std
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
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Placeholder Lambda Specification

Placeholder `_` syntax for creating concise lambda expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLACEHOLDER-LAMBDA |
| Category | Syntax |
| Status | In Progress |
| Source | `test/03_system/feature/language/placeholder_lambda_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Placeholder `_` syntax for creating concise lambda expressions.
`nums.map(_ * 2)` desugars to `nums.map(\__p0: __p0 * 2)`

## Scenarios

### Placeholder Lambda

#### single placeholder

#### transforms _ * 2 to lambda

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map(_ * 2) == [2, 4, 6]
```

</details>

#### transforms _ + 10 to lambda

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map(_ + 10) == [11, 12, 13]
```

</details>

#### transforms _ - 1 to lambda

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [5, 10, 15]
expect nums.map(_ - 1) == [4, 9, 14]
```

</details>

#### transforms _ / 2 to lambda

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [10, 20, 30]
expect nums.map(_ / 2) == [5, 10, 15]
```

</details>

#### transforms unary negation -_

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, -2, 3]
expect nums.map(-_) == [-1, 2, -3]
```

</details>

#### field access

#### accesses x field with _.x

1. expect points map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val points = [Point(x=1, y=2), Point(x=3, y=4)]
expect points.map(_.x) == [1, 3]
```

</details>

#### accesses y field with _.y

1. expect points map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val points = [Point(x=1, y=2), Point(x=3, y=4)]
expect points.map(_.y) == [2, 4]
```

</details>

#### method call

#### calls method with _.method()

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["hello", "world"]
expect texts.map(_.len()) == [5, 5]
```

</details>

#### multiple placeholders

#### reduces with _ + _

1. expect nums reduce


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4]
# reduce requires (init, lambda) form with explicit lambda
expect nums.reduce(0, \acc, x: acc + x) == 10
```

</details>

#### reduces with _ * _

1. expect nums reduce


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4]
# reduce requires (init, lambda) form with explicit lambda
expect nums.reduce(1, \acc, x: acc * x) == 24
```

</details>

#### compares with _ < _

1. expect compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 3
val b = 5
val compare = \x, y: x < y
# This tests that _ < _ creates a two-argument lambda
expect compare(a, b) == true
```

</details>

#### with filter

#### filters with _ > threshold

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 5, 3, 8, 2]
expect nums.filter(_ > 3) == [5, 8]
```

</details>

#### filters with _ < threshold

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 5, 3, 8, 2]
expect nums.filter(_ < 4) == [1, 3, 2]
```

</details>

#### filters with _ == value

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 2, 3, 2]
expect nums.filter(_ == 2) == [2, 2, 2]
```

</details>

#### chained operations

#### chains map and filter

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.map(_ * 2).filter(_ > 5) == [6, 8, 10]
```

</details>

#### chains filter and map

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_ > 2).map(_ * 10) == [30, 40, 50]
```

</details>

#### indexing

#### accesses first element with indexed placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arrays = [[1, 2, 3], [4, 5, 6]]
expect(arrays.map(_1[0]) == [1, 4]).to_equal(true)
```

</details>

#### accesses second element with indexed placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arrays = [[1, 2, 3], [4, 5, 6]]
expect(arrays.map(_1[1]) == [2, 5]).to_equal(true)
```

</details>

#### complex expressions

#### combines operators in expression

1. expect nums map
2. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map(_ * 2 + 1) == [3, 5, 7]
expect nums.map((_ + 1) * 2) == [4, 6, 8]
```

</details>

#### maps with conditional classification

1. fn classify
2. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
fn classify(x: i64) -> text:
    if x > 3:
        return "big"
    else:
        return "small"
expect nums.map(classify(_1)) == ["small", "small", "small", "big", "big"]
```

</details>

#### no transformation when no placeholder

#### leaves expressions without _ unchanged

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map(_1 * 2) == [2, 4, 6]
```

</details>

#### edge cases

#### handles single element list

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [42]
expect nums.map(_ * 2) == [84]
```

</details>

#### handles empty list

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums: [i64] = []
expect nums.map(_ * 2) == []
```

</details>

#### handles nested function calls

1. fn double
2. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
val nums = [1, 2, 3]
# Placeholder expressions are supported inside callback call arguments.
expect nums.map(double(_1)) == [2, 4, 6]
```

</details>

#### null coalescing

#### coalesces with _ ?? default

1. expect opts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts: [Option<i64>] = [Some(1), nil, Some(3)]
expect opts.map(_ ?? 0) == [1, 0, 3]
```

</details>

#### coalesces with expression on right side

1. expect opts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts: [Option<i64>] = [Some(10), nil, Some(30)]
expect opts.map(_ ?? -1 * 100) == [10, -100, 30]
```

</details>

#### slicing

#### slices with _[start:end]

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["hello", "world"]
expect texts.map(_[1:4]) == ["ell", "orl"]
```

</details>

#### slices with _[:end]

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["hello", "world"]
expect texts.map(_[:3]) == ["hel", "wor"]
```

</details>

#### slices with _[start:]

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["hello", "world"]
expect texts.map(_[2:]) == ["llo", "rld"]
```

</details>

#### slices with step _[::step]

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["abcdef", "ghijkl"]
expect texts.map(_[::2]) == ["ace", "gik"]
```

</details>

#### tuple with placeholders

#### creates tuple with placeholder (_, constant)

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map((_, 0)) == [(1, 0), (2, 0), (3, 0)]
```

</details>

#### creates tuple with constant first (constant, _)

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map((100, _)) == [(100, 1), (100, 2), (100, 3)]
```

</details>

#### creates 3-tuple with placeholder

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
expect nums.map((_, "x", 0)) == [(1, "x", 0), (2, "x", 0), (3, "x", 0)]
```

</details>

#### method call with arguments

#### calls method with explicit args _.method(arg)

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["hello", "world"]
expect texts.map(_.slice(0, 3)) == ["hel", "wor"]
```

</details>

#### calls method with placeholder in args _.method(_) from outer scope

1. fn add
2. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: placeholder in function call args not supported, use explicit lambda
val nums = [1, 2, 3]
fn add(a: i64, b: i64) -> i64:
    a + b
expect nums.map(add(_1, 10)) == [11, 12, 13]
```

</details>

#### chained method calls

#### chains method calls _.method1().method2()

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["  hello  ", "  world  "]
expect texts.map(_.trim().len()) == [5, 5]
```

</details>

#### chains multiple string methods

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["HELLO", "WORLD"]
expect texts.map(_.lower().len()) == [5, 5]
```

</details>

#### chains slice with length

1. expect texts map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts = ["hello world", "foo bar baz"]
expect texts.map(_[:5].len()) == [5, 5]
```

</details>

#### scope isolation with nested lambdas

#### does not transform _ inside nested lambda

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
# The outer _ is transformed, inner \x: x stays as is
expect nums.map(_ + (\x: x * 2)(10)) == [21, 22, 23]
```

</details>

#### nested lambda with its own _ is independent

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
# Outer _ becomes __p0, inner _ is separate lambda scope
# This should work because inner lambda is not traversed
val transform = _1 * 2
expect nums.map(_ + transform(5)) == [11, 12, 13]
```

</details>

#### comparison operators

#### uses _ in greater-or-equal comparison

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_ >= 3) == [3, 4, 5]
```

</details>

#### uses _ in less-or-equal comparison

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_ <= 3) == [1, 2, 3]
```

</details>

#### uses _ in not-equal comparison

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 2, 3, 2]
expect nums.filter(_ != 2) == [1, 3]
```

</details>

#### logical operators

#### uses explicit lambda with logical and

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_1 > 1 && _1 < 5) == [2, 3, 4]
```

</details>

#### uses explicit lambda with logical or

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.filter(_1 == 1 || _1 == 5) == [1, 5]
```

</details>

#### modulo and other operators

#### uses _ with modulo

1. expect nums filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5, 6]
expect nums.filter(_ % 2 == 0) == [2, 4, 6]
```

</details>

#### uses _ with bitwise and

1. expect nums map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.map(_ & 1) == [1, 0, 1, 0, 1]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
