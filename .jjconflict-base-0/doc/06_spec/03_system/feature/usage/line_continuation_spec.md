# Line Continuation Specification

> val sum = value1 + \

<!-- sdn-diagram:id=line_continuation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=line_continuation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

line_continuation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=line_continuation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Line Continuation Specification

val sum = value1 + \

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2400 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/line_continuation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Explicit continuation with backslash
val sum = value1 + \
value2 + \
value3

# Function call with continuation
val result = add(1, \
2, \
3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Explicit Continuation | Backslash at line end forces continuation to next line |
| Nesting | Multiple levels of continuation allowed |
| Indentation | Improves readability but not required for continuation |

## Behavior

Line continuation:
- Backslash at end of line continues expression to next line
- Multiple continuations can be chained
- Works in expressions and function calls
- Preserves semantic meaning across line boundaries

## Note

Implicit continuation (just newlines inside parentheses/brackets/braces) is not
currently supported. Use explicit backslash continuation instead.

## Scenarios

### Line Continuation

#### explicit continuation with backslash

#### continues expression with backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 + 2 + \
    3 + 4
expect result == 10
```

</details>

#### continues function call with backslash

1. fn add


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b, c):
    a + b + c
val result = add(1, \
    2, \
    3)
expect result == 6
```

</details>

#### combines backslash and arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = 30
val result = a + \
    b + \
    c
expect result == 60
```

</details>

#### chains multiple continuations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 + \
    2 + \
    3 + \
    4 + \
    5
expect result == 15
```

</details>

#### continuation in various expressions

#### continues binary operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100 + \
    200
expect x == 300
```

</details>

#### continues comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
val result = a < \
    b
var r = 0
if result:
    r = 1
expect r == 1
```

</details>

#### continues string concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello" + \
    " " + \
    "World"
var result = 0
if s == "Hello World":
    result = 1
expect result == 1
```

</details>

#### continuation with indentation

#### works with any indentation level

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + \
            20 + \
    30
expect result == 60
```

</details>

#### continues deeply indented code

1. fn outer
2. fn inner
3. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer():
    fn inner():
        val x = 1 + \
            2
        return x
    return inner()
expect outer() == 3
```

</details>

#### practical examples

#### formats long arithmetic expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 100 + \
    200 + \
    300 + \
    400
expect total == 1000
```

</details>

#### formats function with many arguments

1. fn sum5


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum5(a, b, c, d, e):
    a + b + c + d + e
val result = sum5(1, \
    2, \
    3, \
    4, \
    5)
expect result == 15
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
