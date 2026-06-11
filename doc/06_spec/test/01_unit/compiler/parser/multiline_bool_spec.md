# Multiline Bool Specification

> <details>

<!-- sdn-diagram:id=multiline_bool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multiline_bool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multiline_bool_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multiline_bool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline Bool Specification

## Scenarios

### Multiline Boolean Expressions

#### allows simple multiline and in parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (true and
    true)
expect(result).to_equal(true)
```

</details>

#### allows multiline and with false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (true and
    false)
expect(result).to_equal(false)
```

</details>

#### allows multiline or in parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (false or
    true)
expect(result).to_equal(true)
```

</details>

#### allows three-way and expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (true and
    true and
    true)
expect(result).to_equal(true)
```

</details>

#### allows three-way mixed expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = false
val c = true
val ab = (a and b)
val result = (ab or c)
expect(result).to_equal(true)
```

</details>

#### allows nested parentheses with multiline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (true and (false or
    true))
expect(result).to_equal(true)
```

</details>

#### allows complex nested expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = (false or true)
val middle = (true and inner)
val result = (true and middle)
expect(result).to_equal(true)
```

</details>

#### works in if statement condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = true
val c = true
var result = false
if (a and
    b and
    c):
    result = true
expect(result).to_equal(true)
```

</details>

#### works with comparison operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val result = (x > 3 and
    x < 10)
expect(result).to_equal(true)
```

</details>

#### works with function calls

1. fn is positive
2. fn is even
3. is even
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_positive(n: i64) -> bool:
    n > 0
fn is_even(n: i64) -> bool:
    n % 2 == 0
val n = 4
val result = (is_positive(n) and
    is_even(n))
expect(result).to_equal(true)
```

</details>

#### allows multiline with not operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (not false and
    true)
expect(result).to_equal(true)
```

</details>

#### allows four-level deep nesting

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = (true or false)
val c = (false and d)
val b = (true or c)
val result = (true and b)
expect(result).to_equal(true)
```

</details>

#### works with multiple conditions in while

1. fn run while
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_while() -> i64:
    var count = 0
    var i = 0
    while (i < 5 and
        count < 10):
        count = count + 1
        i = i + 1
    count
val count = run_while()
expect(count).to_equal(5)
```

</details>

#### works in if with multiline condition in match case

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val in_range = (x > 5 and x < 15)
var result = "other"
if x == 10:
    if in_range:
        result = "yes"
    else:
        result = "no"
expect(result).to_equal("yes")
```

</details>

#### works with string comparisons

1. name len
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val result = (name == "Alice" and
    name.len() > 3)
expect(result).to_equal(true)
```

</details>

#### allows very long multiline expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = (a and a and a and a)
val result = (b and a and a and a)
expect(result).to_equal(true)
```

</details>

#### works with array membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
val x = 3
val result = (x in items and
    x > 0)
expect(result).to_equal(true)
```

</details>

#### works with null coalescing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val maybe = x
val lo = (maybe ?? 0 > 0)
val hi = (maybe ?? 0 < 10)
val result = (lo and hi)
expect(result).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/multiline_bool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multiline Boolean Expressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
