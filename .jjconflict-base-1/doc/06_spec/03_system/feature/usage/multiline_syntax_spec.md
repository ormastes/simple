# Multi-line Syntax Specification

> Tests for multi-line syntax patterns including function calls spanning multiple lines, array literals, and continuation lines.

<!-- sdn-diagram:id=multiline_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multiline_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multiline_syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multiline_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-line Syntax Specification

Tests for multi-line syntax patterns including function calls spanning multiple lines, array literals, and continuation lines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MULTI-001 |
| Category | Language \| Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/multiline_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for multi-line syntax patterns including function calls spanning
multiple lines, array literals, and continuation lines.

## Syntax

```simple
# Multi-line function call
val result = function_name(
arg1,
arg2,
arg3
)

# Multi-line array
val items = [
1,
2,
3
]

# Line continuation with backslash
val sum = 1 + 2 + \
3 + 4
```

## Scenarios

### Multi-line Function Calls

#### basic multi-line calls

#### calls function with arguments on multiple lines

1. fn add


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    return a + b

val result = add(
    1,
    2
)
expect result == 3
```

</details>

#### calls function with named arguments on multiple lines

1. fn greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name, msg):
    return 42

val result = greet(
    name: "test",
    msg: "hello"
)
expect result == 42
```

</details>

#### nested function calls

#### nests function calls on single line

1. fn inner
2. fn outer
3. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inner(x):
    return x * 2

fn outer(a, b):
    return a + b

expect outer(inner(5), inner(3)) == 16
```

</details>

#### nests function calls on multiple lines

1. fn inner
2. fn outer
3. inner
4. inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inner(x):
    return x * 2

fn outer(a, b):
    return a + b

val result = outer(
    inner(5),
    inner(3)
)
expect result == 16
```

</details>

### Multi-line Literals

#### creates multi-line array literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [
    1,
    2,
    3
]
expect arr[0] + arr[1] + arr[2] == 6
```

</details>

#### creates multi-line struct initialization

1. fn Config new


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Config:
    name: str
    value: i64

fn Config_new(name, value):
    return Config { name: name, value: value }

val c = Config_new(
    "test",
    42
)
expect c.value == 42
```

</details>

### Continuation Lines

#### continues function call to next line

1. fn match exception


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn match_exception(a, b, c):
    return 42

val result = match_exception("ValueError", "some message",
                   "expected")
expect result == 42
```

</details>

#### continues call at same indent level

1. fn match exception


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn match_exception(a, b, c):
    return 42

val result = match_exception("ValueError", "some message",
```

</details>

### Tuple Destructuring in Assignments

#### destructures tuple from array element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [(10, 20)]
val _pair = arr[0]
val a = _pair[0]
val b = _pair[1]
expect a + b == 30
```

</details>

#### accesses tuple elements with dot notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [(10, 20)]
expect arr[0].0 + arr[0].1 == 30
```

</details>

#### destructures nested tuple data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docstrings = [("content", 1), ("other", 2)]
val _pair = docstrings[0]
val content = _pair[0]
val line = _pair[1]
expect line == 1
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
