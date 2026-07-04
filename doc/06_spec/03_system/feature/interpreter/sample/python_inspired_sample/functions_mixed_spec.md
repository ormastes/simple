# Mixed Function Patterns (Interpreter)

> Tests mixed function patterns in the interpreter including nested calls, higher-order functions, and recursive definitions. Verifies that complex function composition and calling conventions work correctly in interpreted mode.

<!-- sdn-diagram:id=functions_mixed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functions_mixed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functions_mixed_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functions_mixed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixed Function Patterns (Interpreter)

Tests mixed function patterns in the interpreter including nested calls, higher-order functions, and recursive definitions. Verifies that complex function composition and calling conventions work correctly in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests mixed function patterns in the interpreter including nested calls, higher-order
functions, and recursive definitions. Verifies that complex function composition
and calling conventions work correctly in interpreted mode.

## Scenarios

### Mixed Function Patterns

#### default parameters

#### uses default when argument omitted

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text, greeting: text = "Hello"):
    "{greeting}, {name}!"
expect greet("Alice") == "Hello, Alice!"
```

</details>

#### overrides default when provided

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text, greeting: text = "Hello"):
    "{greeting}, {name}!"
expect greet("Bob", "Hi") == "Hi, Bob!"
```

</details>

#### named arguments

#### calls with named arguments

1. fn make point
2.
3. expect p ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_point(x: i64, y: i64) -> (i64, i64):
    (x, y)
val p = make_point(x: 10, y: 20)
expect p == (10, 20)
```

</details>

#### higher-order functions

#### passes function as argument

1. fn apply
2. f
3. fn double
4. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)
fn double(n: i64) -> i64:
    n * 2
expect apply(double, 5) == 10
```

</details>

#### uses lambda expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
val doubled = items.map(_ * 2)
expect doubled == [2, 4, 6]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
