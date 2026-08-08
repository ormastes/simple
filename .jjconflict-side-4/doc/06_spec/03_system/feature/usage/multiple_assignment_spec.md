# Multiple Assignment (Destructuring) Specification

> val (x, y) = get_point()

<!-- sdn-diagram:id=multiple_assignment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multiple_assignment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multiple_assignment_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multiple_assignment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiple Assignment (Destructuring) Specification

val (x, y) = get_point()

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MULTIPLE-ASSIGNMENT |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/multiple_assignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Tuple destructuring
val (x, y) = get_point()
val (first, second, ...rest) = items

# Array destructuring
val [a, b, c] = triple

# Struct destructuring
val {name, age} = person
```

## Key Behaviors

- Pattern must match the structure of the value
- Variables are bound in the order they appear
- Wildcards `_` can ignore unwanted values
- Rest patterns `...rest` capture remaining elements

## Scenarios

### Multiple Assignment (Destructuring)

#### tuple destructuring

#### destructures a pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (10, 20)
val a = pair[0]
val b = pair[1]
expect a == 10
expect b == 20
```

</details>

#### destructures a triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = (1, 2, 3)
val x = triple[0]
val y = triple[1]
val z = triple[2]
expect x == 1
expect y == 2
expect z == 3
```

</details>

#### uses destructured values in expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = (3, 4)
val x = point[0]
val y = point[1]
val distance_squared = x * x + y * y
expect distance_squared == 25
```

</details>

#### destructures function return value

1. fn get coordinates
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_coordinates() -> (i64, i64):
    (100, 200)
val _result = get_coordinates()
val x = _result[0]
val y = _result[1]
expect x == 100
expect y == 200
```

</details>

#### tuple destructuring with wildcards

#### ignores first element with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = (1, 2, 3)
# _ = triple[0]  # ignored
val b = triple[1]
val c = triple[2]
expect b == 2
expect c == 3
```

</details>

#### ignores middle element with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = (1, 2, 3)
val a = triple[0]
# _ = triple[1]  # ignored
val c = triple[2]
expect a == 1
expect c == 3
```

</details>

#### ignores last element with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = (1, 2, 3)
val a = triple[0]
val b = triple[1]
# _ = triple[2]  # ignored
expect a == 1
expect b == 2
```

</details>

#### ignores multiple elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quad = (1, 2, 3, 4)
val a = quad[0]
# _ = quad[1]  # ignored
# _ = quad[2]  # ignored
val d = quad[3]
expect a == 1
expect d == 4
```

</details>

#### nested tuple destructuring

#### destructures nested tuples

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = ((1, 2), 3)
val _inner = nested[0]
val a = _inner[0]
val b = _inner[1]
val c = nested[1]
expect a == 1
expect b == 2
expect c == 3
```

</details>

#### destructures deeply nested tuples

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deep = (((1, 2), 3), 4)
val _outer = deep[0]
val _inner = _outer[0]
val a = _inner[0]
val b = _inner[1]
val c = _outer[1]
val d = deep[1]
expect a == 1
expect b == 2
expect c == 3
expect d == 4
```

</details>

#### array destructuring

#### destructures fixed-size array

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val a = arr[0]
val b = arr[1]
val c = arr[2]
expect a == 10
expect b == 20
expect c == 30
```

</details>

#### destructures with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val x = arr[0]
# _ = arr[1]  # ignored
val z = arr[2]
expect x == 1
expect z == 3
```

</details>

#### mutable destructuring

#### creates mutable bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (5, 10)
var a = pair[0]
var b = pair[1]
a = a + 1
b = b + 1
expect a == 6
expect b == 11
```

</details>

#### allows partial mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = (1, 2, 3)
var x = triple[0]
var y = triple[1]
var z = triple[2]
x = x * 10
expect x == 10
expect y == 2
expect z == 3
```

</details>

#### mixed type destructuring

#### destructures tuples with different types

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixed = ("hello", 42)
val name = mixed[0]
val count = mixed[1]
expect name == "hello"
expect count == 42
```

</details>

#### destructures nested mixed types

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = (("Alice", 30), true)
val _inner = data[0]
val name = _inner[0]
val age = _inner[1]
val active = data[1]
expect name == "Alice"
expect age == 30
expect active == true
```

</details>

#### destructuring in loops

<details>
<summary>Advanced: destructures in for loop</summary>

#### destructures in for loop

1. fn sum pairs
2. expect sum pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tuple destructuring inside for loop body is not supported
# in interpreter mode. Use indexed access instead.
val pairs = [(1, 2), (3, 4), (5, 6)]
fn sum_pairs(pairs) -> i64:
    var sum = 0
    for pair in pairs:
        sum = sum + pair[0] + pair[1]
    sum
expect sum_pairs(pairs) == 21
```

</details>


</details>

#### uses destructured values for computation

1. fn sum points
2. expect sum points


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val points = [(0, 0), (3, 4), (6, 8)]
fn sum_points(points) -> i64:
    var total = 0
    for point in points:
        total = total + point[0] + point[1]
    total
expect sum_points(points) == 21
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
