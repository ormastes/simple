# SPipe System Test

> Tests to verify the SPipe framework itself is working properly.

<!-- sdn-diagram:id=spipe_system_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spipe_system_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spipe_system_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spipe_system_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe System Test

Tests to verify the SPipe framework itself is working properly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Test Framework Verification |
| Status | Complete |
| Source | `test/01_unit/compiler/backend/spipe_system_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests to verify the SPipe framework itself is working properly.

## Scenarios

### SPipe - Basic Assertions

#### passes with true assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### passes with equality check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 2 == 4
```

</details>

#### passes with string equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello" == "hello"
```

</details>

#### passes with array length

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.len() == 3
```

</details>

### SPipe - Variables and Computation

#### evaluates arithmetic correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
val z = x + y
expect z == 30
```

</details>

#### works with strings

1. expect name len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
expect name.len() == 5
```

</details>

#### works with arrays

1. expect numbers len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5]
expect numbers.len() == 5
expect numbers[0] == 1
expect numbers[4] == 5
```

</details>

### SPipe - Data Structures

#### handles simple classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i32
    y: i32

val p = Point(x: 10, y: 20)
expect p.x == 10
expect p.y == 20
```

</details>

#### handles arrays of classes

1. items push
2. items push
3. expect items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Item:
    name: text
    count: i32

var items: [Item] = []
items.push(Item(name: "apple", count: 5))
items.push(Item(name: "banana", count: 3))

expect items.len() == 2
expect items[0].count == 5
```

</details>

### SPipe - Control Flow

#### supports if statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
var result = 0
if x > 40:
    result = 1
else:
    result = 2
expect result == 1
```

</details>

<details>
<summary>Advanced: supports loops</summary>

#### supports loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in [1, 2, 3, 4, 5]:
    sum = sum + i
expect sum == 15
```

</details>


</details>

### SPipe - Function Calls

#### calls functions correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add(10, 20)
expect result == 30
```

</details>

#### chains function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add(multiply(2, 3), 4)
expect result == 10
```

</details>

### SPipe - Context Blocks

#### when testing math

#### adds numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 + 3 == 8
```

</details>

#### subtracts numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 - 3 == 7
```

</details>

#### when testing strings

#### concatenates strings

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello" + " " + "world"
expect s.len() == 11
```

</details>

### SPipe - Integration Test

#### runs complete calculator workflow

1. calc add
2. calc add
3. expect calc get value
4. calc subtract
5. expect calc get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calc = Calculator(value: 0)
calc.add(10)
calc.add(5)
expect calc.get_value() == 15

calc.subtract(3)
expect calc.get_value() == 12
```

</details>

### SPipe - Enumerations

#### creates enum values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.Red
# Just verify it runs without error
expect true
```

</details>

#### uses enums in collections

1. colors push
2. colors push
3. expect colors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var colors: [Color] = []
colors.push(Color.Red)
colors.push(Color.Blue)
expect colors.len() == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
