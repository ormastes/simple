# Lambdas and Closures Specification

> 1. expect double

<!-- sdn-diagram:id=lambdas_closures_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lambdas_closures_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lambdas_closures_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lambdas_closures_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lambdas and Closures Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2300 |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/lambdas_closures_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lambda | Anonymous function defined inline with `\` syntax |
| Closure | Function that captures variables from enclosing scope |
| Higher-Order Function | Function taking or returning other functions |

## Scenarios

### Basic Lambdas

#### creates simple lambda

1. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
expect double(21) == 42
```

</details>

#### creates lambda with multiple params

1. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add = \x, y: x + y
expect add(15, 27) == 42
```

</details>

#### creates lambda with no params

1. expect answer


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val answer = \: 42
expect answer() == 42
```

</details>

#### invokes lambda immediately

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (\x: x + 5)(37)
expect result == 42
```

</details>

### Closures

#### captures outer variable

1. expect multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiplier = 10
val multiply = \x: x * multiplier
expect multiply(4) == 40
```

</details>

#### captures multiple variables

1. expect calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val calc = \x: x * a + b
expect calc(3) == 35
```

</details>

#### nested lambda calls

1. expect add one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
val add_one = \x: x + 1
expect add_one(double(20)) == 41
```

</details>

### Lambdas with Collections

#### maps with lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3]
val doubled = numbers.map(_ * 2)
expect doubled[0] == 2
expect doubled[1] == 4
expect doubled[2] == 6
```

</details>

#### filters with lambda

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5, 6]
val evens = numbers.filter(_ % 2 == 0)
expect evens.len() == 3
```

</details>

#### reduces with lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4]
val sum = numbers.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

### Lambda Edge Cases

#### lambda returning lambda

1. fn make adder
2. expect add five


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_adder(n):
    return \x: x + n
val add_five = make_adder(5)
expect add_five(10) == 15
```

</details>

#### lambda as function parameter

1. fn apply
2. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f, x):
    return f(x)
expect apply(\x: x * 2, 21) == 42
```

</details>

#### lambda with conditional

1. expect abs
2. expect abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abs = \x: if x < 0: -x else: x
expect abs(-5) == 5
expect abs(5) == 5
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
