# Basic Expressions (Interpreter)

> Tests basic expression evaluation in the interpreter including arithmetic, string operations, and type coercion. Verifies that the interpreter correctly computes expression results matching the compiled output behavior.

<!-- sdn-diagram:id=basic_expressions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_expressions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_expressions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_expressions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Expressions (Interpreter)

Tests basic expression evaluation in the interpreter including arithmetic, string operations, and type coercion. Verifies that the interpreter correctly computes expression results matching the compiled output behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests basic expression evaluation in the interpreter including arithmetic, string
operations, and type coercion. Verifies that the interpreter correctly computes
expression results matching the compiled output behavior.

## Scenarios

### Basic Expressions

#### arithmetic expressions

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 == 5
```

</details>

#### evaluates subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 - 4 == 6
```

</details>

#### evaluates multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 6 * 7 == 42
```

</details>

#### evaluates division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 20 / 4 == 5
```

</details>

#### evaluates modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 17 % 5 == 2
```

</details>

#### respects operator precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 + 3 * 4 == 14
```

</details>

#### comparison expressions

#### compares equality

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (5 == 5) == true
expect (5 == 6) == false
```

</details>

#### compares inequality

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (5 != 6) == true
```

</details>

#### compares less than

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (3 < 5) == true
expect (5 < 3) == false
```

</details>

#### compares greater than

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (5 > 3) == true
```

</details>

#### logical expressions

#### evaluates and

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true && true) == true
expect (true && false) == false
```

</details>

#### evaluates or

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (false || true) == true
expect (false || false) == false
```

</details>

#### evaluates not

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (not true) == false
expect (not false) == true
```

</details>

#### string expressions

#### concatenates strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "hello" + " " + "world"
expect result == "hello world"
```

</details>

#### interpolates values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val msg = "value is {x}"
expect msg == "value is 42"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
