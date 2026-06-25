# Interpreter Basics

> Tests fundamental interpreter functionality including expression evaluation, arithmetic operations, comparison operators, boolean logic, and string processing. Verifies that the interpreter correctly handles core language primitives.

<!-- sdn-diagram:id=interpreter_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Basics

Tests fundamental interpreter functionality including expression evaluation, arithmetic operations, comparison operators, boolean logic, and string processing. Verifies that the interpreter correctly handles core language primitives.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/interpreter_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests fundamental interpreter functionality including expression evaluation,
arithmetic operations, comparison operators, boolean logic, and string processing.
Verifies that the interpreter correctly handles core language primitives.

## Scenarios

### Simple Interpreter

#### when evaluating expressions

#### handles arithmetic operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
expect(10 - 3).to_equal(7)
expect(4 * 5).to_equal(20)
expect(15 / 3).to_equal(5)
```

</details>

#### handles comparison operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(5 > 3).to_equal(true)
expect(2 < 10).to_equal(true)
expect(5 == 5).to_equal(true)
expect(3 != 4).to_equal(true)
```

</details>

#### handles boolean operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true and true).to_equal(true)
expect(true and false).to_equal(false)
expect(true or false).to_equal(true)
expect(not false).to_equal(true)
```

</details>

#### when working with strings

#### supports string concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello" + " " + "World"
expect(s).to_equal("Hello World")
```

</details>

#### supports string interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val age = 30
val msg = "Name: {name}, Age: {age}"
expect(msg).to_equal("Name: Alice, Age: 30")
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
