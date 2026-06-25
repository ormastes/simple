# Parser Edge Cases for Operators, Keywords, and Type Syntax

> The Simple parser must handle several non-trivial syntactic forms that are easy to mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor` operator, and bracket-based array type annotations `[T]`. This spec exercises each form in isolation and in combination, verifying correct tokenisation, operator precedence, and type annotation parsing. A `super` keyword test is planned but commented out pending interpreter support for inheritance dispatch.

<!-- sdn-diagram:id=parser_edge_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_edge_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_edge_cases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_edge_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Edge Cases for Operators, Keywords, and Type Syntax

The Simple parser must handle several non-trivial syntactic forms that are easy to mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor` operator, and bracket-based array type annotations `[T]`. This spec exercises each form in isolation and in combination, verifying correct tokenisation, operator precedence, and type annotation parsing. A `super` keyword test is planned but commented out pending interpreter support for inheritance dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-015 |
| Category | Syntax |
| Status | In Progress |
| Source | `test/03_system/feature/usage/parser_edge_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Simple parser must handle several non-trivial syntactic forms that are easy to
mis-parse: the matrix-multiplication operator `@`, the keyword-style bitwise `xor`
operator, and bracket-based array type annotations `[T]`. This spec exercises each
form in isolation and in combination, verifying correct tokenisation, operator
precedence, and type annotation parsing. A `super` keyword test is planned but
commented out pending interpreter support for inheritance dispatch.

## Syntax

```simple
# Matrix multiplication operator (@)
val result = 3 @ 4          # => 12

# Bitwise XOR keyword operator
val bits = 5 xor 3          # => 6

# Array type annotations with square brackets
fn takes_array(items: [i64]) -> [i64]:
return items

# Combined precedence
val c = (a xor b) @ 2       # xor first, then @
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `@` operator | Matrix multiplication infix operator parsed as a binary expression |
| `xor` keyword operator | Bitwise XOR expressed as an alphabetic keyword, not a symbol |
| Array type syntax | `[T]` bracket notation used in parameter and return type positions |
| Operator precedence | Verifies correct evaluation order when `@` and `xor` appear together |

## Scenarios

### Parser Edge Cases

#### Matrix Multiplication Operator

#### parses @ operator in expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3 @ 4
expect result == 12
```

</details>

#### parses @ operator with variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 2
val b = 5
val result = a @ b
expect result == 10
```

</details>

#### Bitwise XOR Keyword

#### parses xor keyword in expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 xor 3
expect result == 6
```

</details>

#### parses xor keyword with variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 12
val b = 7
val result = a xor b
expect result == 11
```

</details>

#### parses xor in complex expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (5 xor 3) xor 1
expect result == 7
```

</details>

#### Array Type Syntax

#### parses array types with square brackets

1. fn takes array
2. expect result length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn takes_array(items: [i64]) -> [i64]:
    return items

val nums = [1, 2, 3]
val result = takes_array(nums)
expect result.length() == 3
```

</details>

#### parses array return types

1. fn make array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_array() -> [text]:
    return ["a", "b", "c"]

val result = make_array()
expect result[0] == "a"
```

</details>

#### Operator Precedence

#### handles @ and xor together

1. expect result == 3  #


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (3 @ 2) xor 5
expect result == 3  # (3 @ 2) = 6, 6 xor 5 = 3
```

</details>

#### handles multiple operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 3
val c = (a xor b) @ 2
expect c == 18  # 10 xor 3 = 9, 9 @ 2 = 18
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
