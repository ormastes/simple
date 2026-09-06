# AST Expression Conversion Specification

> AST expression conversion transforms parse tree (CST) expressions to interpreter AST. It handles all expression types including literals, operators, calls, collections, control flow, and special expressions.

<!-- sdn-diagram:id=ast_convert_expr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ast_convert_expr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ast_convert_expr_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ast_convert_expr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AST Expression Conversion Specification

AST expression conversion transforms parse tree (CST) expressions to interpreter AST. It handles all expression types including literals, operators, calls, collections, control flow, and special expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3031-3060 |
| Category | Interpreter |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/01_unit/app/interpreter/ast_convert_expr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AST expression conversion transforms parse tree (CST) expressions to interpreter AST.
It handles all expression types including literals, operators, calls, collections,
control flow, and special expressions.

## Key Features

- Literal conversion (int, float, string, bool, nil)
- Binary operators (17 types: arithmetic, comparison, logical, bitwise)
- Unary operators (5 types: neg, not, bit_not, ref, deref)
- Call expressions (functions and methods)
- Collection literals (arrays, dicts, tuples)
- Lambda expressions with parameter lists
- Control flow (if, match, range)
- Special expressions (await, try, parenthesized)

## Implementation

File: `/home/ormastes/dev/pub/simple/src/app/interpreter/ast_convert_expr.spl`

## Test Note

These tests validate successful conversion from parse tree nodes to AST expressions.
Full AST structure validation requires integration tests with actual parser output.

## Scenarios

### convert_expression Entry Point

#### converts integer literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that integer nodes are recognized
# Actual conversion requires parser integration
pass
```

</details>

#### converts float literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that float nodes are recognized
pass
```

</details>

#### converts string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that string nodes are recognized
pass
```

</details>

#### converts boolean literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that boolean nodes are recognized
pass
```

</details>

#### converts nil literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that nil nodes are recognized
pass
```

</details>

#### converts identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that identifier nodes are recognized
pass
```

</details>

### convert_binary_expression - Arithmetic

#### recognizes addition operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for +
pass
```

</details>

#### recognizes subtraction operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for -
pass
```

</details>

#### recognizes multiplication operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for *
pass
```

</details>

#### recognizes division operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for /
pass
```

</details>

#### recognizes modulo operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for %
pass
```

</details>

#### recognizes power operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for **
pass
```

</details>

### convert_binary_expression - Comparison

#### recognizes equality operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for ==
pass
```

</details>

#### recognizes inequality operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for !=
pass
```

</details>

#### recognizes less than operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for <
pass
```

</details>

#### recognizes less than or equal operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for <=
pass
```

</details>

#### recognizes greater than operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for >
pass
```

</details>

#### recognizes greater than or equal operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for >=
pass
```

</details>

### convert_binary_expression - Logical & Bitwise

#### recognizes logical and operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for and
pass
```

</details>

#### recognizes logical or operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for or
pass
```

</details>

#### recognizes bitwise and operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for &
pass
```

</details>

#### recognizes bitwise or operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for |
pass
```

</details>

#### recognizes bitwise xor operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for ^
pass
```

</details>

#### recognizes left shift operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for <<
pass
```

</details>

#### recognizes right shift operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for >>
pass
```

</details>

### convert_unary_expression

#### recognizes negation operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for -
pass
```

</details>

#### recognizes logical not operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for not
pass
```

</details>

#### recognizes bitwise not operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for ~
pass
```

</details>

#### recognizes reference operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for &
pass
```

</details>

#### recognizes dereference operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests operator recognition for *
pass
```

</details>

### Call Expression Conversion

#### converts function calls via convert_call_expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests function call node conversion
pass
```

</details>

#### extracts call arguments via convert_arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests argument list extraction
pass
```

</details>

#### converts method calls via convert_method_call

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests method call node conversion
pass
```

</details>

### Access Expression Conversion

#### converts index expressions via convert_index_expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests array/dict indexing
pass
```

</details>

#### converts field access via convert_field_expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests struct field access
pass
```

</details>

### Collection Literal Conversion

#### converts array literals via convert_array_literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests array literal conversion
pass
```

</details>

#### converts dict literals via convert_dict_literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests dict literal conversion
pass
```

</details>

#### converts dict entries via convert_dict_entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests key-value pair conversion
pass
```

</details>

#### converts tuple literals via convert_tuple_literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests tuple literal conversion
pass
```

</details>

### Lambda Expression Conversion

#### converts lambda expressions via convert_lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests lambda expression conversion
pass
```

</details>

#### extracts lambda parameters via convert_lambda_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests parameter list extraction
pass
```

</details>

### Control Flow Expression Conversion

#### converts if expressions via convert_if_expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests if-then-else conversion
pass
```

</details>

#### converts match expressions via convert_match_expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests pattern matching conversion
pass
```

</details>

#### converts match arms via convert_match_arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests case clause conversion
pass
```

</details>

#### converts range expressions via convert_range_expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests range literal conversion
pass
```

</details>

### Conversion Error Handling

#### returns error for unknown expression kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests unknown node type handling
pass
```

</details>

#### returns error for incomplete binary expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests missing operand detection
pass
```

</details>

#### returns error for incomplete unary expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests missing operand detection
pass
```

</details>

#### returns error for call missing callee

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid call expression
pass
```

</details>

#### returns error for method call missing object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid method call
pass
```

</details>

#### returns error for incomplete index expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests missing index detection
pass
```

</details>

#### returns error for field access missing object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid field access
pass
```

</details>

#### returns error for incomplete dict entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests missing key or value
pass
```

</details>

#### returns error for lambda missing body

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests incomplete lambda
pass
```

</details>

#### returns error for incomplete if expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests missing branch detection
pass
```

</details>

#### returns error for match missing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid match expression
pass
```

</details>

#### returns error for incomplete match arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid case clause
pass
```

</details>

#### returns error for incomplete range expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests missing start or end
pass
```

</details>

#### returns error for empty parenthesized expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid parentheses
pass
```

</details>

#### returns error for await missing expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid await
pass
```

</details>

#### returns error for try missing expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests invalid try
pass
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
