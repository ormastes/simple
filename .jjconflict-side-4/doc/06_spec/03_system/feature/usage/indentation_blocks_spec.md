# Indentation-Based Blocks Specification

> Indentation-based blocks use Python-style significant whitespace to delimit code blocks instead of braces. This feature provides clean, readable syntax for function bodies, control flow, and other block-structured code in Simple.

<!-- sdn-diagram:id=indentation_blocks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=indentation_blocks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

indentation_blocks_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=indentation_blocks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Indentation-Based Blocks Specification

Indentation-based blocks use Python-style significant whitespace to delimit code blocks instead of braces. This feature provides clean, readable syntax for function bodies, control flow, and other block-structured code in Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #840-845 |
| Category | Syntax |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/indentation_blocks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Indentation-based blocks use Python-style significant whitespace to delimit code blocks
instead of braces. This feature provides clean, readable syntax for function bodies,
control flow, and other block-structured code in Simple.

## Syntax

```simple
# Function body indentation
fn add(a: i64, b: i64) -> i64:
a + b

# Control flow indentation
if condition:
do_something()
else:
do_alternative()

# Nested indentation
loop:
if inner_condition:
process()
continue
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Indentation | Whitespace level determines block scope |
| Dedentation | Return to previous indentation level |
| Colon | Marks beginning of indented block |
| Continuation | Lines can continue to next with indentation |

## Behavior

- Indentation level determines block membership
- Consistent indentation required within a block
- Tab and space mixing is not allowed
- Indentation can use either tabs or spaces (configured at parse)
- Dedentation marks end of block and returns to outer scope

## Related Specifications

- [Lexer](../lexer/lexer_spec.spl) - Token recognition including indentation
- [Parser](../parser/parser_spec.spl) - Block structure parsing
- [Syntax](../syntax/syntax_spec.spl) - Language syntax overview

## Implementation Notes

Indentation handling in lexer:
- Track indentation stack as separate token stream
- INDENT token marks increase in indentation
- DEDENT token marks decrease in indentation
- Implicit DEDENT at end of file if needed
- Error on inconsistent indentation mixing

## Examples

```simple
# Multi-level nested blocks
fn process_data(items: List<Int>) -> i64:
var total = 0
for item in items:
if item > 0:
total = total + item
else:
total = total - item
total
```

## Scenarios

### Indentation Blocks - Basic

#### with function body indentation

#### recognizes indented function body

1. fn simple
2. expect simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn simple() -> i64:
    42

expect simple() == 42
```

</details>

#### with nested function bodies

#### handles nested function definitions

1. fn outer
2. fn inner
3. inner
4. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer():
    fn inner() -> i64:
        10
    inner()

expect outer() == 10
```

</details>

### Indentation Blocks - Control Flow

#### with if-else blocks

#### handles if-else indentation

1. fn check positive
2. expect check positive
3. expect check positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn check_positive(x: i64) -> text:
    if x > 0:
        "positive"
    else:
        "non-positive"

expect check_positive(5) == "positive"
expect check_positive(-3) == "non-positive"
```

</details>

#### with loop blocks

<details>
<summary>Advanced: handles loop indentation</summary>

#### handles loop indentation

1. fn count up
2. expect count up


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn count_up(n: i64) -> i64:
    var sum = 0
    var i = 0
    loop:
        if i >= n:
            break
        sum = sum + i
        i = i + 1
    sum

expect count_up(5) == 10  # 0+1+2+3+4
```

</details>


</details>

#### with nested control flow

#### handles nested control flow

1. fn matrix sum
2. expect matrix sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn matrix_sum(n: i64) -> i64:
    var sum = 0
    var i = 0
    loop:
        if i >= n:
            break
        var j = 0
        loop:
            if j >= n:
                break
            sum = sum + 1
            j = j + 1
        i = i + 1
    sum

expect matrix_sum(3) == 9  # 3x3 matrix
```

</details>

### Indentation Blocks - Multiple Statements

#### with sequential statements

#### executes multiple statements

1. fn multi statement
2. expect multi statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multi_statement() -> i64:
    var x = 1
    var y = 2
    var z = 3
    x + y + z

expect multi_statement() == 6
```

</details>

#### with mixed statement types

#### mixes different statement types

1. fn mixed statements
2. expect mixed statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn mixed_statements(n: i64) -> i64:
    var result = 0
    result = n * 2
    result = result + 5
    result

expect mixed_statements(10) == 25
```

</details>

### Indentation Blocks - Consistency

#### with consistent indentation

#### maintains block indentation

1. fn consistent indent
2. expect consistent indent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn consistent_indent() -> i64:
    var a = 1
    var b = 2
    var c = 3
    a + b + c

expect consistent_indent() == 6
```

</details>

#### with dedentation

#### terminates block on dedent

1. fn outer
2. fn inner
3. inner
4. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer() -> i64:
    fn inner():
        10
    inner() + 5

expect outer() == 15
```

</details>

### Indentation Blocks - Complex Nesting

#### with deeply nested blocks

#### handles deep nesting

1. fn deep nest
2. expect deep nest


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn deep_nest() -> i64:
    var sum = 0
    var i = 0
    loop:
        if i >= 2:
            break
        var j = 0
        loop:
            if j >= 2:
                break
            var k = 0
            loop:
                if k >= 2:
                    break
                sum = sum + 1
                k = k + 1
            j = j + 1
        i = i + 1
    sum

expect deep_nest() == 8  # 2^3
```

</details>

#### with mixed block types

#### mixes nested block types

1. fn mixed nesting
2. fn compute
3. total = total + compute
4. expect mixed nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn mixed_nesting() -> i64:
    fn compute(x: i64) -> i64:
        if x > 5:
            x * 2
        else:
            x + 1

    var total = 0
    var i = 0
    loop:
        if i >= 3:
            break
        total = total + compute(i)
        i = i + 1
    total

expect mixed_nesting() == 6  # compute(0)=1 + compute(1)=2 + compute(2)=3
```

</details>

### Indentation Blocks - Expressions

#### with conditional expressions

#### handles if expression indentation

1. fn if expr
2. expect if expr


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn if_expr(x: i64) -> i64:
    val result = if x > 0:
        x * 2
    else:
        0
    result

expect if_expr(5) == 10
```

</details>

#### with block values

#### uses indented blocks as values

1. fn block value
2. expect block value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn block_value() -> i64:
    val x = 5
    val y =
        x + 3
    y

expect block_value() == 8
```

</details>

### Indentation Blocks - Edge Cases

#### with empty blocks

#### handles empty block

1. fn empty func
2. empty func


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn empty_func():
    pass

empty_func()
pass
```

</details>

#### with single statement blocks

#### handles single-statement block

1. fn single stmt
2. expect single stmt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn single_stmt() -> i64:
    42

expect single_stmt() == 42
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
