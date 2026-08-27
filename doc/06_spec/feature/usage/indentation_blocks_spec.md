# Indentation-Based Blocks Specification

> Indentation-based blocks use Python-style significant whitespace to delimit code blocks instead of braces. This feature provides clean, readable syntax for function bodies, control flow, and other block-structured code in Simple.

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
| Source | `test/feature/usage/indentation_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Indentation-based blocks use Python-style significant whitespace to delimit code blocks
instead of braces. This feature provides clean, readable syntax for function bodies,
control flow, and other block-structured code in Simple.

## Syntax

```simple
# Function body indentation
use std.spec.step

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

- recognizes indented function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("recognizes indented function body")
fn simple() -> i64:
    42

expect simple() == 42
```

</details>

#### with nested function bodies

#### handles nested function definitions

- handles nested function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested function definitions")
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

- handles if-else indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles if-else indentation")
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

- handles loop indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles loop indentation")
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

- handles nested control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested control flow")
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

- executes multiple statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes multiple statements")
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

- mixes different statement types


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes different statement types")
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

- maintains block indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maintains block indentation")
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

- terminates block on dedent


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("terminates block on dedent")
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

- handles deep nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles deep nesting")
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

- mixes nested block types


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes nested block types")
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

- handles if expression indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles if expression indentation")
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

- uses indented blocks as values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses indented blocks as values")
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

- handles empty block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles empty block")
fn empty_func():
    pass

empty_func()
pass
```

</details>

#### with single statement blocks

#### handles single-statement block

- handles single-statement block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles single-statement block")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `774d0ddb0e6c7f898773dbb9081aeeb2c0375a78b28feb4f1dfbb791ed47e262`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `774d0ddb0e6c7f898773dbb9081aeeb2c0375a78b28feb4f1dfbb791ed47e262`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `774d0ddb0e6c7f898773dbb9081aeeb2c0375a78b28feb4f1dfbb791ed47e262`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/indentation_blocks_spec.spl
mirror: doc/06_spec/feature/usage/indentation_blocks_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/indentation_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/indentation_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/indentation_blocks_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes indented function body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/indentation_blocks_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles nested function definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/indentation_blocks_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles if-else indentation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
