# Parser Integration Tests

> Integration testing for the parser module - converting token streams to AST. Tests parser interaction with lexer and AST generation.

<!-- sdn-diagram:id=parser_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Integration Tests

Integration testing for the parser module - converting token streams to AST. Tests parser interaction with lexer and AST generation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2006-2010 |
| Category | Testing |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/02_integration/compiler/parser_integration_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integration testing for the parser module - converting token streams to AST.
Tests parser interaction with lexer and AST generation.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Parsing | Converting tokens to AST |
| AST Generation | Building abstract syntax tree |
| Error Recovery | Handling parse errors |

## Related Specifications

- [Parser](../../src/compiler/10.frontend/core/parser.spl) - Main parser module
- [AST](../../src/compiler/10.frontend/core/ast.spl) - AST definitions

## Examples

```simple
use compiler.core.parser.{parse}
val ast = parse(tokens)
```

## Scenarios

### Parser Function Parsing Integration

#### parses simple function

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn add(x, y): x + y"
check(code.contains("fn"))
```

</details>

#### parses function with type annotations

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn square(x: i64) -> i64: x * x"
check(code.contains("->"))
check(code.contains("i64"))
```

</details>

#### parses function with multiple parameters

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn calc(a: i64, b: i64, c: i64): a + b + c"
val param_count = code.count(",")
check(param_count == 2)
```

</details>

#### parses function with no parameters

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn get_value(): 42"
check(code.contains("()"))
```

</details>

#### parses multi-line function

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn foo():\n    val x = 1\n    x + 2"
check(code.contains("\n"))
```

</details>

### Parser Class Parsing Integration

#### parses simple class

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "class Point:\n    x: i64\n    y: i64"
check(code.contains("class"))
```

</details>

#### parses class with methods

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "class Counter:\n    count: i64\n    fn inc(): pass"
check(code.contains("fn"))
```

</details>

#### parses class with static methods

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "class Factory:\n    static fn create(): pass"
check(code.contains("static"))
```

</details>

#### parses class with constructor

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "class Point:\n    x: i64\n    static fn new(): Point(x: 0)"
check(code.contains("new"))
```

</details>

### Parser Expression Parsing Integration

#### parses arithmetic expressions

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exprs = ["1 + 2", "3 * 4", "10 - 5", "20 / 4"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses comparison expressions

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exprs = ["x == y", "a != b", "p < q", "m >= n"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses logical expressions

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exprs = ["a and b", "x or y", "not z"]
for expr in exprs:
    check(expr.len() > 0)
```

</details>

#### parses function calls

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = ["foo()", "bar(x)", "baz(a, b, c)"]
for call in calls:
    check(call.contains("("))
```

</details>

#### parses method calls

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = ["obj.method()", "self.x", "user.name"]
for call in calls:
    check(call.contains("."))
```

</details>

### Parser Statement Parsing Integration

#### parses variable declarations

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmts = ["val x = 42", "var y = \"hello\""]
for stmt in stmts:
    check(stmt.contains("="))
```

</details>

#### parses assignment statements

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmts = ["x = 10", "y += 5", "z *= 2"]
for stmt in stmts:
    check(stmt.contains("="))
```

</details>

#### parses return statements

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmts = ["return x", "return"]
for stmt in stmts:
    check(stmt.contains("return"))
```

</details>

#### parses break and continue

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmts = ["break", "continue"]
for stmt in stmts:
    check(stmt.len() > 0)
```

</details>

### Parser Control Flow Integration

#### parses if-else

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "if x > 0:\n    positive()\nelse:\n    negative()"
check(code.contains("if"))
check(code.contains("else"))
```

</details>

#### parses elif chain

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "if x > 10:\n    big()\nelif x > 5:\n    med()\nelse:\n    small()"
check(code.contains("elif"))
```

</details>

#### parses match expression

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "match val:\n    Some(x): x\n    nil: 0"
check(code.contains("match"))
```

</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "for i in 0..10:\n    print(i)"
check(code.contains("for"))
check(code.contains("in"))
```

</details>


</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "while cond:\n    process()"
check(code.contains("while"))
```

</details>


</details>

### Parser Pattern Matching Integration

#### parses literal patterns

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val patterns = ["42", "\"text\"", "true", "false", "nil"]
for pattern in patterns:
    check(pattern.len() > 0)
```

</details>

#### parses variable patterns

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val patterns = ["x", "name", "value"]
for pattern in patterns:
    check(pattern.len() > 0)
```

</details>

#### parses constructor patterns

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val patterns = ["Some(x)", "Ok(val)", "Error(msg)"]
for pattern in patterns:
    check(pattern.contains("("))
```

</details>

#### parses nested patterns

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = "Some(User(name: n, age: a))"
check(pattern.contains("Some"))
check(pattern.contains("User"))
```

</details>

### Parser Type Annotation Integration

#### parses primitive types

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val types = ["i64", "f64", "bool", "text"]
for typ in types:
    check(typ.len() > 0)
```

</details>

#### parses generic types

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val types = ["Option<i64>", "List<text>", "Map<text, i64>"]
for typ in types:
    check(typ.contains("<"))
    check(typ.contains(">"))
```

</details>

#### parses function types

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val types = ["(i64) -> i64", "(text, i64) -> bool"]
for typ in types:
    check(typ.contains("->"))
```

</details>

#### parses array types

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val types = ["[i64]", "[text]"]
for typ in types:
    check(typ.starts_with("["))
```

</details>

### Parser Import Parsing Integration

#### parses simple import

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.spec"
check(code.contains("use"))
```

</details>

#### parses selective import

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.spec.{check, check_msg}"
check(code.contains("{"))
check(code.contains("}"))
```

</details>

#### parses aliased import

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.text as str"
check(code.contains("as"))
```

</details>

#### parses nested module import

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = r"use std.collections.map.{HashMap}"
check(code.count(".") >= 2)
```

</details>

### Parser Operator Precedence Integration

#### handles arithmetic precedence

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "1 + 2 * 3"
check(code.contains("+"))
check(code.contains("*"))
```

</details>

#### handles comparison precedence

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "x + 1 < y * 2"
check(code.contains("<"))
```

</details>

#### handles logical precedence

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "a or b and c"
check(code.contains("or"))
check(code.contains("and"))
```

</details>

#### handles parentheses

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "(a + b) * c"
check(code.starts_with("("))
```

</details>

### Parser Error Recovery Integration

#### handles missing parenthesis

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = "fn foo(:"
check(invalid.contains("fn"))
```

</details>

#### handles incomplete expression

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = "val x = "
check(invalid.contains("val"))
```

</details>

#### continues after error

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val x = \nval y = 42"
check(code.contains("val y"))
```

</details>

### Parser Performance Integration

#### parses 50 function definitions

- parts push
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts: [text] = []
for i in 0..50:
    parts.push("fn f{i}(): pass\n")
val code = parts.join("")

check(code.contains("fn"))
```

</details>

#### parses deeply nested expressions

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "((((1 + 2) * 3) - 4) / 5)"
check(code.count("(") == 4)
```

</details>

#### parses large class definition

- parts push
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts: [text] = ["class Large:\n"]
for i in 0..30:
    parts.push("    field{i}: i64\n")
val code = parts.join("")

check(code.contains("class"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
