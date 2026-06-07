# Grammar Simple Specification

> 1. check

<!-- sdn-diagram:id=grammar_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=grammar_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

grammar_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=grammar_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grammar Simple Specification

## Scenarios

### SimpleGrammar - Core Modern Syntax

#### parses val declarations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val x = 42"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses var declarations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var count = 0"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses const declarations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "const MAX_SIZE = 1000"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Lambda Syntax

#### parses fn lambda syntax

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val add = fn(x, y): x + y"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses backslash lambda

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val double = \\x: x * 2"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Generic Types

#### parses generic type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val items: List<Int> = []"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses nested generics

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val nested: List<Option<Int>> = []"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Module System

#### parses use statement with glob

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.collections"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses use statement with braces

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.spec.{describe, it}"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Advanced Types

#### parses optional type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val maybe: Int? = None"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses result type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val result: Int! = Ok(42)"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Operators

#### parses compound assignment

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "x += 5"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses range operators

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val range1 = 0..10"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Literals

#### parses typed integer

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val a = 42i32"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

#### parses symbols

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val status = :success"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

### SimpleGrammar - Error Recovery

#### recovers from syntax errors

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test()"
val ast = parse_code(code)
check(ast.is_ok())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/grammar_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleGrammar - Core Modern Syntax
- SimpleGrammar - Lambda Syntax
- SimpleGrammar - Generic Types
- SimpleGrammar - Module System
- SimpleGrammar - Advanced Types
- SimpleGrammar - Operators
- SimpleGrammar - Literals
- SimpleGrammar - Error Recovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
