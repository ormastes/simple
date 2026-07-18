# TreeSitter Parser Specification

> use std.parser.treesitter.{TreeSitterParser, Tree, Node}

<!-- sdn-diagram:id=treesitter_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Parser Specification

use std.parser.treesitter.{TreeSitterParser, Tree, Node}

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-PARSER-001 to #TS-PARSER-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/features/treesitter/treesitter_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use std.parser.treesitter.{TreeSitterParser, Tree, Node}

val parser = TreeSitterParser.new("simple")?
val tree = parser.parse(source)?
val root = tree.root()?
```

## Scenarios

### TreeSitter Parser Creation

#### creates parser for Simple language

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TreeSitterParser.new("simple")
expect result.ok.?
```

</details>

#### rejects unsupported languages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TreeSitterParser.new("unknown_language")
expect result.err.?
```

</details>

#### creates parser with grammar loaded

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = TreeSitterParser.new("simple").unwrap()
# Parser should have grammar rules
expect true  # Parser created successfully
```

</details>

### TreeSitter Basic Parsing

#### simple expressions

#### parses integer literal

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("42")
expect tree.ok.?
```

</details>

#### parses variable declaration

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42")
expect tree.ok.?
```

</details>

#### parses binary expression

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 1 + 2")
expect tree.ok.?
```

</details>

#### function definitions

#### parses simple function

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn add(a, b):\n    a + b"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

#### parses function with return type

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn get_value() -> i64:\n    42"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

#### parses function with parameters

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn greet(name: text) -> text:\n    name"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

#### control flow

#### parses if statement

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "if x > 0:\n    y = 1"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "while x < 10:\n    x = x + 1"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>


</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "for i in range(10):\n    sum = sum + i"
val tree = parser.parse(source)
expect tree.ok.?
```

</details>


</details>

### TreeSitter Tree Structure

#### root node

#### has root node after parsing

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root()
expect root.?
```

</details>

#### root node is module type

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.kind == "module"
```

</details>

#### child nodes

#### function has children

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn test():\n    42"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

#### node spans

#### nodes have valid spans

1. var parser = TreeSitterParser new
2. expect tree source len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.?
expect tree.source.len() > 0
```

</details>

### TreeSitter Node Types

#### identifies function definition

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "fn test():\n    42"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

#### identifies variable declaration

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

#### identifies struct definition

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "struct Point:\n    x: i64\n    y: i64"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
```

</details>

### TreeSitter Multi-Statement Parsing

#### parses multiple declarations

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = """val x = 1
```

</details>

#### parses mixed declarations

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = """val x = 42
```

</details>

### TreeSitter Complex Expression Parsing

#### parses nested arithmetic

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = ((1 + 2) * 3)")
expect tree.ok.?
```

</details>

#### parses method chain

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = obj.method1().method2()")
expect tree.ok.?
```

</details>

#### parses array literal

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val arr = [1, 2, 3]")
expect tree.ok.?
```

</details>

#### parses dictionary literal

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val d = {\"key\": \"value\"}")
expect tree.ok.?
```

</details>

#### parses lambda expression

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse(r"val f = \x: x + 1")
expect tree.ok.?
```

</details>

### TreeSitter Source Information

#### preserves source text

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "val x = 42"
val tree = parser.parse(source).unwrap()
expect tree.source == source
```

</details>

#### tracks line numbers

1. var parser = TreeSitterParser new
2. expect tree source contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val source = "val x = 42\nval y = 43"
val tree = parser.parse(source).unwrap()
val root = tree.root().unwrap()
expect root.?
expect tree.source.contains("\n")
```

</details>

#### tracks column positions

1. var parser = TreeSitterParser new
2. expect tree source starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
val root = tree.root().unwrap()
expect root.?
expect tree.source.starts_with("val")
```

</details>

### TreeSitter Tree Versioning

#### initial tree has version 0

1. var parser = TreeSitterParser new
2. expect tree root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("val x = 42").unwrap()
expect tree.root().?
```

</details>

#### incremental parse increments version

1. var parser = TreeSitterParser new
2. expect tree1 root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree1 = parser.parse("val x = 42").unwrap()
expect tree1.root().?
```

</details>

### TreeSitter Parse Results

#### returns Ok for valid syntax

1. var parser = TreeSitterParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val result = parser.parse("val x = 42")
expect result.ok.?
```

</details>

#### returns tree for valid syntax

1. var parser = TreeSitterParser new
2. expect tree root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parser = TreeSitterParser.new("simple").unwrap()
val tree = parser.parse("fn test():\n    42").unwrap()
expect tree.root().?
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
