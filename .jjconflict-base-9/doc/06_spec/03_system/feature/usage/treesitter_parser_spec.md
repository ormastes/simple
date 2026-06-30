# TreeSitter Parser Specification

> use compiler.treesitter.*

<!-- sdn-diagram:id=treesitter_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_parser_spec -> compiler
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
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Parser Specification

use compiler.treesitter.*

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-PARSER-001 to #TS-PARSER-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
```

## Scenarios

### TreeSitter Parser Creation

#### creates parser from source

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("val x = 42")
val outline = ts.parse_outline()
# Parser created and parsed without crashing
expect true to_equal true
```

</details>

#### creates parser from empty source

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect true to_equal true
```

</details>

### TreeSitter Basic Function Parsing

#### parses single function

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn test():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.functions[0].name to_equal "test"
```

</details>

#### parses function with return type

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn get_value() -> i64:\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "get_value"
expect f.has_return_type to_equal true
```

</details>

#### parses function with parameters

1. var ts = TreeSitter new
2. expect f params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn greet(name: text) -> text:\n    name"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val f = outline.functions[0]
expect f.params.len() to_equal 1
```

</details>

### TreeSitter Basic Struct Parsing

#### parses struct with fields

1. var ts = TreeSitter new
2. expect outline structs len
3. expect s fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.name to_equal "Point"
expect s.fields.len() to_equal 2
```

</details>

### TreeSitter Basic Enum Parsing

#### parses enum with variants

1. var ts = TreeSitter new
2. expect outline enums len
3. expect e variants len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "enum Direction:\n    North\n    South\n    East\n    West"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.enums.len() to_equal 1
val e = outline.enums[0]
expect e.name to_equal "Direction"
expect e.variants.len() to_equal 4
```

</details>

### TreeSitter Import Parsing

#### parses use statement

1. var ts = TreeSitter new
2. expect outline imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.text.{NL2}\n\nfn main():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.imports.len() >= 1
```

</details>

### TreeSitter Export Parsing

#### parses export statement

1. var ts = TreeSitter new
2. expect outline exports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "export Foo, Bar"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.exports.len() to_equal 1
```

</details>

### TreeSitter Multi-Declaration Parsing

#### parses function and struct

1. var ts = TreeSitter new
2. expect outline functions len
3. expect outline structs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hello():\n    42\n\nstruct Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.structs.len() to_equal 1
```

</details>

#### parses function, struct, and enum

1. var ts = TreeSitter new
2. expect outline functions len
3. expect outline structs len
4. expect outline enums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hello():\n    42\n\nstruct Point:\n    x: i64\n\nenum Color:\n    Red\n    Blue"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.structs.len() to_equal 1
expect outline.enums.len() to_equal 1
```

</details>

### TreeSitter Complex Source Parsing

#### parses function with impl

1. var ts = TreeSitter new
2. expect outline structs len
3. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Point:\n    x: i64\n    y: i64\n\nimpl Point:\n    fn get_x() -> i64:\n        self.x"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
expect outline.impls.len() to_equal 1
```

</details>

### TreeSitter Empty Source Parsing

#### returns empty outline for empty source

1. var ts = TreeSitter new
2. expect outline functions len
3. expect outline classes len
4. expect outline structs len
5. expect outline enums len
6. expect outline traits len
7. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
expect outline.classes.len() to_equal 0
expect outline.structs.len() to_equal 0
expect outline.enums.len() to_equal 0
expect outline.traits.len() to_equal 0
expect outline.impls.len() to_equal 0
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
