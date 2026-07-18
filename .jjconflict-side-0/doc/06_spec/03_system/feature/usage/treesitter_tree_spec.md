# TreeSitter OutlineModule Structure Specification

> use compiler.treesitter.*

<!-- sdn-diagram:id=treesitter_tree_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_tree_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_tree_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_tree_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter OutlineModule Structure Specification

use compiler.treesitter.*

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-TREE-001 to #TS-TREE-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_tree_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
```

## Scenarios

### OutlineModule Function Parsing

#### parses a simple function

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hello():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "hello"
```

</details>

#### parses function with parameters

1. var ts = TreeSitter new
2. expect outline functions len
3. expect f params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn add(x: i64, y: i64) -> i64:\n    x + y"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "add"
expect f.params.len() to_equal 2
```

</details>

#### parses extern function

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "extern fn rt_read(path: text) -> text"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "rt_read"
expect f.is_extern to_equal true
```

</details>

#### parses multiple functions

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn foo():\n    1\n\nfn bar():\n    2\n\nfn baz():\n    3"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 3
```

</details>

### OutlineModule Class Parsing

#### parses a simple class

1. var ts = TreeSitter new
2. expect outline classes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.classes.len() to_equal 1
val c = outline.classes[0]
expect c.name to_equal "Point"
```

</details>

#### parses class fields

1. var ts = TreeSitter new
2. expect c fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val c = outline.classes[0]
expect c.fields.len() to_equal 2
```

</details>

### OutlineModule Struct Parsing

#### parses a simple struct

1. var ts = TreeSitter new
2. expect outline structs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Vec2:\n    x: f64\n    y: f64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.name to_equal "Vec2"
```

</details>

#### parses struct fields

1. var ts = TreeSitter new
2. expect s fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Color:\n    r: u8\n    g: u8\n    b: u8"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val s = outline.structs[0]
expect s.fields.len() to_equal 3
```

</details>

### OutlineModule Enum Parsing

#### parses a simple enum

1. var ts = TreeSitter new
2. expect outline enums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "enum Color:\n    Red\n    Green\n    Blue"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.enums.len() to_equal 1
val e = outline.enums[0]
expect e.name to_equal "Color"
```

</details>

#### parses enum variants

1. var ts = TreeSitter new
2. expect e variants len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "enum Direction:\n    North\n    South\n    East\n    West"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val e = outline.enums[0]
expect e.variants.len() to_equal 4
```

</details>

### OutlineModule Import Parsing

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

### OutlineModule Multiple Declarations

#### parses mixed declarations

1. var ts = TreeSitter new
2. expect outline functions len
3. expect outline structs len
4. expect outline enums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hello():\n    42\n\nstruct Point:\n    x: i64\n    y: i64\n\nenum Color:\n    Red\n    Blue"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.structs.len() to_equal 1
expect outline.enums.len() to_equal 1
```

</details>

#### produces empty module for empty source

1. var ts = TreeSitter new
2. expect outline functions len
3. expect outline classes len
4. expect outline structs len
5. expect outline enums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ""
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
expect outline.classes.len() to_equal 0
expect outline.structs.len() to_equal 0
expect outline.enums.len() to_equal 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
