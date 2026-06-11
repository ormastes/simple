# TreeSitter Error Handling and Edge Cases Specification

> use compiler.treesitter.*

<!-- sdn-diagram:id=treesitter_error_recovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_error_recovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_error_recovery_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_error_recovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Error Handling and Edge Cases Specification

use compiler.treesitter.*

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-ERR-001 to #TS-ERR-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_error_recovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# outline.errors contains ParseError items
```

## Scenarios

### TreeSitter Edge Cases - Empty Source

#### produces empty module for empty source

1. var ts = TreeSitter new
2. expect outline functions len
3. expect outline classes len
4. expect outline structs len
5. expect outline enums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
expect outline.classes.len() to_equal 0
expect outline.structs.len() to_equal 0
expect outline.enums.len() to_equal 0
```

</details>

#### produces empty module for whitespace only

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("   \n   \n   ")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
```

</details>

#### produces empty module for comments only

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("# just a comment\n# another comment")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
```

</details>

### TreeSitter Multiple Function Parsing

#### parses three functions

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn alpha():\n    1\n\nfn beta():\n    2\n\nfn gamma():\n    3"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 3
```

</details>

#### preserves function names

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn first():\n    1\n\nfn second():\n    2"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions[0].name to_equal "first"
expect outline.functions[1].name to_equal "second"
```

</details>

### TreeSitter Extern Function Parsing

#### parses extern fn

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

#### parses extern fn with params

1. var ts = TreeSitter new
2. expect f params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "extern fn rt_write(path: text, content: text) -> bool"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val f = outline.functions[0]
expect f.params.len() to_equal 2
```

</details>

### TreeSitter Method Modifiers

#### parses static method in impl

1. var ts = TreeSitter new
2. expect outline impls len
3. expect impl block methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
val impl_block = outline.impls[0]
expect impl_block.methods.len() to_equal 1
val m = impl_block.methods[0]
expect m.is_static to_equal true
```

</details>

#### parses mutable method in impl

1. var ts = TreeSitter new
2. expect outline impls len
3. expect impl block methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Point:\n    me move(dx: i64):\n        self.x = self.x + dx"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
val impl_block = outline.impls[0]
expect impl_block.methods.len() to_equal 1
val m = impl_block.methods[0]
expect m.is_mutable to_equal true
```

</details>

### TreeSitter Doc Comment Parsing

#### attaches doc comment to function

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "## This is a doc comment\nfn hello():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.has_doc_comment to_equal true
```

</details>

#### attaches doc comment to struct

1. var ts = TreeSitter new
2. expect outline structs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "## A 2D point\nstruct Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.has_doc_comment to_equal true
```

</details>

### TreeSitter Error Recovery

#### continues parsing after valid declarations

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn valid_first():\n    1\n\nfn valid_second():\n    2"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 2
```

</details>

#### parses complex source without crashing

1. var ts = TreeSitter new
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.text.{NL2}\n\nfn main():\n    val x = 42\n    print x\n\nstruct Config:\n    name: text\n    debug: bool"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# Should find at least the function and struct
expect outline.functions.len() >= 1
```

</details>

### TreeSitter Trait-Impl Parsing

#### parses trait followed by impl

1. var ts = TreeSitter new
2. expect outline traits len
3. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "trait Greetable:\n    fn greet() -> text:\n        pass\n\nimpl Person:\n    fn greet() -> text:\n        self.name"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
expect outline.impls.len() to_equal 1
```

</details>

#### parses impl methods

1. var ts = TreeSitter new
2. expect impl block methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Calculator:\n    fn add(a: i64, b: i64) -> i64:\n        a + b\n    fn sub(a: i64, b: i64) -> i64:\n        a - b"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val impl_block = outline.impls[0]
expect impl_block.methods.len() to_equal 2
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
