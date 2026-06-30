# TreeSitter Heuristic Mode Specification

> use compiler.treesitter.*

<!-- sdn-diagram:id=treesitter_cursor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_cursor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_cursor_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_cursor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Heuristic Mode Specification

use compiler.treesitter.*

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-CURSOR-001 to #TS-CURSOR-015 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_cursor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use compiler.treesitter.*
use compiler.core.lexer.*

# Create heuristic-mode parser
var ts = TreeSitter(
lexer: lexer_new(source),
current: lex_token_eof(1),
previous: lex_token_eof(1),
errors: [],
doc_comment: nil,
inline_blocks: [],
current_context: nil,
fast_mode: false,
heuristic_mode: true,
registry: nil
)
val outline = ts.parse_outline()
```

## Scenarios

### Heuristic Function Parsing

#### parses fn declaration

1. var ts = make heuristic ts
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hello():\n    42"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
```

</details>

#### parses multiple functions

1. var ts = make heuristic ts
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn foo():\n    1\nfn bar():\n    2"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 2
```

</details>

### Heuristic Class Parsing

#### parses class declaration

1. var ts = make heuristic ts
2. expect outline classes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Point:\n    x: i64\n    y: i64"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.classes.len() to_equal 1
```

</details>

### Heuristic Struct Parsing

#### parses struct declaration

1. var ts = make heuristic ts
2. expect outline structs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Vec2:\n    x: f64\n    y: f64"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
```

</details>

### Heuristic Enum Parsing

#### parses enum declaration

1. var ts = make heuristic ts
2. expect outline enums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "enum Color:\n    Red\n    Green\n    Blue"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.enums.len() to_equal 1
```

</details>

### Heuristic Trait Parsing

#### parses trait declaration

1. var ts = make heuristic ts
2. expect outline traits len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "trait Drawable:\n    fn draw():\n        pass"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
```

</details>

### Heuristic Impl Parsing

#### parses impl block

1. var ts = make heuristic ts
2. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Point:\n    fn get_x() -> i64:\n        self.x"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
```

</details>

#### parses impl with multiple members

1. var ts = make heuristic ts
2. expect outline impls len
3. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Point:\n    fn get_x() -> i64:\n        self.x\n    fn get_y() -> i64:\n        self.y"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
# Methods inside impl are collected separately as functions
expect outline.functions.len() >= 2
```

</details>

### Heuristic Visibility Detection

#### detects pub function

1. var ts = make heuristic ts
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub fn hello():\n    42"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
```

</details>

#### detects pub struct

1. var ts = make heuristic ts
2. expect outline structs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub struct Point:\n    x: i64"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
```

</details>

### Heuristic Error Tolerance

#### handles empty source

1. var ts = make heuristic ts
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ""
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
```

</details>

#### skips unrecognized lines

1. var ts = make heuristic ts
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "some random text\nfn valid():\n    42"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
# Should still find the valid function
expect outline.functions.len() to_equal 1
```

</details>

#### parses mixed valid and invalid

1. var ts = make heuristic ts
2. expect outline functions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn first():\n    1\n??? invalid ???\nfn second():\n    2"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 2
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
