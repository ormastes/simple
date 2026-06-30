# TreeSitter Advanced Outline Parsing Specification

> use compiler.treesitter.*

<!-- sdn-diagram:id=treesitter_query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_query_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Advanced Outline Parsing Specification

use compiler.treesitter.*

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-QUERY-001 to #TS-QUERY-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_query_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
```

## Scenarios

### OutlineModule Type Parameters

#### parses struct with type parameter

1. var ts = TreeSitter new
2. expect outline structs len
3. expect s type params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Box<T>:\n    value: T"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.name to_equal "Box"
expect s.type_params.len() to_equal 1
```

</details>

#### parses class with multiple type parameters

1. var ts = TreeSitter new
2. expect outline classes len
3. expect c type params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Pair<A, B>:\n    first: A\n    second: B"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.classes.len() to_equal 1
val c = outline.classes[0]
expect c.name to_equal "Pair"
expect c.type_params.len() to_equal 2
```

</details>

### OutlineModule Trait Parsing

#### parses trait with methods

1. var ts = TreeSitter new
2. expect outline traits len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "trait Drawable:\n    fn draw():\n        pass\n    fn area() -> f64:\n        0.0"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
val t = outline.traits[0]
expect t.name to_equal "Drawable"
```

</details>

#### parses empty trait

1. var ts = TreeSitter new
2. expect outline traits len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "trait Marker:\n    pass"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
val t = outline.traits[0]
expect t.name to_equal "Marker"
```

</details>

### OutlineModule Impl Parsing

#### parses impl with methods

1. var ts = TreeSitter new
2. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Point:\n    fn get_x() -> i64:\n        self.x\n    fn get_y() -> i64:\n        self.y"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
```

</details>

#### parses impl with static method

1. var ts = TreeSitter new
2. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "impl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
```

</details>

### OutlineModule Type Alias Parsing

#### parses type alias

1. var ts = TreeSitter new
2. expect outline type aliases len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "type Point2D = Point"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.type_aliases.len() to_equal 1
val ta = outline.type_aliases[0]
expect ta.name to_equal "Point2D"
```

</details>

### OutlineModule Const Parsing

#### parses val declaration

1. var ts = TreeSitter new
2. expect outline constants len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val PI = 3.14"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.constants.len() to_equal 1
val c = outline.constants[0]
expect c.name to_equal "PI"
expect c.is_mutable to_equal false
```

</details>

#### parses var declaration

1. var ts = TreeSitter new
2. expect outline constants len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var counter = 0"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.constants.len() to_equal 1
val c = outline.constants[0]
expect c.name to_equal "counter"
expect c.is_mutable to_equal true
```

</details>

### OutlineModule Mixed Advanced Declarations

#### parses traits and impls together

1. var ts = TreeSitter new
2. expect outline traits len
3. expect outline impls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "trait Shape:\n    fn area() -> f64:\n        0.0\n\nimpl Circle:\n    fn area() -> f64:\n        3.14"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
expect outline.impls.len() to_equal 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
