# treesitter_highlights_spec

> TreeSitter Highlights Specification

<!-- sdn-diagram:id=treesitter_highlights_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_highlights_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_highlights_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_highlights_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# treesitter_highlights_spec

TreeSitter Highlights Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-HL-001 |
| Category | Compiler \| Parser |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_highlights_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

TreeSitter Highlights Specification

@cover src/compiler/10.frontend/treesitter.spl 80%

Tests outline extraction of items relevant to syntax highlighting:
functions, classes, enums, and their structural properties.

## Scenarios

### TreeSitter Highlight-Relevant Parsing

#### extracts function with parameters for highlight

1. var ts = TreeSitter new
   - Expected: f.name equals `greet`
   - Expected: f.params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn greet(name: text) -> text:\n    name\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
val f = outline.functions[0]
expect(f.name).to_equal("greet")
expect(f.params.len()).to_equal(1)
```

</details>

#### extracts class fields for highlight

1. var ts = TreeSitter new
   - Expected: outline.classes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class Color:\n    r: i64\n    g: i64\n    b: i64\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.classes.len()).to_equal(1)
```

</details>

#### extracts enum variants for highlight

1. var ts = TreeSitter new
   - Expected: outline.enums.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "enum Direction:\n    North\n    South\n    East\n    West\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.enums.len()).to_equal(1)
```

</details>

#### extracts static method for highlight

1. var ts = TreeSitter new
   - Expected: outline.classes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class Point:\n    x: i64\n    y: i64\n\nimpl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.classes.len()).to_equal(1)
```

</details>

#### extracts import statement

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "use std.io\n\nfn main():\n    0\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.imports.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
