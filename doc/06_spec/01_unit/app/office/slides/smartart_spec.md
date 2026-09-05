# smartart_spec

> SmartArt diagram spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smartart_spec

SmartArt diagram spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/smartart_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

SmartArt diagram spec.

Verifies the SmartArt-style diagram model in `app.office.slides.smartart`:
auto-layout for "process" (horizontal chain), "list" (vertical stack), and
"hierarchy" (level-banded tree) diagrams, plus SVG rendering with the
expected rects and connector lines. All positions below are hand-computed
from the stated layout rules, not just re-derived from the implementation.

## Scenarios

### smartart: process layout (horizontal chain)

#### places three equal-width boxes left to right at x=0,300,600

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("process")
diagram = diagram_add(diagram, node_new("A", "Start", 0))
diagram = diagram_add(diagram, node_new("B", "Middle", 0))
diagram = diagram_add(diagram, node_new("C", "End", 0))
val lines = diagram_layout(diagram, 900, 200)
expect(lines).to_equal([
    "A@0,0 300x200: Start",
    "B@300,0 300x200: Middle",
    "C@600,0 300x200: End"
])
```

</details>

#### renders 3 rects and 2 connector lines chaining box N to N+1 center-to-center

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("process")
diagram = diagram_add(diagram, node_new("A", "Start", 0))
diagram = diagram_add(diagram, node_new("B", "Middle", 0))
diagram = diagram_add(diagram, node_new("C", "End", 0))
val svg = diagram_to_svg(diagram, 900, 200)
val rect_parts = svg.split("<rect")
val line_parts = svg.split("<line")
expect(rect_parts.len() - 1).to_equal(3)
expect(line_parts.len() - 1).to_equal(2)
# Box centers: A@150,100  B@450,100  C@750,100 (each box is 300x200)
expect(svg).to_contain("<line x1=\"150\" y1=\"100\" x2=\"450\" y2=\"100\"/>")
expect(svg).to_contain("<line x1=\"450\" y1=\"100\" x2=\"750\" y2=\"100\"/>")
```

</details>

### smartart: list layout (vertical stack)

#### places three full-width boxes top to bottom at y=0,100,200

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("list")
diagram = diagram_add(diagram, node_new("X", "First", 0))
diagram = diagram_add(diagram, node_new("Y", "Second", 0))
diagram = diagram_add(diagram, node_new("Z", "Third", 0))
val lines = diagram_layout(diagram, 400, 300)
expect(lines).to_equal([
    "X@0,0 400x100: First",
    "Y@0,100 400x100: Second",
    "Z@0,200 400x100: Third"
])
```

</details>

#### renders 3 rects with no connector lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("list")
diagram = diagram_add(diagram, node_new("X", "First", 0))
diagram = diagram_add(diagram, node_new("Y", "Second", 0))
val svg = diagram_to_svg(diagram, 400, 200)
val rect_parts = svg.split("<rect")
val line_parts = svg.split("<line")
expect(rect_parts.len() - 1).to_equal(2)
expect(line_parts.len() - 1).to_equal(0)
```

</details>

### smartart: hierarchy layout (level-banded tree)

#### centers the root box at the top

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("hierarchy")
diagram = diagram_add(diagram, node_new("R", "Root", 0))
diagram = diagram_add(diagram, node_new("C1", "Child 1", 1))
diagram = diagram_add(diagram, node_new("C2", "Child 2", 1))
val lines = diagram_layout(diagram, 900, 400)
expect(lines[0]).to_equal("R@225,0 450x200: Root")
```

</details>

#### places the children on a lower row spread across the width

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("hierarchy")
diagram = diagram_add(diagram, node_new("R", "Root", 0))
diagram = diagram_add(diagram, node_new("C1", "Child 1", 1))
diagram = diagram_add(diagram, node_new("C2", "Child 2", 1))
val lines = diagram_layout(diagram, 900, 400)
expect(lines[1]).to_equal("C1@0,200 450x200: Child 1")
expect(lines[2]).to_equal("C2@450,200 450x200: Child 2")
```

</details>

#### renders 3 rects and 2 connector lines from each child to the root

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("hierarchy")
diagram = diagram_add(diagram, node_new("R", "Root", 0))
diagram = diagram_add(diagram, node_new("C1", "Child 1", 1))
diagram = diagram_add(diagram, node_new("C2", "Child 2", 1))
val svg = diagram_to_svg(diagram, 900, 400)
val rect_parts = svg.split("<rect")
val line_parts = svg.split("<line")
expect(rect_parts.len() - 1).to_equal(3)
expect(line_parts.len() - 1).to_equal(2)
expect(svg).to_contain("<line x1=\"450\" y1=\"100\" x2=\"225\" y2=\"300\"/>")
expect(svg).to_contain("<line x1=\"450\" y1=\"100\" x2=\"675\" y2=\"300\"/>")
```

</details>

### smartart: node count

#### counts nodes as they are added

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("list")
expect(diagram_node_count(diagram)).to_equal(0)
diagram = diagram_add(diagram, node_new("X", "First", 0))
diagram = diagram_add(diagram, node_new("Y", "Second", 0))
expect(diagram_node_count(diagram)).to_equal(2)
```

</details>

### deliberate-fail probe (fixed to green)

#### has exactly three nodes after three adds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diagram = diagram_new("process")
diagram = diagram_add(diagram, node_new("A", "Start", 0))
diagram = diagram_add(diagram, node_new("B", "Middle", 0))
diagram = diagram_add(diagram, node_new("C", "End", 0))
expect(diagram_node_count(diagram)).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
