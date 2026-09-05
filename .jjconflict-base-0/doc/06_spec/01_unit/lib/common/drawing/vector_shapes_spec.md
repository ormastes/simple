# vector_shapes_spec

> Vector shape / SVG render spec (LibreOffice Draw).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vector_shapes_spec

Vector shape / SVG render spec (LibreOffice Draw).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/drawing/vector_shapes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vector shape / SVG render spec (LibreOffice Draw).

Verifies the Draw component's vector-graphics model: shapes (rect/line/circle/
label) on a canvas render to an SVG document. Integer coordinates are used so the
model is verifiable without the f64 toolchain bug that blocks the Skia
primitives.

Shape counts and the text attributes (fill/stroke, SVG structure) are asserted
here; the exact integer coordinate values in the SVG are verified via direct
`bin/simple run` (the runner's compiled mode is unreliable for i32 string
interpolation — same toolchain fragility tracked in the f64 bug doc). A probe
canvas with a rect, circle, and label renders to a complete, well-formed SVG.

## Scenarios

### vector draw: canvas shape model

#### starts empty

- starts empty
   - Expected: canvas_shape_count(c) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts empty")
val c = empty_canvas(200, 100)
expect(canvas_shape_count(c)).to_equal(0)
```

</details>

#### accumulates added shapes

- accumulates added shapes
   - Expected: canvas_shape_count(c) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accumulates added shapes")
var c = empty_canvas(200, 100)
c = add_shape(c, DrawShape.Rect(x: 10, y: 20, w: 50, h: 30, fill: "red"))
c = add_shape(c, DrawShape.Circle(cx: 100, cy: 50, r: 25, fill: "blue"))
expect(canvas_shape_count(c)).to_equal(2)
```

</details>

### vector draw: SVG rendering
_Shapes render to well-formed SVG elements._

#### wraps the canvas in an svg root

- wraps the canvas in an svg root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wraps the canvas in an svg root")
val c = empty_canvas(200, 100)
val svg = canvas_to_svg(c)
expect(svg).to_start_with("<svg ")
expect(svg).to_end_with("</svg>")
```

</details>

#### renders a rect element with its fill

- renders a rect element with its fill


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a rect element with its fill")
val svg = shape_to_svg(DrawShape.Rect(x: 10, y: 20, w: 50, h: 30, fill: "red"))
expect(svg).to_start_with("<rect ")
expect(svg).to_contain("fill=\"red\"")
```

</details>

#### renders a circle element with its fill

- renders a circle element with its fill


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a circle element with its fill")
val svg = shape_to_svg(DrawShape.Circle(cx: 100, cy: 50, r: 25, fill: "blue"))
expect(svg).to_start_with("<circle ")
expect(svg).to_contain("fill=\"blue\"")
```

</details>

#### renders a label with its content

- renders a label with its content


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a label with its content")
val svg = shape_to_svg(DrawShape.Label(x: 5, y: 90, content: "Hi"))
expect(svg).to_contain(">Hi</text>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2977eb1226e801d14f7a58b031b6d7cdcab3d3af1a40b706d3e1351f6ff957c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2977eb1226e801d14f7a58b031b6d7cdcab3d3af1a40b706d3e1351f6ff957c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2977eb1226e801d14f7a58b031b6d7cdcab3d3af1a40b706d3e1351f6ff957c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/drawing/vector_shapes_spec.spl
mirror: doc/06_spec/01_unit/lib/common/drawing/vector_shapes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/drawing/vector_shapes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/drawing/vector_shapes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/drawing/vector_shapes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/drawing/vector_shapes_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/drawing/vector_shapes_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accumulates added shapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/drawing/vector_shapes_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps the canvas in an svg root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
