# web_layout_paint_spec

> Verifies the web layout paint behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_layout_paint_spec

Verifies the web layout paint behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_layout_paint_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the web layout paint behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### tiny Web block layout and paint records

#### lays out and paints admitted content in a bounded viewport

- Verify: lays out and paints admitted content in a bounded viewport
   - Expected: layout.panes.len() equals `layout.nodes.len()`
   - Expected: layout.panes[2].absolute.x equals `layout.nodes[2].bounds.x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_LAYOUT_PAINT-001
step("Verify: lays out and paints admitted content in a bounded viewport")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_web_parse("<body><div><p>Hello</p><button>Go</button><input></div></body>", 16, 8, 64)
val layout = tiny_web_layout(parsed, TinyRect(x: 0, y: 0, width: 120, height: 80), 12, 16)
expect(layout.status.is_ok()).to_be(true)
expect(layout.content_height).to_be_greater_than(0)
expect(layout.panes.len()).to_equal(layout.nodes.len())
expect(layout.panes[2].absolute.x).to_equal(layout.nodes[2].bounds.x)
expect(layout.panes[2].effective_clip.width).to_be_greater_than(0)
val painted = tiny_web_paint(layout, 16)
expect(painted.status.is_ok()).to_be(true)
var has_text = false
var has_border = false
for record in painted.records:
    if record.opcode == TINY_PAINT_GLYPH_RUN: has_text = true
    if record.opcode == TINY_PAINT_BORDER_RECT: has_border = true
expect(has_text).to_be(true)
expect(has_border).to_be(true)
val draw = tiny_web_paint_to_draw(painted, 128)
expect(draw.status.is_ok()).to_be(true)
expect(draw.word_count).to_be_greater_than(1)
```

</details>

#### emits one glyph command per Unicode scalar and rejects unknown paint operations

- Verify: emits one glyph command per Unicode scalar and rejects unknown paint operations
   - Expected: draw.word_count equals `27)  # oracle: pinned constant asserted by this scenario`
   - Expected: draw.stream[0] equals `TINY_DRAW_GLYPH_MONO`
   - Expected: draw.stream[1] equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: draw.stream[13] equals `TINY_DRAW_GLYPH_MONO`
   - Expected: draw.stream[14] equals `9)  # oracle: pinned constant asserted by this scenario`
   - Expected: draw.stream[26] equals `TINY_DRAW_END`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_LAYOUT_PAINT-001
step("Verify: emits one glyph command per Unicode scalar and rejects unknown paint operations")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val paint = TinyWebPaintResult(
    status: TinyStatus.ok(),
    records: [TinyPaintRecord(opcode: TINY_PAINT_GLYPH_RUN, bounds: TinyRect(x: 3, y: 4, width: 20, height: 7), color: 9, text_value: "Aé")],
)
val draw = tiny_web_paint_to_draw(paint, 32)
expect(draw.status.is_ok()).to_be(true)
expect(draw.word_count).to_equal(27)  # oracle: pinned constant asserted by this scenario
expect(draw.stream[0]).to_equal(TINY_DRAW_GLYPH_MONO)
expect(draw.stream[1]).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(draw.stream[13]).to_equal(TINY_DRAW_GLYPH_MONO)
expect(draw.stream[14]).to_equal(9)  # oracle: pinned constant asserted by this scenario
expect(draw.stream[26]).to_equal(TINY_DRAW_END)

val unknown = TinyWebPaintResult(
    status: paint.status,
    records: [TinyPaintRecord(opcode: 999, bounds: TinyRect.empty(), color: 0, text_value: "")],
)
expect(tiny_web_paint_to_draw(unknown, 8).status.is_ok()).to_be(false)
```

</details>

#### rejects invalid viewport and layout or paint capacity

- Verify: rejects invalid viewport and layout or paint capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_LAYOUT_PAINT-001
step("Verify: rejects invalid viewport and layout or paint capacity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_web_parse("<body><p>Hello</p></body>", 8, 8, 64)
expect(tiny_web_layout(parsed, TinyRect.empty(), 12, 8).status.is_ok()).to_be(false)
expect(tiny_web_layout(parsed, TinyRect(x: 0, y: 0, width: 100, height: 40), 12, 1).status.is_ok()).to_be(false)
val layout = tiny_web_layout(parsed, TinyRect(x: 0, y: 0, width: 100, height: 40), 12, 8)
expect(tiny_web_paint(layout, 1).status.is_ok()).to_be(false)
val painted = tiny_web_paint(layout, 8)
expect(tiny_web_paint_to_draw(painted, 2).status.is_ok()).to_be(false)
```

</details>

#### cascades bounded CSS into layout and paint while hiding non-rendered content

- Verify: cascades bounded CSS into layout and paint while hiding non-rendered content
   - Expected: main_width equals `40)  # oracle: pinned constant asserted by this scenario`
   - Expected: css_text_color equals `-16776961)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_LAYOUT_PAINT-001
step("Verify: cascades bounded CSS into layout and paint while hiding non-rendered content")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_web_parse("<html><head><title>Hidden title</title><style>#main { width: 40px; background-color: red; color: blue; line-height: 20px } .hidden { display: none }</style></head><body><div id='main'><p>Shown</p><p class='hidden'>Gone</p></div></body></html>", 24, 10, 256)
val layout = tiny_web_layout(parsed, TinyRect(x: 0, y: 0, width: 100, height: 80), 12, 24)
expect(layout.status.is_ok()).to_be(true)
expect(layout.css_status.is_ok()).to_be(true)
var main_width = -1
var gone_visible = false
var index = 0
while index < layout.nodes.len():
    if layout.nodes[index].id_value == "main": main_width = layout.nodes[index].bounds.width
    if layout.nodes[index].text_value == "Gone": gone_visible = layout.rendered[index]
    index = index + 1
expect(main_width).to_equal(40)  # oracle: pinned constant asserted by this scenario
expect(gone_visible).to_be(false)
val painted = tiny_web_paint(layout, 24)
expect(painted.status.is_ok()).to_be(true)
var shown = false
var hidden = false
var css_text_color = 0
for record in painted.records:
    if record.text_value == "Shown":
        shown = true
        css_text_color = record.color
    if record.text_value == "Gone" or record.text_value == "Hidden title": hidden = true
expect(shown).to_be(true)
expect(hidden).to_be(false)
expect(css_text_color).to_equal(-16776961)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5be1d19ce1eccab5311156cb5eadf8c87e24f6aedf01fd7885a7727c01f5ff3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5be1d19ce1eccab5311156cb5eadf8c87e24f6aedf01fd7885a7727c01f5ff3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5be1d19ce1eccab5311156cb5eadf8c87e24f6aedf01fd7885a7727c01f5ff3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/web_layout_paint_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
