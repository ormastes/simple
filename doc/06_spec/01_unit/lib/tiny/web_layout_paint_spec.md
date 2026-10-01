# Web Layout Paint Specification

> Tests covering tiny Web block layout and paint records.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Layout Paint Specification

## Scenarios

### tiny Web block layout and paint records

#### lays out and paints admitted content in a bounded viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### emits one glyph command per Unicode scalar and rejects unknown paint operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paint = TinyWebPaintResult(
    status: TinyStatus.ok(),
    records: [TinyPaintRecord(opcode: TINY_PAINT_GLYPH_RUN, bounds: TinyRect(x: 3, y: 4, width: 20, height: 7), color: 9, text_value: "Aé")],
)
val draw = tiny_web_paint_to_draw(paint, 32)
expect(draw.status.is_ok()).to_be(true)
expect(draw.word_count).to_equal(27)
expect(draw.stream[0]).to_equal(TINY_DRAW_GLYPH_MONO)
expect(draw.stream[1]).to_equal(3)
expect(draw.stream[13]).to_equal(TINY_DRAW_GLYPH_MONO)
expect(draw.stream[14]).to_equal(9)
expect(draw.stream[26]).to_equal(TINY_DRAW_END)

val unknown = TinyWebPaintResult(
    status: paint.status,
    records: [TinyPaintRecord(opcode: 999, bounds: TinyRect.empty(), color: 0, text_value: "")],
)
expect(tiny_web_paint_to_draw(unknown, 8).status.is_ok()).to_be(false)
```

</details>

#### rejects invalid viewport and layout or paint capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(main_width).to_equal(40)
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
expect(css_text_color).to_equal(-16776961)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_layout_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tiny Web block layout and paint records.
- tiny Web block layout and paint records

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2562debd1fb410f79f6115a6122acebace14d96fe484f36f6c8b24a7073071a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2562debd1fb410f79f6115a6122acebace14d96fe484f36f6c8b24a7073071a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2562debd1fb410f79f6115a6122acebace14d96fe484f36f6c8b24a7073071a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/tiny/web_layout_paint_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_layout_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/web_layout_paint_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/web_layout_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/web_layout_paint_spec.spl:18:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'lays out and paints admitted content in a bounded viewport' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_layout_paint_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'emits one glyph command per Unicode scalar and rejects unknown paint operations' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_layout_paint_spec.spl:61:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects invalid viewport and layout or paint capacity' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_layout_paint_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'cascades bounded CSS into layout and paint while hiding non-rendered content' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
