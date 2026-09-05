# Border + Box-Shadow Paint Specification

> Closes exit criterion 4 ("borders, box-shadow, transforms, gradients") for the blink render lane, borders and simple box-shadow only — see `src/lib/blink/paint/border_paint.spl`'s header for exactly what is and is not covered (no border-radius, no shadow blur/spread, no dash/dot pattern distinction, no transforms, no gradients).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Border + Box-Shadow Paint Specification

Closes exit criterion 4 ("borders, box-shadow, transforms, gradients") for the blink render lane, borders and simple box-shadow only — see `src/lib/blink/paint/border_paint.spl`'s header for exactly what is and is not covered (no border-radius, no shadow blur/spread, no dash/dot pattern distinction, no transforms, no gradients).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/paint/border_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Closes exit criterion 4 ("borders, box-shadow, transforms, gradients") for
the blink render lane, borders and simple box-shadow only — see
`src/lib/blink/paint/border_paint.spl`'s header for exactly what is and is
not covered (no border-radius, no shadow blur/spread, no dash/dot pattern
distinction, no transforms, no gradients).

These examples build a real HTML+CSS document through the same
parse->cascade->layout pipeline `style_paint_spec.spl` already proves, run it
through `paint_border_chunks_from_styled_layout` /
`paint_box_shadow_chunks_from_styled_layout`, and assert on the resulting
rect/colour arrays directly — same "inspect the data, not the pixels" scope
as the sibling spec.

@manual_section Browser Rendering

## Scenarios

### paint_border_chunks_from_styled_layout

#### emits 4 edge rects for a box with a uniform solid border on all sides

- emits 4 edge rects for a box with a uniform solid border on all sides
- style the first div with a 4px solid green border, sized 100x50
- flatten border edges into paint rects
- sabotage oracle: exactly 8 edge rects (4 per div, 2 divs) — not 0 (no-op) and not 1 per box (flat-rect shortcut)
   - Expected: rects.rect_count equals `8`
- every emitted rect is coloured opaque green
   - Expected: rects.colour[i as i32] equals `sk_color_argb(255, 0, 128, 0)`
- the top edge of the first div is 4px thick and spans the box width
   - Expected: rects.rect_h[0] equals `4`
   - Expected: rects.rect_w[0] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 4 edge rects for a box with a uniform solid border on all sides")
step("style the first div with a 4px solid green border, sized 100x50")
val css = "div { width: 100px; height: 50px; border: 4px solid green; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("flatten border edges into paint rects")
val rects = paint_border_chunks_from_styled_layout(layout)

step("sabotage oracle: exactly 8 edge rects (4 per div, 2 divs) — not 0 (no-op) and not 1 per box (flat-rect shortcut)")
expect(rects.rect_count).to_equal(8)

step("every emitted rect is coloured opaque green")
var i = 0
while i < rects.rect_count:
    expect(rects.colour[i as i32]).to_equal(sk_color_argb(255, 0, 128, 0))
    i = i + 1

step("the top edge of the first div is 4px thick and spans the box width")
expect(rects.rect_h[0]).to_equal(4)
expect(rects.rect_w[0]).to_equal(100)
```

</details>

#### contributes no rect for a box with border-style: none (the CSS default)

- contributes no rect for a box with border-style: none (the CSS default)
- size a div but declare no border at all
- no side paints: style defaults to none on every side of every box
   - Expected: rects.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contributes no rect for a box with border-style: none (the CSS default)")
step("size a div but declare no border at all")
val css = "div { width: 40px; height: 20px; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

val rects = paint_border_chunks_from_styled_layout(layout)

step("no side paints: style defaults to none on every side of every box")
expect(rects.rect_count).to_equal(0)
```

</details>

#### only the declared side paints when a single side is styled

- only the declared side paints when a single side is styled
- style only border-left on the first div
- exactly one edge rect: only .a's left side, nothing for .b (unstyled)
   - Expected: rects.rect_count equals `1`
   - Expected: rects.rect_w[0] equals `3`
   - Expected: rects.rect_h[0] equals `30`
   - Expected: rects.colour[0] equals `sk_color_argb(255, 0, 0, 255)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only the declared side paints when a single side is styled")
step("style only border-left on the first div")
val css = "div { width: 60px; height: 30px; } .a { border-left: 3px solid blue; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

val rects = paint_border_chunks_from_styled_layout(layout)

step("exactly one edge rect: only .a's left side, nothing for .b (unstyled)")
expect(rects.rect_count).to_equal(1)
expect(rects.rect_w[0]).to_equal(3)
expect(rects.rect_h[0]).to_equal(30)
expect(rects.colour[0]).to_equal(sk_color_argb(255, 0, 0, 255))
```

</details>

#### a zero-width border paints nothing even when border-style is solid

- a zero-width border paints nothing even when border-style is solid
- declare a solid style but 0px width
   - Expected: rects.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a zero-width border paints nothing even when border-style is solid")
step("declare a solid style but 0px width")
val css = "div { width: 40px; height: 20px; border: 0px solid red; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

val rects = paint_border_chunks_from_styled_layout(layout)
expect(rects.rect_count).to_equal(0)
```

</details>

### paint_box_shadow_chunks_from_styled_layout

#### emits one shadow rect per box that declares box-shadow, offset and sized to the box

- emits one shadow rect per box that declares box-shadow, offset and sized to the box
- give the first div a 5px/5px black shadow, sized 20x10
- sabotage oracle: exactly 1 rect (only .a declared box-shadow, not .b or body)
   - Expected: rects.rect_count equals `1`
- the shadow rect is the same size as the box, opaque black
   - Expected: rects.rect_w[0] equals `20`
   - Expected: rects.rect_h[0] equals `10`
   - Expected: rects.colour[0] equals `sk_color_argb(255, 0, 0, 0)`
- the shadow rect is offset from the box's own top-left by (5, 5)
   - Expected: rects.rect_x[0] equals `r.0.to_i64() + 5`
   - Expected: rects.rect_y[0] equals `r.1.to_i64() + 5`
   - Expected: "first div laid out" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits one shadow rect per box that declares box-shadow, offset and sized to the box")
step("give the first div a 5px/5px black shadow, sized 20x10")
val css = "div { width: 20px; height: 10px; } .a { box-shadow: 5px 5px black; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

val rects = paint_box_shadow_chunks_from_styled_layout(layout)

step("sabotage oracle: exactly 1 rect (only .a declared box-shadow, not .b or body)")
expect(rects.rect_count).to_equal(1)

step("the shadow rect is the same size as the box, opaque black")
expect(rects.rect_w[0]).to_equal(20)
expect(rects.rect_h[0]).to_equal(10)
expect(rects.colour[0]).to_equal(sk_color_argb(255, 0, 0, 0))

step("the shadow rect is offset from the box's own top-left by (5, 5)")
match layout.rect_for(2):
    Some(r):
        expect(rects.rect_x[0]).to_equal(r.0.to_i64() + 5)
        expect(rects.rect_y[0]).to_equal(r.1.to_i64() + 5)
    None:
        expect("first div laid out").to_equal("it did not")
```

</details>

#### contributes no rect when no box declares box-shadow

- contributes no rect when no box declares box-shadow
   - Expected: rects.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contributes no rect when no box declares box-shadow")
val css = "div { width: 20px; height: 10px; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)
val rects = paint_box_shadow_chunks_from_styled_layout(layout)
expect(rects.rect_count).to_equal(0)
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

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-BORDER-PAINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `940cf02ecaa6176455140494e4a3af30dc537f1d90d95d688bd89cd1394ed651`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `940cf02ecaa6176455140494e4a3af30dc537f1d90d95d688bd89cd1394ed651`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `940cf02ecaa6176455140494e4a3af30dc537f1d90d95d688bd89cd1394ed651`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/paint/border_paint_spec.spl
mirror: doc/06_spec/unit/lib/blink/paint/border_paint_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/paint/border_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/paint/border_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/paint/border_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/paint/border_paint_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/paint/border_paint_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 4 edge rects for a box with a uniform solid border on all sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/border_paint_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contributes no rect for a box with border-style: none (the CSS default)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/border_paint_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'only the declared side paints when a single side is styled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
