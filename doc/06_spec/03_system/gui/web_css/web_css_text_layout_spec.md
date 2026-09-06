# Web CSS Text Layout System Test

> A reader wants to know whether the headless web/HTML-CSS renderer's Draw IR

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Text Layout System Test

A reader wants to know whether the headless web/HTML-CSS renderer's Draw IR

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.4) |
| Source | `test/03_system/gui/web_css/web_css_text_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer's Draw IR
carries correct computed text-layout facts: the resolved `text-align` value
reaching a text run's computed style, `line-height` spacing between stacked
text runs, `white-space: pre` preserving literal whitespace runs, and
`text-transform: uppercase` rewriting glyph content without touching the
renderer's fixed-advance width model.

## Scope and Preconditions

Runs entirely in-process, headless, no display server:
`simple_web_layout_render_html_draw_ir(html, width, height)` produces a
`common.ui.draw_ir.DrawIrComposition`. Assertions read real `DrawIrCommand`
fields (`x`/`y`/`width`/`height`/`text_value`/`computed_style`) off the actual
renderer output — never a "didn't crash" check.

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the `kind ==
"text"` command for a named element, and assert exact computed geometry,
text-run content, or forwarded computed-style values.

## Evidence and Provenance

DrawIR-tree oracle per plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`
(`_html_draw_ir_command`, `simple_web_html_layout_renderer_decl_apply.spl`
text-align resolution).

## A genuine renderer-architecture finding (read before editing this file)

`_html_draw_ir_command` (`simple_web_html_layout_renderer_paint_layout.spl:1900`)
emits exactly one Draw IR `text` command per `#text` HNode, built straight from
`node.text_trimmed` at the node's own box position. It never calls
`text_line_aligned_x` or `ellipsize_text_for_width` — those two functions are
called only from the separate CPU-framebuffer raster loops further up the same
file (`:1013`/`:1019`, `:1047`/`:1053`), which paint to a pixel buffer for
software/widget output, not to the Draw IR tree. Two consequences that this
spec asserts directly instead of guessing past:
- `text-align` never repositions a Draw IR text command's `x` — it only rides
  along in `computed_style["text-align"]`, resolved by
  `simple_web_html_layout_renderer_decl_apply.spl:1040-1042`. This spec tests
  that resolution (and is the sabotage target below), not on-canvas geometry.
- Draw IR composition never splits one `#text` node into multiple line
  commands, so `overflow-wrap` still has zero effect on the Draw IR tree and
  remains asserted RED-by-design (bug record below). `text-overflow:
  ellipsis` was the same kind of gap but is narrower — it only needed
  `_html_draw_ir_command` to call the already-existing
  `ellipsize_text_for_width` before emitting/measuring the text run, not a
  line-splitting subsystem — and is now fixed (2026-08-07); its `it` block
  below is green.

## Scenarios

### Web CSS text layout

#### text-align: center resolves onto the text run's computed style

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Text layout geometry and computed style" (expected show, folded, detail, or skip)


- text-align: center resolves onto the text run's computed style
- Render a div with text-align:center and a div with text-align:left
- Assert the resolved text-align value is forwarded onto the text run's computed style
   - Expected: _draw_ir_style_prop_value(text_center, "text-align") equals `center`
   - Expected: _draw_ir_style_prop_value(text_left, "text-align") equals `left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("text-align: center resolves onto the text run's computed style")
step("Render a div with text-align:center and a div with text-align:left")
val html_center = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:60px;height:20px;background-color:#e5e7eb;" +
    "text-align:center;font-size:8px}" +
    "</style></head><body><div id='box'>Hi</div></body></html>"
)
val html_left = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:60px;height:20px;background-color:#e5e7eb;" +
    "text-align:left;font-size:8px}" +
    "</style></head><body><div id='box'>Hi</div></body></html>"
)
val composition_center = simple_web_layout_render_html_draw_ir(html_center, 64, 64)
val composition_left = simple_web_layout_render_html_draw_ir(html_left, 64, 64)
val text_center = _draw_ir_first_text_command(composition_center.batches[0].commands)
val text_left = _draw_ir_first_text_command(composition_left.batches[0].commands)

step("Assert the resolved text-align value is forwarded onto the text run's computed style")
expect(_draw_ir_style_prop_value(text_center, "text-align")).to_equal("center")
expect(_draw_ir_style_prop_value(text_left, "text-align")).to_equal("left")
```

</details>

#### line-height spaces stacked lines by the specified amount

- line-height spaces stacked lines by the specified amount
- Render two text nodes separated by a line break under a fixed line-height
- Assert the second stacked line starts exactly one line-height below the first
   - Expected: first_text.text_value equals `a`
   - Expected: second_text.text_value equals `b`
   - Expected: second_text.y equals `first_text.y + 20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("line-height spaces stacked lines by the specified amount")
step("Render two text nodes separated by a line break under a fixed line-height")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:60px;height:60px;background-color:#e5e7eb;" +
    "line-height:20px;font-size:8px}" +
    "</style></head><body><div id='box'>a<br/>b</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
var first_text: DrawIrCommand = commands[0]
var second_text: DrawIrCommand = commands[0]
var seen_first = false
var idx = 0
while idx < commands.len():
    if commands[idx].kind == "text":
        if not seen_first:
            first_text = commands[idx]
            seen_first = true
        else:
            second_text = commands[idx]
    idx = idx + 1

step("Assert the second stacked line starts exactly one line-height below the first")
expect(first_text.text_value).to_equal("a")
expect(second_text.text_value).to_equal("b")
expect(second_text.y).to_equal(first_text.y + 20)
```

</details>

#### white-space: pre preserves runs of spaces and newlines

- white-space: pre preserves runs of spaces and newlines
- Render a div with white-space:pre and a run of interior spaces
- Assert the three interior spaces survive instead of collapsing to one
   - Expected: text.text_value equals `a   b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("white-space: pre preserves runs of spaces and newlines")
step("Render a div with white-space:pre and a run of interior spaces")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:60px;height:20px;background-color:#e5e7eb;" +
    "white-space:pre;font-size:8px}" +
    "</style></head><body><div id='box'>a   b</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val text = _draw_ir_first_text_command(composition.batches[0].commands)

step("Assert the three interior spaces survive instead of collapsing to one")
expect(text.text_value).to_equal("a   b")
```

</details>

#### overflow-wrap breaks a long unbreakable word at the container edge

- overflow-wrap breaks a long unbreakable word at the container edge
- Render a 20px-wide box with a 10-character unbreakable word and overflow-wrap:break-word
- Assert the word broke into more than one line command at the 20px edge (currently false)


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overflow-wrap breaks a long unbreakable word at the container edge")
"""
RED-by-design: `overflow_wrap` is stored on `Style` (assigned from
the cascaded declaration in `simple_web_html_layout_renderer_style.spl`)
but has zero conditional readers anywhere in the browser_engine
module family — `grep -rn "overflow_wrap ==" src/lib/gc_async_mut/gpu/
browser_engine/*.spl` returns nothing. `_html_draw_ir_command` always
emits one unbroken text command per `#text` node regardless of
container width. Filed:
doc/08_tracking/bug/web_css_overflow_wrap_zero_consumer_2026-08-07.md
"""
step("Render a 20px-wide box with a 10-character unbreakable word and overflow-wrap:break-word")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:20px;height:60px;background-color:#e5e7eb;" +
    "overflow-wrap:break-word;font-size:8px}" +
    "</style></head><body><div id='box'>abcdefghij</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands

step("Assert the word broke into more than one line command at the 20px edge (currently false)")
expect(_draw_ir_text_command_count(commands) > 1).to_be(true)
```

</details>

#### text-transform: uppercase changes glyphs not layout width class

- text-transform: uppercase changes glyphs not layout width class
- Render text-transform:uppercase alongside the equivalent literal-uppercase text
- Assert the glyph content uppercased, and its measured width matches literal-uppercase text (same fixed-advance width class)
   - Expected: text_transformed.text_value equals `HI`
   - Expected: text_transformed.width equals `text_literal.width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("text-transform: uppercase changes glyphs not layout width class")
step("Render text-transform:uppercase alongside the equivalent literal-uppercase text")
val html_transformed = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:60px;height:20px;background-color:#e5e7eb;" +
    "text-transform:uppercase;font-size:8px}" +
    "</style></head><body><div id='box'>hi</div></body></html>"
)
val html_literal = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:60px;height:20px;background-color:#e5e7eb;font-size:8px}" +
    "</style></head><body><div id='box'>HI</div></body></html>"
)
val composition_transformed = simple_web_layout_render_html_draw_ir(html_transformed, 64, 64)
val composition_literal = simple_web_layout_render_html_draw_ir(html_literal, 64, 64)
val text_transformed = _draw_ir_first_text_command(composition_transformed.batches[0].commands)
val text_literal = _draw_ir_first_text_command(composition_literal.batches[0].commands)

step("Assert the glyph content uppercased, and its measured width matches literal-uppercase text (same fixed-advance width class)")
expect(text_transformed.text_value).to_equal("HI")
expect(text_transformed.width).to_equal(text_literal.width)
```

</details>

#### text-overflow: ellipsis truncates a single-line overflowing box

- text-overflow: ellipsis truncates a single-line overflowing box
- Render a 30px-wide box with overflow:hidden, white-space:nowrap, and text-overflow:ellipsis over a long word
- Assert the text run's measured width fits inside the 30px box (currently it overflows to 65px)


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("text-overflow: ellipsis truncates a single-line overflowing box")
"""
Fixed 2026-08-07: `_html_draw_ir_command`
(`simple_web_html_layout_renderer_paint_layout.spl:1900`) now calls
`ellipsize_text_for_width` (`simple_web_html_layout_
renderer_layout.spl:590`) on the node's text before emitting or
measuring the Draw IR text run, whenever `st.text_overflow_ellipsis`
is set — the same fixed-advance width model the CPU-framebuffer
raster loops already used at `:1013`/`:1047`. Previously this call
existed only in those raster loops, never in the Draw IR builder, so
the Draw IR text run always carried the full untruncated string and
its full measured width regardless of `text-overflow: ellipsis`.
History: doc/08_tracking/bug/web_css_text_overflow_ellipsis_draw_ir_gap_2026-08-07.md
"""
step("Render a 30px-wide box with overflow:hidden, white-space:nowrap, and text-overflow:ellipsis over a long word")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#box{width:30px;height:10px;background-color:#e5e7eb;" +
    "white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-size:8px}" +
    "</style></head><body><div id='box'>abcdefghijklmnop</div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val text = _draw_ir_first_text_command(composition.batches[0].commands)

step("Assert the text run's measured width fits inside the 30px box (currently it overflows to 65px)")
expect(text.width <= 30).to_be(true)
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


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.4)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e1f13c96711126ca38b943aff88ee4036c8a5d2027c2091cfb7e61303e6b25b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e1f13c96711126ca38b943aff88ee4036c8a5d2027c2091cfb7e61303e6b25b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e1f13c96711126ca38b943aff88ee4036c8a5d2027c2091cfb7e61303e6b25b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_text_layout_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_text_layout_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_text_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_text_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_text_layout_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_text_layout_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'text-align: center resolves onto the text run's computed style' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_text_layout_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'line-height spaces stacked lines by the specified amount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_text_layout_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'white-space: pre preserves runs of spaces and newlines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
