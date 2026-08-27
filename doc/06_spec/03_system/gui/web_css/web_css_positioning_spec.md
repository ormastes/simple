# Web CSS Positioning System Test

> A reader wants to know whether the headless web/HTML-CSS renderer computes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Positioning System Test

A reader wants to know whether the headless web/HTML-CSS renderer computes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.7) |
| Source | `test/03_system/gui/web_css/web_css_positioning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer computes
CSS positioning geometry correctly: `position: relative` offsetting a box's
own paint rect without disturbing sibling flow, `position: absolute`
resolving its offset against the nearest positioned ancestor's box (not the
viewport or the immediate DOM parent), `position: fixed` anchoring to the
viewport regardless of ancestor offsets, `z-index` reordering the paint order
of overlapping positioned boxes, `clear` moving a block below preceding
floated content, and `float` taking a box out of normal flow so following
inline content wraps beside it.

## Scope and Preconditions

Runs entirely in-process, headless, no display server: assertions read real
`DrawIrCommand.x`/`.y`/`.width`/`.height` fields off
`simple_web_layout_render_html_draw_ir(html, width, height)` output — never a
"didn't crash" check. Paint order (for z-index) is read from the position of
each element's command within `composition.batches[0].commands`.

## A genuine renderer-architecture finding (read before editing this file)

Probed directly against this renderer before writing assertions (not assumed
from the CSS spec): `position: fixed` parses correctly into
`Style.position_fixed` (`simple_web_html_layout_renderer_decl_apply.spl:800`)
but that field is read back only by a debug `getComputedStyle`-style text
accessor (`simple_web_html_layout_renderer_core.spl:3028`) — no layout pass
ever branches on it to establish the viewport as the containing block, so a
fixed-positioned box's offset resolves against its nearest DOM ancestor's box
exactly like `position: absolute` would, instead of the viewport. See
`it "position: fixed anchors to the viewport"` below (RED-by-design; bug
filed: `doc/08_tracking/bug/browser_engine_css_position_fixed_not_viewport_anchored_2026-08-08.md`).

Separately, `float` is already tracked as unimplemented
(`doc/08_tracking/bug/browser_engine_css_float_layout_unimplemented_2026-07-20.md`):
two `float: left` siblings stack vertically instead of sitting side by side,
and a paragraph following a float starts below it instead of wrapping beside
it. Because floated boxes never leave normal flow, a following block already
lands below them with or without `clear` — so `clear` currently has no
independent, observable effect either; that same bug doc has been updated
with this spec's citation rather than filing a duplicate. Both `it` blocks
below (`"float: left takes a box out of flow with text wrap"` and `"clear
moves a block below preceding content"`) are RED-by-design for that shared
root cause.

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the command
for a named element by `component_id` (or the first `kind == "text"` command
for the float/wrap case), and assert exact computed geometry or paint-order
position.

## Evidence and Provenance

DrawIR-tree oracle per plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl`.

## Scenarios

### Web CSS positioning

#### position: relative offsets paint without moving siblings

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Positioning" (expected show, folded, detail, or skip)


- position: relative offsets paint without moving siblings
- Render a relatively-offset block followed by a plain sibling
- Assert the relatively-positioned box painted at its static position plus its own left/top offset
   - Expected: r1.x equals `5`
   - Expected: r1.y equals `3`
- Assert the following sibling flows as if r1 had never been offset: r2 starts at r1's UNOFFSET static x (0) and at r1's static height below (10), proving relative offset is paint-only
   - Expected: r2.x equals `0`
   - Expected: r2.y equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("position: relative offsets paint without moving siblings")
step("Render a relatively-offset block followed by a plain sibling")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#r1{display:block;width:20px;height:10px;background-color:#3b82f6;" +
    "position:relative;left:5px;top:3px}" +
    "#r2{display:block;width:20px;height:10px;background-color:#22c55e}" +
    "</style></head><body><div id='r1'></div><div id='r2'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val r1 = _draw_ir_command_by_id(composition.batches[0].commands, "r1")
val r2 = _draw_ir_command_by_id(composition.batches[0].commands, "r2")

step("Assert the relatively-positioned box painted at its static position plus its own left/top offset")
expect(r1.x).to_equal(5)
expect(r1.y).to_equal(3)

step("Assert the following sibling flows as if r1 had never been offset: r2 starts at r1's UNOFFSET static x (0) and at r1's static height below (10), proving relative offset is paint-only")
expect(r2.x).to_equal(0)
expect(r2.y).to_equal(10)
```

</details>

#### position: absolute anchors to the nearest positioned ancestor

- position: absolute anchors to the nearest positioned ancestor
- Render a relatively-positioned ancestor containing an absolutely-positioned child
- Assert the positioned ancestor itself sits at its own margin offset
   - Expected: anc.x equals `5`
   - Expected: anc.y equals `5`
- Assert the absolutely-positioned child's box is the ancestor's own box origin plus the child's left/top offset, not the viewport origin plus the offset
   - Expected: abs_box.x equals `anc.x + 2`
   - Expected: abs_box.y equals `anc.y + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("position: absolute anchors to the nearest positioned ancestor")
step("Render a relatively-positioned ancestor containing an absolutely-positioned child")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#anc{display:block;position:relative;width:40px;height:40px;margin:5px;" +
    "background-color:#3b82f6}" +
    "#abs{position:absolute;left:2px;top:3px;width:10px;height:10px;" +
    "background-color:#22c55e}" +
    "</style></head><body><div id='anc'><div id='abs'></div></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val anc = _draw_ir_command_by_id(composition.batches[0].commands, "anc")
val abs_box = _draw_ir_command_by_id(composition.batches[0].commands, "abs")

step("Assert the positioned ancestor itself sits at its own margin offset")
expect(anc.x).to_equal(5)
expect(anc.y).to_equal(5)

step("Assert the absolutely-positioned child's box is the ancestor's own box origin plus the child's left/top offset, not the viewport origin plus the offset")
expect(abs_box.x).to_equal(anc.x + 2)
expect(abs_box.y).to_equal(anc.y + 3)
```

</details>

#### position: fixed anchors to the viewport

- position: fixed anchors to the viewport
- Render a margined, non-positioned wrapper containing a fixed-positioned box
- Assert the fixed box resolves its left/top offset against the viewport origin (0,0), ignoring the 20px-margined ancestor entirely -- RED-by-design, see header finding and bug doc
   - Expected: fx.x equals `1`
   - Expected: fx.y equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("position: fixed anchors to the viewport")
step("Render a margined, non-positioned wrapper containing a fixed-positioned box")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#wrap{display:block;margin:20px;width:10px;height:10px}" +
    "#fx{position:fixed;left:1px;top:2px;width:8px;height:8px;" +
    "background-color:#ff0000}" +
    "</style></head><body><div id='wrap'><div id='fx'></div></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val fx = _draw_ir_command_by_id(composition.batches[0].commands, "fx")

step("Assert the fixed box resolves its left/top offset against the viewport origin (0,0), ignoring the 20px-margined ancestor entirely -- RED-by-design, see header finding and bug doc")
expect(fx.x).to_equal(1)
expect(fx.y).to_equal(2)
```

</details>

#### z-index reorders overlapping positioned boxes

- z-index reorders overlapping positioned boxes
- Render two overlapping absolutely-positioned boxes; the higher z-index box comes FIRST in DOM order
- Assert both commands were found
- Assert the higher z-index box paints AFTER (on top of) the lower z-index box, even though it comes first in DOM order, proving z-index -- not DOM order -- controls paint order


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("z-index reorders overlapping positioned boxes")
step("Render two overlapping absolutely-positioned boxes; the higher z-index box comes FIRST in DOM order")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#z_hi{position:absolute;left:0px;top:0px;width:20px;height:20px;" +
    "background-color:#ff0000;z-index:5}" +
    "#z_lo{position:absolute;left:5px;top:5px;width:20px;height:20px;" +
    "background-color:#00ff00;z-index:1}" +
    "</style></head><body><div id='z_hi'></div><div id='z_lo'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val hi_index = _draw_ir_command_index_by_id(composition.batches[0].commands, "z_hi")
val lo_index = _draw_ir_command_index_by_id(composition.batches[0].commands, "z_lo")

step("Assert both commands were found")
assert_true(hi_index >= 0)
assert_true(lo_index >= 0)

step("Assert the higher z-index box paints AFTER (on top of) the lower z-index box, even though it comes first in DOM order, proving z-index -- not DOM order -- controls paint order")
assert_true(hi_index > lo_index)
```

</details>

#### clear moves a block below preceding content

- clear moves a block below preceding content
- Render a float followed by a plain block with no clear, then the same shape with clear:left
- Assert the un-cleared block's own top is unaffected by the preceding float (block-level boxes ignore floats for their own flow position in real CSS) -- RED-by-design, float takes nothing out of flow yet, see header finding and bug doc
   - Expected: nc.y equals `0`
- Assert the cleared block moves below the float's bottom edge specifically because of clear, not because it would land there anyway
   - Expected: cl.y equals `fl_a.height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clear moves a block below preceding content")
step("Render a float followed by a plain block with no clear, then the same shape with clear:left")
val html_no_clear = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#fl_a{float:left;width:10px;height:20px;background-color:#3b82f6}" +
    "#nc{display:block;width:20px;height:5px;background-color:#eab308}" +
    "</style></head><body><div id='fl_a'></div><div id='nc'></div></body></html>"
)
val html_clear = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#fl_b{float:left;width:10px;height:20px;background-color:#3b82f6}" +
    "#cl{clear:left;display:block;width:20px;height:5px;background-color:#22c55e}" +
    "</style></head><body><div id='fl_b'></div><div id='cl'></div></body></html>"
)
val composition_no_clear = simple_web_layout_render_html_draw_ir(html_no_clear, 64, 64)
val composition_clear = simple_web_layout_render_html_draw_ir(html_clear, 64, 64)
val fl_a = _draw_ir_command_by_id(composition_no_clear.batches[0].commands, "fl_a")
val nc = _draw_ir_command_by_id(composition_no_clear.batches[0].commands, "nc")
val cl = _draw_ir_command_by_id(composition_clear.batches[0].commands, "cl")

step("Assert the un-cleared block's own top is unaffected by the preceding float (block-level boxes ignore floats for their own flow position in real CSS) -- RED-by-design, float takes nothing out of flow yet, see header finding and bug doc")
expect(nc.y).to_equal(0)

step("Assert the cleared block moves below the float's bottom edge specifically because of clear, not because it would land there anyway")
expect(cl.y).to_equal(fl_a.height)
```

</details>

#### float: left takes a box out of flow with text wrap

- float: left takes a box out of flow with text wrap
- Render a float followed by a paragraph, expecting the paragraph's text to wrap beside the float rather than start below it
- Assert the text run starts beside the float (past its width) at the top of the flow, not below it -- RED-by-design, see doc/08_tracking/bug/browser_engine_css_float_layout_unimplemented_2026-07-20.md
   - Expected: text_command.x equals `10`
   - Expected: text_command.y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float: left takes a box out of flow with text wrap")
step("Render a float followed by a paragraph, expecting the paragraph's text to wrap beside the float rather than start below it")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#fl{float:left;width:10px;height:20px;background-color:#3b82f6}" +
    "#p{display:block;width:40px}" +
    "</style></head><body><div id='fl'></div>" +
    "<p id='p'>hello world</p></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val text_command = _draw_ir_first_text_command(composition.batches[0].commands)

step("Assert the text run starts beside the float (past its width) at the top of the flow, not below it -- RED-by-design, see doc/08_tracking/bug/browser_engine_css_float_layout_unimplemented_2026-07-20.md")
expect(text_command.x).to_equal(10)
expect(text_command.y).to_equal(0)
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

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.7)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e814cae6c4be982cbfb1d35c0f853a88e32036fe424179711543d283fb829ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e814cae6c4be982cbfb1d35c0f853a88e32036fe424179711543d283fb829ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e814cae6c4be982cbfb1d35c0f853a88e32036fe424179711543d283fb829ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_positioning_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_positioning_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_positioning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_positioning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_positioning_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/web_css/web_css_positioning_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_positioning_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'position: relative offsets paint without moving siblings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_positioning_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'position: absolute anchors to the nearest positioned ancestor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_positioning_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'position: fixed anchors to the viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
