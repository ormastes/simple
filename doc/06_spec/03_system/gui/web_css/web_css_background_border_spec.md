# Web CSS Background/Border System Test

> A reader wants to know whether the headless web/HTML-CSS renderer paints the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web CSS Background/Border System Test

A reader wants to know whether the headless web/HTML-CSS renderer paints the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.5) |
| Source | `test/03_system/gui/web_css/web_css_background_border_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the headless web/HTML-CSS renderer paints the
CSS visual-effects layer correctly: background-color filling exactly the
padding box (not spilling into the margin), independently authored per-side
border widths and colors, border-radius rounding corners, box-shadow painting
outside the border box, outline painting outside the box without disturbing
layout, and background-position/-size placing an image region.

## Scope and Preconditions

Most assertions read computed geometry and `computed_style` key/value props
straight off `DrawIrCommand` from
`simple_web_layout_render_html_draw_ir(html, width, height)` (DrawIR-tree
oracle, plan §3.6). Two assertions (border-radius corner rounding, box-shadow
painting outside the border box) need an actual rasterized pixel, so they use
the CPU presenter readback
`simple_web_layout_render_html_pixels(html, width, height, "cpu")` instead, as
explicitly permitted by the plan for this unit.

## Primary Workflow

Render small fixed HTML/CSS fixtures at a fixed viewport, look up the command
for a named element by `component_id` (or a specific pixel by index for the
two pixel-oracle cases), and assert exact computed values.

## Evidence and Provenance

DrawIR-tree oracle + CPU presenter pixel oracle per plan §3.6; source:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects.spl`.

## Scenarios

### Web CSS background and border effects

#### background-color fills exactly the padding box

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Background and border effects" (expected show, folded, detail, or skip)


- background-color fills exactly the padding box
- Render a padded, margined block with a solid background-color
- Assert the box is offset by its own margin only
   - Expected: a.x equals `5`
   - Expected: a.y equals `6`
- Assert the painted box grew by padding on both axes (border 0, so this is exactly the padding box)
   - Expected: a.width equals `28`
   - Expected: a.height equals `18`
- Assert the content box kept the authored content width/height, proving the background covers padding beyond content
   - Expected: a.content_rect.width equals `20`
   - Expected: a.content_rect.height equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("background-color fills exactly the padding box")
step("Render a padded, margined block with a solid background-color")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#a{display:block;width:20px;height:10px;padding:4px;" +
    "margin:6px 0 0 5px;background-color:#3b82f6}" +
    "</style></head><body><div id='a'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val a = _draw_ir_command_by_id(composition.batches[0].commands, "a")

step("Assert the box is offset by its own margin only")
expect(a.x).to_equal(5)
expect(a.y).to_equal(6)

step("Assert the painted box grew by padding on both axes (border 0, so this is exactly the padding box)")
expect(a.width).to_equal(28)
expect(a.height).to_equal(18)

step("Assert the content box kept the authored content width/height, proving the background covers padding beyond content")
expect(a.content_rect.width).to_equal(20)
expect(a.content_rect.height).to_equal(10)
```

</details>

#### per-side border widths and colors paint four distinct edges

- per-side border widths and colors paint four distinct edges
- Render a block with four different per-side border widths and colors
- Assert the painted box grew asymmetrically by each side's own width
   - Expected: b.width equals `20 + 5 + 3`
   - Expected: b.height equals `10 + 2 + 4`
- Assert each side's authored width survived independently
   - Expected: _style_prop(b, "border-top-width") equals `2`
   - Expected: _style_prop(b, "border-right-width") equals `3`
   - Expected: _style_prop(b, "border-bottom-width") equals `4`
   - Expected: _style_prop(b, "border-left-width") equals `5`
- Assert the four side colors are pairwise distinct, proving they paint four different edges rather than one shared border color


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("per-side border widths and colors paint four distinct edges")
step("Render a block with four different per-side border widths and colors")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#b{display:block;width:20px;height:10px;" +
    "border-top:2px solid #ff0000;border-right:3px solid #00ff00;" +
    "border-bottom:4px solid #0000ff;border-left:5px solid #ffff00;" +
    "background-color:#111827}" +
    "</style></head><body><div id='b'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val b = _draw_ir_command_by_id(composition.batches[0].commands, "b")

step("Assert the painted box grew asymmetrically by each side's own width")
expect(b.width).to_equal(20 + 5 + 3)
expect(b.height).to_equal(10 + 2 + 4)

step("Assert each side's authored width survived independently")
expect(_style_prop(b, "border-top-width")).to_equal("2")
expect(_style_prop(b, "border-right-width")).to_equal("3")
expect(_style_prop(b, "border-bottom-width")).to_equal("4")
expect(_style_prop(b, "border-left-width")).to_equal("5")

step("Assert the four side colors are pairwise distinct, proving they paint four different edges rather than one shared border color")
val top_color = _style_prop(b, "border-top-color")
val right_color = _style_prop(b, "border-right-color")
val bottom_color = _style_prop(b, "border-bottom-color")
val left_color = _style_prop(b, "border-left-color")
assert_true(top_color != right_color)
assert_true(top_color != bottom_color)
assert_true(top_color != left_color)
assert_true(right_color != bottom_color)
assert_true(right_color != left_color)
assert_true(bottom_color != left_color)
```

</details>

#### border-radius rounds corners (pixel oracle: corner pixel outside radius is background)

- border-radius rounds corners (pixel oracle: corner pixel outside radius is background)
- Render a 20x20 black block at the viewport origin with an 8px border-radius over a white body
- Assert the box's square corner pixel, which sits outside the 8px radius arc, is still the white background
   - Expected: pixels[0 * 64 + 0] equals `0xFFFFFFFFu32`
- Assert a pixel well inside the box (near its center) is the box's own black background
   - Expected: pixels[10 * 64 + 10] equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("border-radius rounds corners (pixel oracle: corner pixel outside radius is background)")
step("Render a 20x20 black block at the viewport origin with an 8px border-radius over a white body")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#r{display:block;width:20px;height:20px;border-radius:8px;" +
    "background-color:#000000}" +
    "</style></head><body><div id='r'></div></body></html>"
)
val pixels = simple_web_layout_render_html_pixels(html, 64, 64, "cpu")

step("Assert the box's square corner pixel, which sits outside the 8px radius arc, is still the white background")
expect(pixels[0 * 64 + 0]).to_equal(0xFFFFFFFFu32)

step("Assert a pixel well inside the box (near its center) is the box's own black background")
expect(pixels[10 * 64 + 10]).to_equal(0xFF000000u32)
```

</details>

#### box-shadow paints outside the border box

- box-shadow paints outside the border box
- Render a small blue block, offset from the viewport edge by body padding, with a hard-edged red box-shadow
- Assert a pixel inside the box's own border box is the box's own blue background
   - Expected: pixels[22 * 64 + 22] equals `0xFF0000FFu32`
- Assert a pixel inside the shadow region but outside the border box is the shadow's red color
   - Expected: pixels[32 * 64 + 32] equals `0xFFFF0000u32`
- Assert a pixel outside both the box and the shadow region stayed the unpainted white body background
   - Expected: pixels[20 * 64 + 34] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("box-shadow paints outside the border box")
step("Render a small blue block, offset from the viewport edge by body padding, with a hard-edged red box-shadow")
val html = (
    "<html><head><style>" +
    "html{margin:0;padding:0}" +
    "body{margin:0;padding:20px;background:#ffffff}" +
    "#s{display:block;width:10px;height:10px;" +
    "background-color:#0000ff;box-shadow:6px 6px 0px #ff0000}" +
    "</style></head><body><div id='s'></div></body></html>"
)
val pixels = simple_web_layout_render_html_pixels(html, 64, 64, "cpu")

step("Assert a pixel inside the box's own border box is the box's own blue background")
expect(pixels[22 * 64 + 22]).to_equal(0xFF0000FFu32)

step("Assert a pixel inside the shadow region but outside the border box is the shadow's red color")
expect(pixels[32 * 64 + 32]).to_equal(0xFFFF0000u32)

step("Assert a pixel outside both the box and the shadow region stayed the unpainted white body background")
expect(pixels[20 * 64 + 34]).to_equal(0xFFFFFFFFu32)
```

</details>

#### outline paints outside without affecting layout

- outline paints outside without affecting layout
- Render two stacked siblings; the first has a thick offset outline
- Assert the outlined box's own border-box size is unaffected by the outline
   - Expected: o1.width equals `20`
   - Expected: o1.height equals `10`
- Assert the following sibling sits immediately after o1 with no gap, proving outline never participates in layout
   - Expected: o2.y equals `o1.y + o1.height`
- Assert the outline's own width/offset survived for the paint layer
   - Expected: _style_prop(o1, "outline-width") equals `3`
   - Expected: _style_prop(o1, "outline-offset") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outline paints outside without affecting layout")
step("Render two stacked siblings; the first has a thick offset outline")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#o1{display:block;width:20px;height:10px;" +
    "outline:3px solid #000000;outline-offset:2px;" +
    "background-color:#3b82f6}" +
    "#o2{display:block;width:20px;height:10px;" +
    "background-color:#22c55e}" +
    "</style></head><body><div id='o1'></div><div id='o2'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val o1 = _draw_ir_command_by_id(composition.batches[0].commands, "o1")
val o2 = _draw_ir_command_by_id(composition.batches[0].commands, "o2")

step("Assert the outlined box's own border-box size is unaffected by the outline")
expect(o1.width).to_equal(20)
expect(o1.height).to_equal(10)

step("Assert the following sibling sits immediately after o1 with no gap, proving outline never participates in layout")
expect(o2.y).to_equal(o1.y + o1.height)

step("Assert the outline's own width/offset survived for the paint layer")
expect(_style_prop(o1, "outline-width")).to_equal("3")
expect(_style_prop(o1, "outline-offset")).to_equal("2")
```

</details>

#### background-position and -size place an image region

- background-position and -size place an image region
- Render a block with a url() background image, an explicit size, and an offset position
- Assert the placed image region used the explicit background-size, not the block's own box size
   - Expected: _style_prop(image_command, "background-tile-width") equals `8`
   - Expected: _style_prop(image_command, "background-tile-height") equals `8`
- Assert the placed image region was offset from the box origin by the explicit background-position
   - Expected: _style_prop(image_command, "background-tile-x") equals `2`
   - Expected: _style_prop(image_command, "background-tile-y") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("background-position and -size place an image region")
step("Render a block with a url() background image, an explicit size, and an offset position")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#img{display:block;width:20px;height:20px;" +
    "background-image:url('tex.png');background-repeat:no-repeat;" +
    "background-size:8px 8px;background-position:2px 3px}" +
    "</style></head><body><div id='img'></div></body></html>"
)
var pixels: [u32] = []
var idx = 0
while idx < 8 * 8:
    pixels.push(0xFFFF00FFu32)
    idx = idx + 1
val images = [SimpleOsHostGpuImageResource(
    image_uri: "tex.png", width: 8, height: 8, pixels: pixels,
    pixel_checksum: 0
)]
val composition = simple_web_layout_render_html_draw_ir_with_images(
    html, 64, 64, images
)
val image_command = _draw_ir_command_by_id(
    composition.batches[0].commands, "img_background_image"
)

step("Assert the placed image region used the explicit background-size, not the block's own box size")
expect(_style_prop(image_command, "background-tile-width")).to_equal("8")
expect(_style_prop(image_command, "background-tile-height")).to_equal("8")

step("Assert the placed image region was offset from the box origin by the explicit background-position")
expect(_style_prop(image_command, "background-tile-x")).to_equal("2")
expect(_style_prop(image_command, "background-tile-y")).to_equal("3")
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

- **Plan:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md (unit U3.5)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-CSS-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7f914b685b3866c479c0c5be7a2556355f10b3666c6e00d0ea0672388224294d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f914b685b3866c479c0c5be7a2556355f10b3666c6e00d0ea0672388224294d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f914b685b3866c479c0c5be7a2556355f10b3666c6e00d0ea0672388224294d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/web_css/web_css_background_border_spec.spl
mirror: doc/06_spec/03_system/gui/web_css/web_css_background_border_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/web_css/web_css_background_border_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_css/web_css_background_border_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_css/web_css_background_border_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/web_css/web_css_background_border_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/web_css/web_css_background_border_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'background-color fills exactly the padding box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_background_border_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'per-side border widths and colors paint four distinct edges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_css/web_css_background_border_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'border-radius rounds corners (pixel oracle: corner pixel outside radius is background)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
