# simple_web_html_layout_renderer_coverage_spec

> Layout-phase coverage spec for the simple_web_html_layout_renderer family.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_web_html_layout_renderer_coverage_spec

Layout-phase coverage spec for the simple_web_html_layout_renderer family.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Layout-phase coverage spec for the simple_web_html_layout_renderer family.

The web-rendering pipeline is tokenize -> dom -> style -> layout -> paint ->
tiles -> present. The LAYOUT phase modules had never been measured at all; this
spec drives their PUBLIC entry points so `SIMPLE_COVERAGE=1` reports a real
number for each file instead of an unmeasured blank.

Every example drives a public `simple_web_layout_*` entry point -- no private
internals are imported. The fixtures are picked from the measured uncovered-line
map rather than guessed, and every expectation was read off a throwaway probe
before being asserted (that is how `animation_end_ms` on an `infinite`
animation turned out to be -2, not the -1 a guess would have written).

Framebuffers are deliberately tiny. The paint primitives under measurement
(`fb_background_radial_stack_clip`, `fb_soft_box_shadow`,
`fb_rounded_rect_opacity_clip`) are per-pixel loops, so raster cost is the
budget here: one feature per small fixture keeps the whole spec affordable
while still entering each primitive. A single 96x192 tile-parity pair pushed an
earlier revision of this spec past 25 minutes.

@tag: rendering, simple-web, layout, coverage
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles.spl
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl

## Scenarios

### layout phase: draw-ir composition lane

#### composes a non-empty batch list for a full-feature document

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- composes a non-empty batch list for a full-feature document


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composes a non-empty batch list for a full-feature document")
val res = simple_web_layout_render_html_draw_ir_result(_layout_doc(), 64, 64)
expect(res.composition.batches.len() > 0).to_be(true)
```

</details>

#### composes the selector document

- composes the selector document


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composes the selector document")
val res = simple_web_layout_render_html_draw_ir_result(_selector_doc(), 64, 64)
expect(res.composition.batches.len() > 0).to_be(true)
```

</details>

#### composes the animation document at a mid-animation time

- composes the animation document at a mid-animation time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composes the animation document at a mid-animation time")
val res = simple_web_layout_render_html_draw_ir_result_at_time(_anim_doc(), 48, 32, 700)
expect(res.composition.batches.len() > 0).to_be(true)
```

</details>

#### reports that an animation touching a layout property needs relayout

- reports that an animation touching a layout property needs relayout


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports that an animation touching a layout property needs relayout")
# measured: `slide` animates `left`, a layout property, so the frame
# cannot be replayed from the retained display list alone. A fixture
# animating only `opacity` is the false case.
val res = simple_web_layout_render_html_draw_ir_result_at_time(_anim_doc(), 48, 32, 700)
expect(simple_web_layout_animation_needs_layout(res)).to_be(true)
```

</details>

#### composes checkable-input (radio) draw-ir commands

- composes checkable-input (radio) draw-ir commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composes checkable-input (radio) draw-ir commands")
# The only path that reaches _html_draw_ir_checkable_commands
# (0-covered before this example) -- a real batch means the
# frame/border/checked-dot sub-commands actually got pushed.
val res = simple_web_layout_render_html_draw_ir_result(_radio_doc(), 32, 40)
expect(res.composition.batches.len() > 0).to_be(true)
```

</details>

### layout phase: paint primitives

<details>
<summary>Advanced: blends a soft box shadow across many intermediate values</summary>

#### blends a soft box shadow across many intermediate values _(slow)_

- blends a soft box shadow across many intermediate values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blends a soft box shadow across many intermediate values")
# The load-bearing one: 78 distinct values over a 32x24 frame can only
# come from `fb_soft_box_shadow` actually running its falloff. A solid
# fill would leave 2 or 3.
val px = simple_web_layout_render_html_software_pixels(_shadow_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px) > 10).to_be(true)
```

</details>


</details>

#### rasters a linear-gradient stack

- rasters a linear-gradient stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters a linear-gradient stack")
val px = simple_web_layout_render_html_software_pixels(_grad_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(3)
```

</details>

#### rasters rounded corners under fractional opacity

- rasters rounded corners under fractional opacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters rounded corners under fractional opacity")
val px = simple_web_layout_render_html_software_pixels(_round_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(3)
```

</details>

#### enters the radial-gradient painter

- enters the radial-gradient painter


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters the radial-gradient painter")
# Measured: this fixture currently resolves to 2 distinct values, i.e.
# the radial stack flattens to a solid fill at this box size rather
# than painting a visible ramp. The example is kept because it does
# enter `fb_background_radial_stack_clip`, and the pinned count will
# move the day that flattening changes -- it is NOT evidence that a
# radial gradient renders correctly.
val px = simple_web_layout_render_html_software_pixels(_rad_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(2)
```

</details>

#### rasters a text run carrying decoded numeric entities

- rasters a text run carrying decoded numeric entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters a text run carrying decoded numeric entities")
# Same caveat: 2 distinct values means no glyph ink landed in this
# frame. Pinned as measured, not asserted as a rendering guarantee.
val px = simple_web_layout_render_html_software_pixels(_text_doc(), 40, 24, 3600000)
expect(px.len()).to_be(960)
expect(_distinct(px)).to_be(2)
```

</details>

#### enters fb_outline_clip via a box with a CSS outline set

- enters fb_outline_clip via a box with a CSS outline set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters fb_outline_clip via a box with a CSS outline set")
# Measured: background blue, outline red, page-bg white -> 3 distinct
# values. Without the outline color present this would read 2, so the
# count itself proves the outline primitive actually painted pixels.
val px = simple_web_layout_render_html_software_pixels(_outline_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(3)
```

</details>

#### enters the widget-panel/widget-button fb_rect fallback fills

- enters the widget-panel/widget-button fb_rect fallback fills


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters the widget-panel/widget-button fb_rect fallback fills")
# Measured: page-bg white, panel-gray 245/245/245, focus-line blue,
# button-gray 203/213/225 -> 3 distinct values over a 32x24 frame
# (the 1px focus line and button fill share one of the three bins at
# this size). Without the class-driven fallback paths this reads 1.
val px = simple_web_layout_render_html_software_pixels(_widget_panel_button_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(3)
```

</details>

#### enters fb_input_accent_control_clip's rounded-dot branches via radio inputs

- enters fb_input_accent_control_clip's rounded-dot branches via radio inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters fb_input_accent_control_clip's rounded-dot branches via radio inputs")
# Measured: page-bg white, accent blue (ring + checked dot), inner
# white-ish fill -> 3 distinct values over a 32x40 frame. This is the
# only path that reaches fb_rounded_rect_opacity_clip from this file.
val px = simple_web_layout_render_html_software_pixels(_radio_doc(), 32, 40, 3600000)
expect(px.len()).to_be(1280)
expect(_distinct(px)).to_be(3)
```

</details>

#### enters fb_background_radial_stack_clip via a legacy-widget-chrome radial body background

- enters fb_background_radial_stack_clip via a legacy-widget-chrome radial body background


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters fb_background_radial_stack_clip via a legacy-widget-chrome radial body background")
# Measured: 14 distinct ARGB values over a 32x24 frame -- only a real
# radial-ramp raster produces that many bins; a flattened/solid fill
# (as seen in the non-widget-chrome `_rad_doc` fixture above) would
# read 2.
val px = simple_web_layout_render_html_software_pixels(_widget_radial_body_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(14)
```

</details>

#### enters fb_widget_image_placeholder_clip via a non-widget-mode widget-image img

- enters fb_widget_image_placeholder_clip via a non-widget-mode widget-image img


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters fb_widget_image_placeholder_clip via a non-widget-mode widget-image img")
# Measured: page-bg white, placeholder fill, placeholder border -> 3
# distinct values over a 32x24 frame. Without the placeholder path
# actually running this reads 1 (the bare page background).
val px = simple_web_layout_render_html_software_pixels(_widget_image_doc(), 32, 24, 3600000)
expect(px.len()).to_be(768)
expect(_distinct(px)).to_be(3)
```

</details>

### layout phase: software raster lane

#### rasters the paint lane end to end

- rasters the paint lane end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters the paint lane end to end")
expect(simple_web_layout_render_html_software_pixels(_lane_doc(), 48, 48, 3600000).len()).to_be(2304)
```

</details>

#### rasters at a scroll offset

- rasters at a scroll offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters at a scroll offset")
expect(simple_web_layout_render_html_software_pixels_at_scroll(_lane_doc(), 48, 48, 20, 3600000).len()).to_be(2304)
```

</details>

#### returns an empty buffer for a zero-width viewport

- returns an empty buffer for a zero-width viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty buffer for a zero-width viewport")
expect(simple_web_layout_render_html_software_pixels_at_scroll(_lane_doc(), 0, 48, 0, 3600000).len()).to_be(0)
```

</details>

#### rasters the full-feature layout document

- rasters the full-feature layout document


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters the full-feature layout document")
expect(simple_web_layout_render_html_software_pixels(_layout_doc(), 32, 32, 3600000).len()).to_be(1024)
```

</details>

#### rasters through the traced lane

- rasters through the traced lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters through the traced lane")
expect(simple_web_layout_render_html_software_pixels_traced(_box_doc(), 32, 24).len()).to_be(768)
```

</details>

### layout phase: tile lane parity

#### produces identical pixels through the tiled and classic lanes

- produces identical pixels through the tiled and classic lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces identical pixels through the tiled and classic lanes")
val tiled = simple_web_layout_render_html_software_pixels_tile_lane(
    _lane_doc(), 32, 32, 0, 32, true)
val classic = simple_web_layout_render_html_software_pixels_tile_lane(
    _lane_doc(), 32, 32, 0, 32, false)
expect(tiled.len()).to_be(classic.len())
expect(tiled).to_be(classic)
```

</details>

### layout phase: gpu display-list frame

#### builds a gpu paint frame carrying solid-fill ops

- builds a gpu paint frame carrying solid-fill ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a gpu paint frame carrying solid-fill ops")
val frame = simple_web_layout_render_html_gpu_frame(_lane_doc(), 48, 48, 3600000)
expect(frame.width).to_be(48)
expect(frame.height).to_be(48)
expect(frame.fill_ops.len() > 0).to_be(true)
```

</details>

#### counts gpu paint state visits

- counts gpu paint state visits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts gpu paint state visits")
expect(simple_web_layout_debug_gpu_paint_state_visits(_lane_doc(), 64) >= 0).to_be(true)
```

</details>

### layout phase: css animation scheduling

#### reconciles animation instances and schedules their next tick

- reconciles animation instances and schedules their next tick


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconciles animation instances and schedules their next tick")
val insts = simple_web_layout_reconcile_animation_instances(_anim_doc(), 64, 0, 0, false, [])
expect(insts.len() > 0).to_be(true)
expect(simple_web_layout_animation_instances_next_ms(insts, 0) >= 0).to_be(true)
```

</details>

#### reports no next tick for an empty instance list

- reports no next tick for an empty instance list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no next tick for an empty instance list")
expect(simple_web_layout_animation_instances_next_ms([], 0)).to_be(-1)
```

</details>

#### reports the -2 never-ends sentinel for an infinite animation

- reports the -2 never-ends sentinel for an infinite animation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the -2 never-ends sentinel for an infinite animation")
# measured, not guessed: -1 means "no @keyframes at all", -2 means
# "declared, but never reaches an end time".
expect(simple_web_layout_animation_end_ms(_anim_doc(), 64)).to_be(-2)
```

</details>

#### reports -1 end time for a document with no @keyframes

- reports -1 end time for a document with no @keyframes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports -1 end time for a document with no @keyframes")
expect(simple_web_layout_animation_end_ms(_layout_doc(), 64)).to_be(-1)
```

</details>

### layout phase: hit testing and debug read-back

#### hit tests a point inside the document

- hit tests a point inside the document


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit tests a point inside the document")
expect(simple_web_layout_hit_test_target_at_time(_layout_doc(), 64, 64, 4, 4, 0).len() >= 0).to_be(true)
```

</details>

#### reads laid-out geometry back by node id

- reads laid-out geometry back by node id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads laid-out geometry back by node id")
expect(simple_web_layout_debug_layout_by_id(_box_doc(), 64, 48, "b1", "w")).to_be("20")
expect(simple_web_layout_debug_layout_by_id(_box_doc(), 64, 48, "b1", "h")).to_be("10")
expect(simple_web_layout_debug_layout_by_id(_box_doc(), 64, 48, "b1", "x")).to_be("0")
```

</details>

#### reads a resolved style field back by node id

- reads a resolved style field back by node id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a resolved style field back by node id")
# `color` is not one of the fields this debug entry answers; `display`
# is, and a bare <div> resolves to block.
expect(simple_web_layout_debug_style_by_id(_box_doc(), "b1", "display")).to_be("block")
```

</details>

#### reads an attribute back by node id

- reads an attribute back by node id


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads an attribute back by node id")
expect(simple_web_layout_debug_attr_by_id(_selector_doc(), "c1", "data-role")).to_be("card")
```

</details>

#### counts capped nodes and capped input bytes

- counts capped nodes and capped input bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts capped nodes and capped input bytes")
expect(simple_web_layout_debug_capped_node_count(_layout_doc(), 4096) > 0).to_be(true)
expect(simple_web_layout_debug_capped_input_node_count(_layout_doc(), 65536) > 0).to_be(true)
```

</details>

#### dumps parsed nodes

- dumps parsed nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dumps parsed nodes")
expect(simple_web_layout_debug_dump_nodes(_layout_doc()).len() > 0).to_be(true)
```

</details>

#### classifies legacy widget chrome usage

- classifies legacy widget chrome usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies legacy widget chrome usage")
expect(simple_web_layout_uses_legacy_widget_chrome(_layout_doc())).to_be(false)
```

</details>

### layout phase: flex-wrap row measurement and placement

#### wraps a second 20px item onto a new line inside a 30px container

- wraps a second 20px item onto a new line inside a 30px container


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps a second 20px item onto a new line inside a 30px container")
# 20+20=40 > 30, so the row-wrap measurement pass must close line 1
# after the first item and place the second on line 2 -- entering
# the wrap-measurement/placement loops in layout_with_style that a
# nowrap flex row never reaches.
val y1 = simple_web_layout_debug_layout_by_id(_flex_wrap_doc(), 30, 60, "i1", "y")
val y2 = simple_web_layout_debug_layout_by_id(_flex_wrap_doc(), 30, 60, "i2", "y")
expect(y1).to_be("0")
expect(y2 != y1).to_be(true)
```

</details>

#### keeps both items at the same x when each starts its own line

- keeps both items at the same x when each starts its own line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps both items at the same x when each starts its own line")
val x1 = simple_web_layout_debug_layout_by_id(_flex_wrap_doc(), 30, 60, "i1", "x")
val x2 = simple_web_layout_debug_layout_by_id(_flex_wrap_doc(), 30, 60, "i2", "x")
expect(x1).to_be("0")
expect(x2).to_be("0")
```

</details>

### layout phase: column-direction flex

#### stacks column-flex children vertically, second below first

- stacks column-flex children vertically, second below first


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stacks column-flex children vertically, second below first")
val y1 = simple_web_layout_debug_layout_by_id(_flex_col_doc(), 64, 48, "c1", "y")
val h1 = simple_web_layout_debug_layout_by_id(_flex_col_doc(), 64, 48, "c1", "h")
val y2 = simple_web_layout_debug_layout_by_id(_flex_col_doc(), 64, 48, "c2", "y")
expect(y1).to_be("0")
expect(h1).to_be("6")
expect(y2).to_be("6")
```

</details>

### layout phase: explicit-width table column offsets

#### computes a wider second-column offset from the explicit cell widths

- computes a wider second-column offset from the explicit cell widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes a wider second-column offset from the explicit cell widths")
# table width:60px, border-spacing:2px, cols 20px/8px: only the
# table_layout=='auto' + explicit-width path calls
# explicit_auto_table_column_offsets, and only its authored-spacing
# branch grows columns to fill the leftover 60-20-8-3*2=26px.
val x1 = simple_web_layout_debug_layout_by_id(_table_offsets_doc(), 64, 32, "c1", "x")
val x2 = simple_web_layout_debug_layout_by_id(_table_offsets_doc(), 64, 32, "c2", "x")
expect(x1 != "").to_be(true)
expect(x2 != x1).to_be(true)
```

</details>

### layout phase: collapsed table borders (bounded fast path)

#### resolves a single-row two-cell collapsed table without erroring

- resolves a single-row two-cell collapsed table without erroring


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a single-row two-cell collapsed table without erroring")
# Single row + exactly two direct table-cell children + no
# colspan/rowspan is the only shape `simple_web_resolve_collapsed_
# table_borders` treats as 'bounded' and zeroes the shared edge for;
# `_layout_doc`'s two-row table never takes this branch. Measured:
# `simple_web_layout_debug_layout_by_id` calls `layout()` directly and
# never calls `simple_web_resolve_collapsed_table_borders` at all, so
# this must go through the full render pipeline entry point instead.
val res = simple_web_layout_render_html_draw_ir_result(_table_collapse_doc(), 64, 32)
expect(res.composition.batches.len() > 0).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 1 |
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

- Canonical SPipe generation for source `b6affa009e2e5e5aa27d706e23c89aac586906984652159e1e4a085796e38671`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6affa009e2e5e5aa27d706e23c89aac586906984652159e1e4a085796e38671`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6affa009e2e5e5aa27d706e23c89aac586906984652159e1e4a085796e38671`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.spl:281:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composes a non-empty batch list for a full-feature document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.spl:287:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composes the selector document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_coverage_spec.spl:293:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composes the animation document at a mid-animation time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
