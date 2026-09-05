# Simple Web Html Layout Renderer Paint Layout Coverage Closure Specification

> Tests covering paint entry point: node/style pipeline via HTML (paint closure), has_visible_overflow_clip, _html_draw_ir_non_negative, _html_draw_ir_shadow_layer_count, _html_draw_ir_clamp_i64, _html_draw_ir_abs_i32, _html_draw_ir_saturated_i32, _html_draw_ir_background_offset, _html_draw_ir_background_edge, _tile_abs_i32, _tile_style_hash, input_text_prefix, _input_text_source_boundaries, input_caret_color, input_selection_color, _text_decoration_line_text, paint_tiled: widget_mode early-return branch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Html Layout Renderer Paint Layout Coverage Closure Specification

## Scenarios

### paint entry point: node/style pipeline via HTML (paint closure)

#### paints scrollbar-track pixels distinct from the box's own background and from the page outside it

- paints scrollbar-track pixels distinct from the box's own background and from the page outside it


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints scrollbar-track pixels distinct from the box's own background and from the page outside it")
val px = simple_web_layout_render_html_software_pixels(_pl_scrollbar_doc(), 24, 24, 3600000)
# col4: the div's own #e2e8f0 background, left of the scrollbar.
# col10: inside the 15px-wide scrollbar track/thumb region
# (x = box_right(20) - border_r(0) - 15 = 5 .. 19).
# col22: outside the 20px-wide box, the page's white background.
assert_true(px[4] != px[10])
assert_true(px[10] != px[22])
assert_equal(px[22], 4294967295u32)
```

</details>

#### z-sorts unsorted positive-z-index absolute boxes so the highest z-index paints on top

- z-sorts unsorted positive-z-index absolute boxes so the highest z-index paints on top


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("z-sorts unsorted positive-z-index absolute boxes so the highest z-index paints on top")
val px = simple_web_layout_render_html_software_pixels(_pl_zsort_doc(), 12, 12, 3600000)
# z1 (z-index:30, #ff0000) is declared second in DOM order but has the
# highest z-index, so it must be the topmost (last-painted) pixel at
# the fully-overlapping origin -- only reachable if the unsorted-input
# branch actually calls _sort_positive_z_indices.
assert_equal(px[0], 4294901760u32)
```

</details>

#### reverses RTL #text glyph order relative to the same LTR text

- reverses RTL #text glyph order relative to the same LTR text


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses RTL #text glyph order relative to the same LTR text")
val res_rtl = simple_web_layout_render_html_draw_ir_result(_pl_rtl_doc(), 64, 24)
val res_ltr = simple_web_layout_render_html_draw_ir_result(_pl_ltr_doc(), 64, 24)
var rtl_text = ""
for b in res_rtl.composition.batches:
    for c in b.commands:
        if c.kind == "text" and rtl_text == "":
            rtl_text = c.text_value
var ltr_text = ""
for b in res_ltr.composition.batches:
    for c in b.commands:
        if c.kind == "text" and ltr_text == "":
            ltr_text = c.text_value
assert_equal(ltr_text, "abc")
assert_equal(rtl_text, "cba")
```

</details>

#### applies text-transform:uppercase before the Draw IR text command is built

- applies text-transform:uppercase before the Draw IR text command is built


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies text-transform:uppercase before the Draw IR text command is built")
val res = simple_web_layout_render_html_draw_ir_result(_pl_upper_doc(), 64, 24)
var upper_text = ""
for b in res.composition.batches:
    for c in b.commands:
        if c.kind == "text" and upper_text == "":
            upper_text = c.text_value
assert_equal(upper_text, "ABC")
```

</details>

#### ellipsizes an overflowing text-overflow:ellipsis run in the Draw IR text command

- ellipsizes an overflowing text-overflow:ellipsis run in the Draw IR text command


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ellipsizes an overflowing text-overflow:ellipsis run in the Draw IR text command")
val res = simple_web_layout_render_html_draw_ir_result(_pl_ellipsis_doc(), 64, 24)
var ellipsis_text = ""
for b in res.composition.batches:
    for c in b.commands:
        if c.kind == "text" and ellipsis_text == "":
            ellipsis_text = c.text_value
assert_equal(ellipsis_text, "...")
```

</details>

#### passes the full text through unmodified when text-overflow:ellipsis is not set

- passes the full text through unmodified when text-overflow:ellipsis is not set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the full text through unmodified when text-overflow:ellipsis is not set")
val res = simple_web_layout_render_html_draw_ir_result(_pl_noellipsis_doc(), 64, 24)
var full_text = ""
for b in res.composition.batches:
    for c in b.commands:
        if c.kind == "text" and full_text == "":
            full_text = c.text_value
assert_equal(full_text, "abcdefghijklmnop")
```

</details>

#### computes the background-image layer set and falls back cleanly with no image resources supplied

- computes the background-image layer set and falls back cleanly with no image resources supplied


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes the background-image layer set and falls back cleanly with no image resources supplied")
val res = simple_web_layout_render_html_draw_ir_result(_pl_bgimg_doc(), 24, 24)
var command_count = 0
for b in res.composition.batches:
    for c in b.commands:
        command_count = command_count + 1
# canvas + html + body + div, and NO extra background-image command --
# proving the backgrounds_ready=false fallback path ran to completion
# (rather than crashing or silently appending a partial command).
assert_equal(command_count, 4)
```

</details>

#### emits an explicit summary-marker Draw IR command for a <details><summary>

- emits an explicit summary-marker Draw IR command for a <details><summary>


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an explicit summary-marker Draw IR command for a <details><summary>")
val res = simple_web_layout_render_html_draw_ir_result(_pl_details_doc(), 64, 24)
var marker_text = ""
var marker_component = ""
for b in res.composition.batches:
    for c in b.commands:
        if c.kind == "text" and c.component_id.contains("::marker"):
            marker_text = c.text_value
            marker_component = c.component_id
assert_equal(marker_text, "▶")
assert_true(marker_component.contains("summary"))
```

</details>

### has_visible_overflow_clip

#### is false for an empty style list

- is false for an empty style list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false for an empty style list")
assert_false(has_visible_overflow_clip([]))
```

</details>

#### is false when no style clips overflow

- is false when no style clips overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false when no style clips overflow")
val st = renderer_default_style()
assert_false(has_visible_overflow_clip([st, st]))
```

</details>

#### is true when one style in the list clips overflow and is visible

- is true when one style in the list clips overflow and is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is true when one style in the list clips overflow and is visible")
var st_clip = renderer_default_style()
st_clip.overflow_hidden = true
assert_true(has_visible_overflow_clip([renderer_default_style(), st_clip]))
```

</details>

#### ignores a clipping style that is display:none

- ignores a clipping style that is display:none


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores a clipping style that is display:none")
var st_clip = renderer_default_style()
st_clip.overflow_hidden = true
st_clip.display = "none"
assert_false(has_visible_overflow_clip([st_clip]))
```

</details>

### _html_draw_ir_non_negative

#### clamps a negative value to 0

- clamps a negative value to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps a negative value to 0")
assert_equal(_html_draw_ir_non_negative(-5), 0)
```

</details>

#### passes a non-negative value through unchanged

- passes a non-negative value through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a non-negative value through unchanged")
assert_equal(_html_draw_ir_non_negative(7), 7)
assert_equal(_html_draw_ir_non_negative(0), 0)
```

</details>

### _html_draw_ir_shadow_layer_count

#### is 0 for an empty shadow value

- is 0 for an empty shadow value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is 0 for an empty shadow value")
assert_equal(_html_draw_ir_shadow_layer_count(""), 0)
```

</details>

#### counts one layer for a single shadow with no top-level comma

- counts one layer for a single shadow with no top-level comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts one layer for a single shadow with no top-level comma")
assert_equal(_html_draw_ir_shadow_layer_count("2px 2px 4px #000"), 1)
```

</details>

#### counts each top-level-comma-separated shadow as its own layer

- counts each top-level-comma-separated shadow as its own layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts each top-level-comma-separated shadow as its own layer")
assert_equal(
    _html_draw_ir_shadow_layer_count("2px 2px 4px #000, 0 0 2px red"), 2)
```

</details>

### _html_draw_ir_clamp_i64

#### clamps a value below the low bound up to low

- clamps a value below the low bound up to low


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps a value below the low bound up to low")
assert_equal(_html_draw_ir_clamp_i64(-10i64, 0i64, 100i64), 0i64)
```

</details>

#### clamps a value above the high bound down to high

- clamps a value above the high bound down to high


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps a value above the high bound down to high")
assert_equal(_html_draw_ir_clamp_i64(200i64, 0i64, 100i64), 100i64)
```

</details>

#### passes an in-range value through unchanged

- passes an in-range value through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes an in-range value through unchanged")
assert_equal(_html_draw_ir_clamp_i64(50i64, 0i64, 100i64), 50i64)
```

</details>

### _html_draw_ir_abs_i32

#### negates a negative value into i64

- negates a negative value into i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negates a negative value into i64")
assert_equal(_html_draw_ir_abs_i32(-9), 9i64)
```

</details>

#### passes a non-negative value through as i64

- passes a non-negative value through as i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a non-negative value through as i64")
assert_equal(_html_draw_ir_abs_i32(9), 9i64)
assert_equal(_html_draw_ir_abs_i32(0), 0i64)
```

</details>

### _html_draw_ir_saturated_i32

#### saturates a value above i32::MAX down to i32::MAX

- saturates a value above i32::MAX down to i32::MAX


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("saturates a value above i32::MAX down to i32::MAX")
assert_equal(_html_draw_ir_saturated_i32(9999999999i64), 2147483647)
```

</details>

#### saturates a value below i32::MIN up to i32::MIN

- saturates a value below i32::MIN up to i32::MIN


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("saturates a value below i32::MIN up to i32::MIN")
assert_equal(_html_draw_ir_saturated_i32(0i64 - 9999999999i64), 0 - 2147483647 - 1)
```

</details>

#### passes an in-range i64 through as i32

- passes an in-range i64 through as i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes an in-range i64 through as i32")
assert_equal(_html_draw_ir_saturated_i32(42i64), 42)
```

</details>

### _html_draw_ir_background_offset

#### passes a normal (non-sentinel) value through unchanged

- passes a normal (non-sentinel) value through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a normal (non-sentinel) value through unchanged")
assert_equal(_html_draw_ir_background_offset(10, 200), 10)
```

</details>

#### resolves a percentage-sentinel value against free_space

- resolves a percentage-sentinel value against free_space


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a percentage-sentinel value against free_space")
# value <= -1000 encodes a percentage: pct = -1000 - value, offset =
# free_space * pct / 100. -1050 encodes 50%, so with free_space=200
# the offset is 200 * 50 / 100 = 100.
assert_equal(_html_draw_ir_background_offset(0 - 1050, 200), 100)
```

</details>

### _html_draw_ir_background_edge

#### returns the full box span unchanged for border-box

- returns the full box span unchanged for border-box


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the full box span unchanged for border-box")
val edge = _html_draw_ir_background_edge("border-box", 10, 100, 2, 3, 4, 5)
assert_equal(edge.0, 10)
assert_equal(edge.1, 100)
```

</details>

#### insets by border+padding on both sides for content-box

- insets by border+padding on both sides for content-box


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insets by border+padding on both sides for content-box")
val edge = _html_draw_ir_background_edge("content-box", 10, 100, 2, 3, 4, 5)
# start = box_start + border_start + padding_start = 10 + 2 + 4 = 16
assert_equal(edge.0, 16)
# size = box_size - inset_start - border_end - padding_end = 100 - 6 - 3 - 5 = 86
assert_equal(edge.1, 86)
```

</details>

#### insets by border only for the padding-box default case

- insets by border only for the padding-box default case


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insets by border only for the padding-box default case")
val edge = _html_draw_ir_background_edge("padding-box", 10, 100, 2, 3, 4, 5)
assert_equal(edge.0, 12)
assert_equal(edge.1, 95)
```

</details>

#### never returns a negative size (clamped by non_negative)

- never returns a negative size (clamped by non_negative)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never returns a negative size (clamped by non_negative)")
val edge = _html_draw_ir_background_edge("content-box", 0, 5, 10, 10, 10, 10)
assert_equal(edge.1, 0)
```

</details>

### _tile_abs_i32

#### negates a negative value

- negates a negative value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negates a negative value")
assert_equal(_tile_abs_i32(-3), 3)
```

</details>

#### passes a non-negative value through unchanged

- passes a non-negative value through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a non-negative value through unchanged")
assert_equal(_tile_abs_i32(3), 3)
assert_equal(_tile_abs_i32(0), 0)
```

</details>

### _tile_style_hash

#### differs when bg differs and matches when every hashed field matches

- differs when bg differs and matches when every hashed field matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("differs when bg differs and matches when every hashed field matches")
var a = renderer_default_style()
var b = renderer_default_style()
assert_equal(_tile_style_hash(a), _tile_style_hash(b))
a.bg = 0xFF0000FFu32
assert_true(_tile_style_hash(a) != _tile_style_hash(b))
```

</details>

#### differs when opacity_pct differs

- differs when opacity_pct differs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("differs when opacity_pct differs")
var a = renderer_default_style()
var b = renderer_default_style()
a.opacity_pct = 50
assert_true(_tile_style_hash(a) != _tile_style_hash(b))
```

</details>

### input_text_prefix

#### returns the empty text when max_glyphs is 0 or negative

- returns the empty text when max_glyphs is 0 or negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the empty text when max_glyphs is 0 or negative")
assert_equal(input_text_prefix("hello", 0), "")
assert_equal(input_text_prefix("hello", -1), "")
```

</details>

#### returns the value unchanged when it already fits within max_glyphs

- returns the value unchanged when it already fits within max_glyphs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the value unchanged when it already fits within max_glyphs")
assert_equal(input_text_prefix("hi", 5), "hi")
```

</details>

#### truncates to the first max_glyphs codepoints on an ASCII value

- truncates to the first max_glyphs codepoints on an ASCII value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates to the first max_glyphs codepoints on an ASCII value")
assert_equal(input_text_prefix("hello world", 5), "hello")
```

</details>

### _input_text_source_boundaries

#### starts with a leading 0 boundary for an empty value

- starts with a leading 0 boundary for an empty value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with a leading 0 boundary for an empty value")
val b = _input_text_source_boundaries("")
assert_equal(b.len(), 1)
assert_equal(b[0], 0i64)
```

</details>

#### records one boundary per ASCII byte plus the leading 0

- records one boundary per ASCII byte plus the leading 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records one boundary per ASCII byte plus the leading 0")
val b = _input_text_source_boundaries("abc")
assert_equal(b.len(), 4)
assert_equal(b[0], 0i64)
assert_equal(b[1], 1i64)
assert_equal(b[2], 2i64)
assert_equal(b[3], 3i64)
```

</details>

### input_caret_color

#### returns the style's explicit caret_color when set

- returns the style's explicit caret_color when set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the style's explicit caret_color when set")
var st = renderer_default_style()
st.caret_color = 0xFF112233u32
assert_equal(input_caret_color(st), 0xFF112233u32)
```

</details>

#### falls back to fg when caret_color is unset (0)

- falls back to fg when caret_color is unset (0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to fg when caret_color is unset (0)")
var st = renderer_default_style()
st.fg = 0xFF445566u32
st.caret_color = 0u32
assert_equal(input_caret_color(st), 0xFF445566u32)
```

</details>

### input_selection_color

#### composes the fixed selection alpha with the caret color's rgb

- composes the fixed selection alpha with the caret color's rgb


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composes the fixed selection alpha with the caret color's rgb")
var st = renderer_default_style()
st.caret_color = 0xFF112233u32
# INPUT_TEXT_SELECTION_ALPHA (0x66) shifted into the alpha byte, rgb
# taken from caret_color with its own alpha byte masked off.
assert_equal(input_selection_color(st), 0x66112233u32)
```

</details>

### _text_decoration_line_text

#### reports none when no decoration line is set

- reports none when no decoration line is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports none when no decoration line is set")
val st = renderer_default_style()
assert_equal(_text_decoration_line_text(st), "none")
```

</details>

#### reports a single active decoration line

- reports a single active decoration line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a single active decoration line")
var st = renderer_default_style()
st.text_decoration_underline = true
assert_equal(_text_decoration_line_text(st), "underline")
```

</details>

#### joins multiple active decoration lines in canonical order

- joins multiple active decoration lines in canonical order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins multiple active decoration lines in canonical order")
var st = renderer_default_style()
st.text_decoration_underline = true
st.text_decoration_overline = true
st.text_decoration_line_through = true
assert_equal(_text_decoration_line_text(st), "underline overline line-through")
```

</details>

### paint_tiled: widget_mode early-return branch

#### routes a legacy-widget-chrome document straight to the classic painter (tiled == classic)

- routes a legacy-widget-chrome document straight to the classic painter (tiled == classic)


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a legacy-widget-chrome document straight to the classic painter (tiled == classic)")
val html = _pl_tiled_widget_doc()
val tiled = simple_web_layout_render_html_software_pixels_tile_lane(
    html, 32, 24, 0, 24, true)
val classic = simple_web_layout_render_html_software_pixels_tile_lane(
    html, 32, 24, 0, 24, false)
# widget_mode short-circuits paint_tiled to `paint(...)` unconditionally,
# so the tiled and classic lanes must be byte-identical -- any tile
# culling/survivor-set involvement would risk a divergence here since
# the widget-chrome background base color differs from the normal
# canvas background path.
assert_equal(tiled.len(), 768)
assert_equal(classic.len(), 768)
assert_equal(tiled, classic)
# The top-left pixel falls inside the widget-panel div's own fallback
# fill (fb_rect's widget-panel branch in paint_layout.spl, the same
# 0-covered-before-round-2 fallback closed by
# simple_web_html_layout_renderer_coverage_spec.spl's
# `_widget_panel_button_doc`), not the plain-page white background --
# confirming widget_mode actually routed through the widget-chrome
# paint path rather than silently reading false. Measured via this
# same entry point (not the argb(245,245,245) canvas base, since the
# unstyled div covers the whole 32x24 frame here).
assert_equal(tiled[0], 0xFF0066CCu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering paint entry point: node/style pipeline via HTML (paint closure), has_visible_overflow_clip, _html_draw_ir_non_negative, _html_draw_ir_shadow_layer_count, _html_draw_ir_clamp_i64, _html_draw_ir_abs_i32, _html_draw_ir_saturated_i32, _html_draw_ir_background_offset, _html_draw_ir_background_edge, _tile_abs_i32, _tile_style_hash, input_text_prefix, _input_text_source_boundaries, input_caret_color, input_selection_color, _text_decoration_line_text, paint_tiled: widget_mode early-return branch.
- paint entry point: node/style pipeline via HTML (paint closure)
- has_visible_overflow_clip
- _html_draw_ir_non_negative
- _html_draw_ir_shadow_layer_count
- _html_draw_ir_clamp_i64
- _html_draw_ir_abs_i32
- _html_draw_ir_saturated_i32
- _html_draw_ir_background_offset
- _html_draw_ir_background_edge
- _tile_abs_i32
- _tile_style_hash
- input_text_prefix
- _input_text_source_boundaries
- input_caret_color
- input_selection_color
- _text_decoration_line_text
- paint_tiled: widget_mode early-return branch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
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

- Canonical SPipe generation for source `4559f370319c87998a205a05e1faebf73c08c6ea38d6a2f4e9428b3064c2d303`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4559f370319c87998a205a05e1faebf73c08c6ea38d6a2f4e9428b3064c2d303`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4559f370319c87998a205a05e1faebf73c08c6ea38d6a2f4e9428b3064c2d303`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints scrollbar-track pixels distinct from the box's own background and from the page outside it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'z-sorts unsorted positive-z-index absolute boxes so the highest z-index paints on top' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout_coverage_closure_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverses RTL #text glyph order relative to the same LTR text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
