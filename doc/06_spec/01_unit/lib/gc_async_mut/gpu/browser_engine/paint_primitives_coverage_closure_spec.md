# Paint Primitives Coverage Closure Specification

> Tests covering paint_primitives.spl coverage closure, paint_primitives.spl coverage closure: Style-driven remainder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paint Primitives Coverage Closure Specification

## Scenarios

### paint_primitives.spl coverage closure

#### fb_put clips out-of-bounds writes and fb_clear/fb_px write real pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fb_put clips out-of-bounds writes and fb_clear/fb_px write real pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_put clips out-of-bounds writes and fb_clear/fb_px write real pixels")
var fb: [u32] = [0u32; 20]
fb_put(fb, 5, 4, 2, 1, 0xAAu32)
assert_equal(fb[7], 0xAAu32)
# x = -1 is out of bounds: the whole buffer must stay untouched.
var fb2: [u32] = [0u32; 20]
fb_put(fb2, 5, 4, -1, 1, 0xAAu32)
assert_equal(fb2[0], 0u32)
var fb3: [u32] = [1u32; 6]
fb_clear(fb3, 9u32)
assert_equal(fb3[0], 9u32)
assert_equal(fb3[5], 9u32)
var fb4: [u32] = [0u32; 20]
val fb4_out = fb_px(fb4, 5, 4, 3, 2, 0x77u32)
assert_equal(fb4_out[13], 0x77u32)
```

</details>

#### reverse_text_for_paint reverses non-empty text and leaves empty text empty

- reverse_text_for_paint reverses non-empty text and leaves empty text empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverse_text_for_paint reverses non-empty text and leaves empty text empty")
assert_equal(reverse_text_for_paint("abc"), "cba")
assert_equal(reverse_text_for_paint(""), "")
```

</details>

#### apply_text_transform_for_paint covers uppercase, lowercase, capitalize, and passthrough

- apply_text_transform_for_paint covers uppercase, lowercase, capitalize, and passthrough


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_text_transform_for_paint covers uppercase, lowercase, capitalize, and passthrough")
assert_equal(apply_text_transform_for_paint("AbC", "uppercase"), "ABC")
assert_equal(apply_text_transform_for_paint("AbC", "lowercase"), "abc")
# capitalize upper-cases only the first letter of each space-separated
# word; interior letters are left as-is (real behavior, not Title Case).
assert_equal(apply_text_transform_for_paint("hello world", "capitalize"), "Hello World")
# Unrecognized transform value falls through unchanged.
assert_equal(apply_text_transform_for_paint("HeLLo", "none"), "HeLLo")
```

</details>

#### is_text_flow_fixture requires the exact 96x64 size AND both marker texts

- is_text_flow_fixture requires the exact 96x64 size AND both marker texts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_text_flow_fixture requires the exact 96x64 size AND both marker texts")
var n1 = mk_node("#text", -1)
n1.text_trimmed = "GUI"
var n2 = mk_node("#text", -1)
n2.text_trimmed = "taskbar command"
assert_true(is_text_flow_fixture([n1, n2], 96, 64))
assert_false(is_text_flow_fixture([n1, n2], 10, 10))
assert_false(is_text_flow_fixture([n1], 96, 64))
```

</details>

#### fb_text_underline paints solid, double, and dashed/gapped styles and skips zero-width

- fb_text_underline paints solid, double, and dashed/gapped styles and skips zero-width


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_text_underline paints solid, double, and dashed/gapped styles and skips zero-width")
# solid: a single line_h=1 row at y=5, columns 1..6 (fbw=10 -> row offset 50).
var fb5: [u32] = [0u32; 100]
val fb5_out = fb_text_underline(fb5, 10, 10, 1, 5, 6, 1, "solid", 0xFFu32)
assert_equal(fb5_out[51], 0xFFu32)
assert_equal(fb5_out[56], 0xFFu32)
# w<=0 must be a true no-op.
var fb5b: [u32] = [0u32; 100]
val fb5b_out = fb_text_underline(fb5b, 10, 10, 0, 0, 0, 1, "solid", 0xFFu32)
assert_equal(fb5b_out[0], 0u32)
# double: two parallel rows, y=5 and y=5+line_h+1=7 (row offset 51 and 71).
var fb5c: [u32] = [0u32; 100]
val fb5c_out = fb_text_underline(fb5c, 10, 10, 1, 5, 4, 1, "double", 0xFFu32)
assert_equal(fb5c_out[51], 0xFFu32)
assert_equal(fb5c_out[71], 0xFFu32)
# dashed: dash_w=3, gap_w=1 over w=6 at x=0,y=5 -> painted cols 0-2 and
# 4-5, col 3 is the gap and must stay clear.
var fb5d: [u32] = [0u32; 100]
val fb5d_out = fb_text_underline(fb5d, 10, 10, 0, 5, 6, 1, "dashed", 0xFFu32)
assert_equal(fb5d_out[50], 0xFFu32)
assert_equal(fb5d_out[52], 0xFFu32)
assert_equal(fb5d_out[53], 0u32)
```

</details>

#### gradient_dither_threshold covers every (px%4, py%4) cell of the 4x4 tile

- gradient_dither_threshold covers every (px%4, py%4) cell of the 4x4 tile


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gradient_dither_threshold covers every (px%4, py%4) cell of the 4x4 tile")
assert_equal(gradient_dither_threshold(0, 0), 7)
assert_equal(gradient_dither_threshold(1, 0), 10)
assert_equal(gradient_dither_threshold(2, 0), 4)
assert_equal(gradient_dither_threshold(3, 0), 7)
assert_equal(gradient_dither_threshold(0, 1), 12)
assert_equal(gradient_dither_threshold(1, 1), 2)
assert_equal(gradient_dither_threshold(2, 1), 14)
assert_equal(gradient_dither_threshold(3, 1), 2)
# my==2, mx==0 has a further px%8==4 sub-branch.
assert_equal(gradient_dither_threshold(0, 2), 7)
assert_equal(gradient_dither_threshold(4, 2), 3)
assert_equal(gradient_dither_threshold(1, 2), 11)
assert_equal(gradient_dither_threshold(2, 2), 7)
assert_equal(gradient_dither_threshold(3, 2), 9)
assert_equal(gradient_dither_threshold(0, 3), 15)
assert_equal(gradient_dither_threshold(1, 3), 2)
assert_equal(gradient_dither_threshold(2, 3), 12)
assert_equal(gradient_dither_threshold(3, 3), 5)
```

</details>

#### mix_channel_gradient_centered and mix_color_vertical_centered do dithered integer rounding

- mix_channel_gradient_centered and mix_color_vertical_centered do dithered integer rounding


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mix_channel_gradient_centered and mix_color_vertical_centered do dithered integer rounding")
# span<=0 is a passthrough of `a`.
assert_equal(mix_channel_gradient_centered(0, 1, 0, 0, 0, 0), 0)
# px=0,py=0 -> dither threshold 7: rem*16=16 > 7*2=14, rounds UP.
assert_equal(mix_channel_gradient_centered(0, 1, 0, 1, 0, 0), 1)
# px=1,py=0 -> dither threshold 10: rem*16=16 > 10*2=20 is false, rounds DOWN.
assert_equal(mix_channel_gradient_centered(0, 1, 0, 1, 1, 0), 0)
# span<=0 passthrough on the composed ARGB color too.
assert_equal(mix_color_vertical_centered(0xFF112233u32, 0xFF445566u32, 0, 0, 5, 5), 0xFF112233u32)
# Per-channel: alpha/red/green unchanged (both sides 0 or equal),
# blue channel rounds down per the px=1,py=0 case above (127, not 128).
assert_equal(mix_color_vertical_centered(0xFF000000u32, 0xFF0000FFu32, 0, 1, 1, 0), 0xFF00007Fu32)
```

</details>

#### background_gradient_pixel_opacity scales element opacity by the color's alpha channel

- background_gradient_pixel_opacity scales element opacity by the color's alpha channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("background_gradient_pixel_opacity scales element opacity by the color's alpha channel")
assert_equal(background_gradient_pixel_opacity(0xFF000000u32, 100), 100)
assert_equal(background_gradient_pixel_opacity(0x80000000u32, 50), 25)
```

</details>

#### clamp_corner_radius clamps to zero, caps at the shorter side, and passes through in range

- clamp_corner_radius clamps to zero, caps at the shorter side, and passes through in range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamp_corner_radius clamps to zero, caps at the shorter side, and passes through in range")
assert_equal(clamp_corner_radius(-3, 10, 10), 0)
assert_equal(clamp_corner_radius(100, 10, 20), 5)
assert_equal(clamp_corner_radius(3, 10, 20), 3)
```

</details>

#### _radial_center_pct parses at-keyword and percentage positions, and defaults with no 'at '

- _radial_center_pct parses at-keyword and percentage positions, and defaults with no 'at '


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_radial_center_pct parses at-keyword and percentage positions, and defaults with no 'at '")
val top_left = _radial_center_pct("circle at top left")
assert_equal(top_left[0], 0)
assert_equal(top_left[1], 0)
val bottom_right = _radial_center_pct("circle at bottom right")
assert_equal(bottom_right[0], 100)
assert_equal(bottom_right[1], 100)
val pct = _radial_center_pct("circle at 30% 40%")
assert_equal(pct[0], 30)
assert_equal(pct[1], 40)
# No "at " at all -> the true early-return default branch.
val no_at = _radial_center_pct("circle")
assert_equal(no_at[0], 50)
assert_equal(no_at[1], 50)
# "center center": the first "center" sets x_set, the second (x_set
# already true) sets y_set -- exercises both halves of that branch.
val center_center = _radial_center_pct("circle at center center")
assert_equal(center_center[0], 50)
assert_equal(center_center[1], 50)
```

</details>

#### compute_widget_paint_flags's need_text path stops at the first non-empty widget-descendant text

- compute_widget_paint_flags's need_text path stops at the first non-empty widget-descendant text


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_widget_paint_flags's need_text path stops at the first non-empty widget-descendant text")
var widget_ancestor = mk_node("div", -1)
widget_ancestor.has_widget_class = true
var child_text = mk_node("#text", 0)
child_text.text_trimmed = "hi"
val flags = compute_widget_paint_flags([widget_ancestor, child_text], false, true)
assert_false(flags.has_widget_panel)
assert_true(flags.has_nonempty_widget_text)
# not need_text: the widget_mode-seeded, panel-class-scanning branch
# (already covered by the existing coverage_spec) is re-exercised here
# with widget_mode=true to pin has_widget_panel starting true.
val flags2 = compute_widget_paint_flags([widget_ancestor, child_text], true, false)
assert_true(flags2.has_widget_panel)
assert_false(flags2.has_nonempty_widget_text)
```

</details>

#### fb_rounded_rect_row_span_opacity_clip: all-zero radii delegates to a plain rect fill, positive radii clip corners per-pixel

- fb_rounded_rect_row_span_opacity_clip: all-zero radii delegates to a plain rect fill, positive radii clip corners per-pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_rounded_rect_row_span_opacity_clip: all-zero radii delegates to a plain rect fill, positive radii clip corners per-pixel")
val clip = ClipRect(x0: 0, y0: 0, x1: 20, y1: 20)
# radii all 0 -> early-return delegation to fb_rect_opacity_clip.
var fbA: [u32] = [0u32; 400]
val fbA_out = fb_rounded_rect_row_span_opacity_clip(fbA, 20, 20, 2, 2, 10, 10, 0, 0, 0, 0, 5, 2, 8, 0xFFu32, 100, clip)
assert_equal(fbA_out[102], 0xFFu32)
# radii 4 on all corners, row py=2 is inside the top-left/top-right
# corner bands: column 2 (idx 42) falls outside both corner circles
# (clipped away), column 7 (idx 47) falls inside the top-right circle.
var fbB: [u32] = [0u32; 400]
val fbB_out = fb_rounded_rect_row_span_opacity_clip(fbB, 20, 20, 2, 2, 10, 10, 4, 4, 4, 4, 2, 2, 8, 0xFFu32, 100, clip)
assert_equal(fbB_out[42], 0u32)
assert_equal(fbB_out[47], 0xFFu32)
```

</details>

#### browser_layout_framebuffer_filled_serial fills every cell with the base color, single-worker path

- browser_layout_framebuffer_filled_serial fills every cell with the base color, single-worker path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("browser_layout_framebuffer_filled_serial fills every cell with the base color, single-worker path")
val bs = browser_layout_framebuffer_filled_serial(7u32, 3, 2)
assert_equal(bs.len(), 6)
assert_equal(bs[0], 7u32)
assert_equal(bs[5], 7u32)
```

</details>

### paint_primitives.spl coverage closure: Style-driven remainder

#### fb_style_rounded_rect_opacity_clip: zero radii delegate to an opaque rect fill

- fb_style_rounded_rect_opacity_clip: zero radii delegate to an opaque rect fill


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_rounded_rect_opacity_clip: zero radii delegate to an opaque rect fill")
var st = renderer_default_style()
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_rounded_rect_opacity_clip(fb, 10, 10, 3, 3, 2, 2, st, 0xFF0000FFu32, 100, clip)
# box covers (3,3)-(5,5) exclusive: rows 3-4, cols 3-4.
assert_equal(fb_out[33], 0xFF0000FFu32)
assert_equal(fb_out[44], 0xFF0000FFu32)
# untouched outside the box.
assert_equal(fb_out[0], 0u32)
```

</details>

#### fb_style_rounded_rect_opacity_clip: zero radii + opacity<100 delegates to blend_opacity

- fb_style_rounded_rect_opacity_clip: zero radii + opacity<100 delegates to blend_opacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_rounded_rect_opacity_clip: zero radii + opacity<100 delegates to blend_opacity")
var st = renderer_default_style()
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
# src=0xFF804020 (r=128,g=64,b=32) blended onto dst=0 at 50%:
# r=(128*50+50)/100=64, g=(64*50+50)/100=32, b=(32*50+50)/100=16.
val fb_out = fb_style_rounded_rect_opacity_clip(fb, 10, 10, 3, 3, 2, 2, st, 0xFF804020u32, 50, clip)
assert_equal(fb_out[33], 0xFF402010u32)
```

</details>

#### fb_style_rounded_rect_opacity_clip: positive corner radii clip per-pixel via the Style's own radii

- fb_style_rounded_rect_opacity_clip: positive corner radii clip per-pixel via the Style's own radii


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_rounded_rect_opacity_clip: positive corner radii clip per-pixel via the Style's own radii")
var st = renderer_default_style()
st.border_radius_tl_px = 4
st.border_radius_tr_px = 4
st.border_radius_br_px = 4
st.border_radius_bl_px = 4
val clip = ClipRect(x0: 0, y0: 0, x1: 20, y1: 20)
var fb: [u32] = [0u32; 400]
val fb_out = fb_style_rounded_rect_opacity_clip(fb, 20, 20, 2, 2, 10, 10, st, 0xFFu32, 100, clip)
# row py=2 (fbw=20 -> row offset 40): col 2 (idx 42) is clipped away by
# the top-left corner circle, col 7 (idx 47) is inside the top-right one.
assert_equal(fb_out[42], 0u32)
assert_equal(fb_out[47], 0xFFu32)
```

</details>

#### fb_style_background_opacity_clip: opaque solid fill, default padding-box clip/origin, zero radii

- fb_style_background_opacity_clip: opaque solid fill, default padding-box clip/origin, zero radii


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: opaque solid fill, default padding-box clip/origin, zero radii")
var st = renderer_default_style()
st.bg = 0xFF0000FFu32
st.opacity_pct = 100
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 2, 2, 3, 3, st, clip)
# border_l/pad_l all 0 -> padding-box clip is a no-op; box covers (2,2)-(5,5).
assert_equal(fb_out[22], 0xFF0000FFu32)
assert_equal(fb_out[44], 0xFF0000FFu32)
assert_equal(fb_out[0], 0u32)
```

</details>

#### fb_style_background_opacity_clip: translucent bg alpha folds into opacity, padding-box clip shrinks by border

- fb_style_background_opacity_clip: translucent bg alpha folds into opacity, padding-box clip shrinks by border


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: translucent bg alpha folds into opacity, padding-box clip shrinks by border")
var st = renderer_default_style()
st.bg = 0x80112233u32
st.opacity_pct = 100
st.background_clip = "padding-box"
st.border_l = 1
st.border_t = 1
st.border_r = 1
st.border_b = 1
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 2, 2, 4, 4, st, clip)
# solid_bg_alpha=128 -> solid_bg_opacity=(100*128+127)/255=50.
# bg_x=3,bg_y=3,bg_w=2,bg_h=2 (shrunk by the 1px border on every side).
# blend_opacity(0xFF112233, 0, 50): r=(17*50+50)/100=9, g=(34*50+50)/100=17, b=(51*50+50)/100=26.
assert_equal(fb_out[33], 0xFF09111Au32)
assert_equal(fb_out[44], 0xFF09111Au32)
# the border band itself (row/col 2) is left untouched.
assert_equal(fb_out[22], 0u32)
```

</details>

#### fb_style_background_opacity_clip: a clip rect that misses the box entirely is a true no-op

- fb_style_background_opacity_clip: a clip rect that misses the box entirely is a true no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: a clip rect that misses the box entirely is a true no-op")
var st = renderer_default_style()
st.bg = 0xFFFFFFFFu32
st.opacity_pct = 100
val clip = ClipRect(x0: 0, y0: 0, x1: 1, y1: 1)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 5, 5, 3, 3, st, clip)
assert_equal(fb_out[0], 0u32)
assert_equal(fb_out[55], 0u32)
```

</details>

#### fb_style_background_opacity_clip: gradient small-tile no-repeat path (from==to pins the dither-independent color)

- fb_style_background_opacity_clip: gradient small-tile no-repeat path (from==to pins the dither-independent color)


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: gradient small-tile no-repeat path (from==to pins the dither-independent color)")
var st = renderer_default_style()
st.bg = 0u32
st.background_gradient_from = 0xFF000000u32
st.background_gradient_to = 0xFF000000u32
st.background_repeat = "no-repeat"
st.background_size_w_px = 2
st.background_size_h_px = 2
st.background_position_x_px = 0
st.background_position_y_px = 0
st.background_attachment = "scroll"
st.background_clip = "border-box"
st.background_origin = "border-box"
st.opacity_pct = 100
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 2, 2, 6, 6, st, clip)
# a==b makes mix_channel_gradient_centered's remainder exactly 0, so
# every tile pixel is the flat gradient color regardless of dithering.
# tile 2x2 written at (x+0..1, y+0..1) = rows/cols 2-3.
assert_equal(fb_out[22], 0xFF000000u32)
assert_equal(fb_out[23], 0xFF000000u32)
assert_equal(fb_out[32], 0xFF000000u32)
# outside the 2x2 tile (col/row 4) stays untouched -- proves the tile
# does not silently cover the whole box.
assert_equal(fb_out[44], 0u32)
```

</details>

#### fb_style_background_opacity_clip: gradient repeat path (non-small-tile else branch) fills the whole box

- fb_style_background_opacity_clip: gradient repeat path (non-small-tile else branch) fills the whole box


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: gradient repeat path (non-small-tile else branch) fills the whole box")
var st = renderer_default_style()
st.bg = 0u32
st.background_gradient_from = 0xFF000000u32
st.background_gradient_to = 0xFF000000u32
st.background_repeat = "repeat"
st.background_size_w_px = 0
st.background_size_h_px = 0
st.background_attachment = "scroll"
st.background_clip = "border-box"
st.background_origin = "border-box"
st.opacity_pct = 100
val clip = ClipRect(x0: 0, y0: 0, x1: 8, y1: 8)
var fb: [u32] = [0u32; 64]
val fb_out = fb_style_background_opacity_clip(fb, 8, 8, 1, 1, 4, 3, st, clip)
# repeat (not no-repeat) forces the "else" per-row branch (sw=max_x),
# filling every cell of the (1,1)-(5,4) box.
assert_equal(fb_out[9], 0xFF000000u32)
assert_equal(fb_out[28], 0xFF000000u32)
# (5,3) is one column past the box's right edge (w=4 covers x=1..4).
assert_equal(fb_out[29], 0u32)
```

</details>

#### fb_style_background_opacity_clip: content-box clip AND origin shrink the box by border+padding

- fb_style_background_opacity_clip: content-box clip AND origin shrink the box by border+padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: content-box clip AND origin shrink the box by border+padding")
var st = renderer_default_style()
st.bg = 0xFF445566u32
st.opacity_pct = 100
st.background_clip = "content-box"
st.background_origin = "content-box"
st.border_l = 1
st.border_t = 1
st.border_r = 1
st.border_b = 1
st.pad_l = 1
st.pad_t = 1
st.pad_r = 1
st.pad_b = 1
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 0, 0, 8, 8, st, clip)
# bg_x/y = 0 + border(1) + pad(1) = 2; bg_w/h = 8 - 2*(border+pad) = 4.
assert_equal(fb_out[22], 0xFF445566u32)
assert_equal(fb_out[55], 0xFF445566u32)
assert_equal(fb_out[11], 0u32)
assert_equal(fb_out[66], 0u32)
```

</details>

#### fb_style_background_opacity_clip: w<=0 hits the bg_w<=0 early-return no-op

- fb_style_background_opacity_clip: w<=0 hits the bg_w<=0 early-return no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: w<=0 hits the bg_w<=0 early-return no-op")
var st = renderer_default_style()
st.bg = 0xFFAABBCCu32
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [5u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 2, 2, 0, 3, st, clip)
assert_equal(fb_out[0], 5u32)
assert_equal(fb_out[22], 5u32)
```

</details>

#### fb_style_background_opacity_clip: image_origin_w<=0 falls back to the bg_* rect (default padding-box origin)

- fb_style_background_opacity_clip: image_origin_w<=0 falls back to the bg_* rect (default padding-box origin)


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: image_origin_w<=0 falls back to the bg_* rect (default padding-box origin)")
var st = renderer_default_style()
st.bg = 0xFF112233u32
st.opacity_pct = 100
# default background_origin ("padding-box") is neither the "border-box"
# nor "content-box" elif, so image_origin_w = w - border_l - border_r
# is computed directly; border_l+border_r >= w drives it <= 0, while
# bg_w (border-box background_clip default, unaffected by border_l/r)
# stays positive so the solid fill still proceeds.
st.border_l = 5
st.border_r = 5
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 0, 0, 6, 4, st, clip)
assert_equal(fb_out[23], 0xFF112233u32)
assert_equal(fb_out[27], 0u32)
```

</details>

#### fb_style_background_opacity_clip: a fully-transparent bg color folds to opacity<=0 and no-ops

- fb_style_background_opacity_clip: a fully-transparent bg color folds to opacity<=0 and no-ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: a fully-transparent bg color folds to opacity<=0 and no-ops")
var st = renderer_default_style()
# alpha byte 0 -> solid_bg_opacity = (opacity_pct*0+127)/255 = 0.
st.bg = 0x00112233u32
st.opacity_pct = 100
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 2, 2, 3, 3, st, clip)
assert_equal(fb_out[22], 0u32)
```

</details>

#### fb_style_background_opacity_clip: opaque solid layer THEN gradient tile paint on top of it

- fb_style_background_opacity_clip: opaque solid layer THEN gradient tile paint on top of it


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fb_style_background_opacity_clip: opaque solid layer THEN gradient tile paint on top of it")
var st = renderer_default_style()
st.bg = 0xFF00FF00u32
st.opacity_pct = 100
st.background_gradient_from = 0xFF000000u32
st.background_gradient_to = 0xFF000000u32
st.background_repeat = "no-repeat"
st.background_size_w_px = 2
st.background_size_h_px = 2
st.background_position_x_px = 0
st.background_position_y_px = 0
st.background_attachment = "scroll"
st.background_clip = "border-box"
st.background_origin = "border-box"
val clip = ClipRect(x0: 0, y0: 0, x1: 10, y1: 10)
var fb: [u32] = [0u32; 100]
val fb_out = fb_style_background_opacity_clip(fb, 10, 10, 2, 2, 6, 6, st, clip)
# the solid green layer fills the whole (2,2)-(8,8) box first; the
# 2x2 gradient tile then overwrites its own corner with black.
assert_equal(fb_out[22], 0xFF000000u32)
assert_equal(fb_out[55], 0xFF00FF00u32)
assert_equal(fb_out[88], 0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering paint_primitives.spl coverage closure, paint_primitives.spl coverage closure: Style-driven remainder.
- paint_primitives.spl coverage closure
- paint_primitives.spl coverage closure: Style-driven remainder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `4e6f818cf7ccbaccd0c5b83875dfa4d2920d228af70771dc45f1a0a8262f9131`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e6f818cf7ccbaccd0c5b83875dfa4d2920d228af70771dc45f1a0a8262f9131`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e6f818cf7ccbaccd0c5b83875dfa4d2920d228af70771dc45f1a0a8262f9131`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fb_put clips out-of-bounds writes and fb_clear/fb_px write real pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverse_text_for_paint reverses non-empty text and leaves empty text empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/paint_primitives_coverage_closure_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_text_transform_for_paint covers uppercase, lowercase, capitalize, and passthrough' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
