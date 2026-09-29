# HTML Layout Renderer Decl Apply — Coverage Closure (tranche 3)

> Purpose: Prove that decl_apply early returns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 68 | 68 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Layout Renderer Decl Apply — Coverage Closure (tranche 3)

Purpose: Prove that decl_apply early returns.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that decl_apply early returns.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### decl_apply early returns

#### empty declaration block returns the style unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty declaration block returns the style unchanged
- Verify: empty declaration block returns the style unchanged
   - Expected: st.width_px equals `base.width_px`
   - Expected: st.fg equals `base.fg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("empty declaration block returns the style unchanged")
step("Verify: empty declaration block returns the style unchanged")
# @req: REQ-BROWSER-ENGINE-SIMPLE-WEB-HTML-LAYOUT-RENDERER-DECL-APPLY-COVERAGE-CLOSURE-SPEC-SPL-001
val base = renderer_default_style()
val st = apply_decls(base, "", 16)
expect(st.width_px).to_equal(base.width_px)
expect(st.fg).to_equal(base.fg)
```

</details>

#### a rule over the per-rule declaration quota is dropped wholesale

- a rule over the per-rule declaration quota is dropped wholesale
- Verify: a rule over the per-rule declaration quota is dropped wholesale
   - Expected: st.width_px equals `base.width_px`
   - Expected: st.fg equals `base.fg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("a rule over the per-rule declaration quota is dropped wholesale")
step("Verify: a rule over the per-rule declaration quota is dropped wholesale")
var decls = "width:10px"
var i = 0
while i < 260:
    decls = decls + ";color:#123456"
    i = i + 1
val st = apply_decls(renderer_default_style(), decls, 16)
val base = renderer_default_style()
expect(st.width_px).to_equal(base.width_px)
expect(st.fg).to_equal(base.fg)
```

</details>

### decl_apply box model lengths

#### applies width/height/min/max in px

- applies width/height/min/max in px
- Verify: applies width/height/min/max in px
   - Expected: st.width_px equals `120`
   - Expected: st.height_px equals `48`
   - Expected: st.min_width_px equals `10`
   - Expected: st.max_width_px equals `300`
   - Expected: st.min_height_px equals `5`
   - Expected: st.max_height_px equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("applies width/height/min/max in px")
step("Verify: applies width/height/min/max in px")
val st = ap("width:120px;height:48px;min-width:10px;max-width:300px;min-height:5px;max-height:400px")
expect(st.width_px).to_equal(120)  # oracle: 120 — named expected value from the requirement
expect(st.height_px).to_equal(48)  # oracle: 48 — named expected value from the requirement
expect(st.min_width_px).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(st.max_width_px).to_equal(300)  # oracle: 300 — named expected value from the requirement
expect(st.min_height_px).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(st.max_height_px).to_equal(400)  # oracle: 400 — named expected value from the requirement
```

</details>

#### font-size em lengths scale by em_base (width does not support em)

- font-size em lengths scale by em_base (width does not support em)
- Verify: font-size em lengths scale by em_base (width does not support em)
   - Expected: st.font_size equals `40`
   - Expected: w.width_px equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("font-size em lengths scale by em_base (width does not support em)")
step("Verify: font-size em lengths scale by em_base (width does not support em)")
val st = apply_decls(renderer_default_style(), "font-size:2em;letter-spacing:0px", 20)
expect(st.font_size).to_equal(40)  # oracle: 40 — named expected value from the requirement
# width has no em branch: the numeric prefix is taken as-is
val w = apply_decls(renderer_default_style(), "width:2em;letter-spacing:0px", 20)
expect(w.width_px).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### padding shorthand 1/2/4-value forms

- padding shorthand 1/2/4-value forms
- Verify: padding shorthand 1/2/4-value forms
   - Expected: one.pad_l equals `8`
   - Expected: one.pad_t equals `8`
   - Expected: one.pad_r equals `8`
   - Expected: one.pad_b equals `8`
   - Expected: two.pad_t equals `4`
   - Expected: two.pad_b equals `4`
   - Expected: two.pad_l equals `12`
   - Expected: two.pad_r equals `12`
   - Expected: four.pad_t equals `1`
   - Expected: four.pad_r equals `2`
   - Expected: four.pad_b equals `3`
   - Expected: four.pad_l equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("padding shorthand 1/2/4-value forms")
step("Verify: padding shorthand 1/2/4-value forms")
val one = ap("padding:8px")
expect(one.pad_l).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(one.pad_t).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(one.pad_r).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(one.pad_b).to_equal(8)  # oracle: 8 — named expected value from the requirement
val two = ap("padding:4px 12px")
expect(two.pad_t).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(two.pad_b).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(two.pad_l).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(two.pad_r).to_equal(12)  # oracle: 12 — named expected value from the requirement
val four = ap("padding:1px 2px 3px 4px")
expect(four.pad_t).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(four.pad_r).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(four.pad_b).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(four.pad_l).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### margin shorthand and auto margins

- margin shorthand and auto margins
- Verify: margin shorthand and auto margins
   - Expected: st.margin_t equals `5`
   - Expected: st.margin_r equals `6`
   - Expected: st.margin_b equals `7`
   - Expected: st.margin_l equals `8`
   - Expected: au.margin_l_auto is true
   - Expected: au.margin_r_auto is true
   - Expected: au.margin_t_auto is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("margin shorthand and auto margins")
step("Verify: margin shorthand and auto margins")
val st = ap("margin:5px 6px 7px 8px")
expect(st.margin_t).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(st.margin_r).to_equal(6)  # oracle: 6 — named expected value from the requirement
expect(st.margin_b).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(st.margin_l).to_equal(8)  # oracle: 8 — named expected value from the requirement
val au = ap("margin:0 auto")
expect(au.margin_l_auto).to_equal(true)
expect(au.margin_r_auto).to_equal(true)
expect(au.margin_t_auto).to_equal(false)
```

</details>

#### individual margin/padding longhands win over earlier shorthand

- individual margin/padding longhands win over earlier shorthand
- Verify: individual margin/padding longhands win over earlier shorthand
   - Expected: st.margin_l equals `9`
   - Expected: st.margin_t equals `2`
   - Expected: st.pad_b equals `11`
   - Expected: st.pad_t equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("individual margin/padding longhands win over earlier shorthand")
step("Verify: individual margin/padding longhands win over earlier shorthand")
val st = ap("margin:2px;margin-left:9px;padding:3px;padding-bottom:11px")
expect(st.margin_l).to_equal(9)  # oracle: 9 — named expected value from the requirement
expect(st.margin_t).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.pad_b).to_equal(11)  # oracle: 11 — named expected value from the requirement
expect(st.pad_t).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### box-sizing border-box toggles border_box

- box-sizing border-box toggles border_box
- Verify: box-sizing border-box toggles border_box
   - Expected: ap("box-sizing:border-box").border_box is true
   - Expected: ap("box-sizing:content-box").border_box is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("box-sizing border-box toggles border_box")
step("Verify: box-sizing border-box toggles border_box")
expect(ap("box-sizing:border-box").border_box).to_equal(true)
expect(ap("box-sizing:content-box").border_box).to_equal(false)
```

</details>

### decl_apply borders

#### border shorthand sets width, sides and color

- border shorthand sets width, sides and color
- Verify: border shorthand sets width, sides and color
   - Expected: st.border_w equals `3`
   - Expected: st.border_l equals `3`
   - Expected: st.border_b equals `3`
   - Expected: st.border_color equals `ap("border-color:#112233").border_color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border shorthand sets width, sides and color")
step("Verify: border shorthand sets width, sides and color")
val st = ap("border:3px solid #112233")
expect(st.border_w).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_l).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_b).to_equal(3)  # oracle: 3 — named expected value from the requirement
# same color through the border-color longhand path (relational oracle)
expect(st.border_color).to_equal(ap("border-color:#112233").border_color)
```

</details>

#### per-side border widths (left/right require a paintable style)

- per-side border widths (left/right require a paintable style)
- Verify: per-side border widths (left/right require a paintable style)
   - Expected: st.border_l equals `1`
   - Expected: st.border_t equals `2`
   - Expected: st.border_r equals `3`
   - Expected: st.border_b equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("per-side border widths (left/right require a paintable style)")
step("Verify: per-side border widths (left/right require a paintable style)")
val st = ap("border-left-style:solid;border-right-style:solid;border-left-width:1px;border-top-width:2px;border-right-width:3px;border-bottom-width:4px")
expect(st.border_l).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(st.border_t).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.border_r).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_b).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### l/r widths without a border style are zeroed (default style none), t/b are kept

- l/r widths without a border style are zeroed (default style none), t/b are kept
- Verify: l/r widths without a border style are zeroed (default style none), t/b are kept
   - Expected: st.border_l equals `0`
   - Expected: st.border_r equals `0`
   - Expected: st.border_t equals `2`
   - Expected: st.border_b equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("l/r widths without a border style are zeroed (default style none), t/b are kept")
step("Verify: l/r widths without a border style are zeroed (default style none), t/b are kept")
# Style only tracks border_style_l/border_style_r; the none/hidden
# paint-disable pass therefore applies to left/right only.
val st = ap("border-left-width:1px;border-top-width:2px;border-right-width:3px;border-bottom-width:4px")
expect(st.border_l).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_r).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_t).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.border_b).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### per-side border colors parse hex

- per-side border colors parse hex
- Verify: per-side border colors parse hex
   - Expected: st.border_color_l equals `st.border_color_t`
   - Expected: st.border_color_l == renderer_default_style().border_color_l is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("per-side border colors parse hex")
step("Verify: per-side border colors parse hex")
val st = ap("border-left-color:#0000ff;border-top-color:#0000ff")
expect(st.border_color_l).to_equal(st.border_color_t)
expect(st.border_color_l == renderer_default_style().border_color_l).to_equal(false)
```

</details>

#### border-radius shorthand and corners

- border-radius shorthand and corners
- Verify: border-radius shorthand and corners
   - Expected: st.border_radius_px equals `6`
   - Expected: c.border_radius_tl_px equals `1`
   - Expected: c.border_radius_tr_px equals `2`
   - Expected: c.border_radius_br_px equals `3`
   - Expected: c.border_radius_bl_px equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-radius shorthand and corners")
step("Verify: border-radius shorthand and corners")
val st = ap("border-radius:6px")
expect(st.border_radius_px).to_equal(6)  # oracle: 6 — named expected value from the requirement
val c = ap("border-radius:1px 2px 3px 4px")
expect(c.border_radius_tl_px).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(c.border_radius_tr_px).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(c.border_radius_br_px).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(c.border_radius_bl_px).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### outline shorthand sets width and offset longhand applies

- outline shorthand sets width and offset longhand applies
- Verify: outline shorthand sets width and offset longhand applies
   - Expected: st.outline_w equals `2`
   - Expected: st.outline_offset_px equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("outline shorthand sets width and offset longhand applies")
step("Verify: outline shorthand sets width and offset longhand applies")
val st = ap("outline:2px solid red;outline-offset:3px")
expect(st.outline_w).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.outline_offset_px).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### border-collapse and border-spacing

- border-collapse and border-spacing
- Verify: border-collapse and border-spacing
   - Expected: st.border_collapse equals `collapse`
   - Expected: st.border_spacing_x_px equals `4`
   - Expected: st.border_spacing_y_px equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-collapse and border-spacing")
step("Verify: border-collapse and border-spacing")
val st = ap("border-collapse:collapse;border-spacing:4px 7px")
expect(st.border_collapse).to_equal("collapse")
expect(st.border_spacing_x_px).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(st.border_spacing_y_px).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

### decl_apply display, position, inset

#### display keywords land in display

- display keywords land in display
- Verify: display keywords land in display
   - Expected: ap("display:flex").display equals `flex`
   - Expected: ap("display:none").display equals `none`
   - Expected: ap("display:inline-block").display equals `inline-block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("display keywords land in display")
step("Verify: display keywords land in display")
expect(ap("display:flex").display).to_equal("flex")
expect(ap("display:none").display).to_equal("none")
expect(ap("display:inline-block").display).to_equal("inline-block")
```

</details>

#### position keywords set the exclusive position flags

- position keywords set the exclusive position flags
- Verify: position keywords set the exclusive position flags
   - Expected: rel.position_relative is true
   - Expected: rel.position_absolute is false
   - Expected: abs.position_absolute is true
   - Expected: abs.left_px equals `10`
   - Expected: abs.top_px equals `20`
   - Expected: abs.right_px equals `30`
   - Expected: abs.bottom_px equals `40`
   - Expected: ap("position:fixed").position_fixed is true
   - Expected: ap("position:sticky").position_sticky is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("position keywords set the exclusive position flags")
step("Verify: position keywords set the exclusive position flags")
val rel = ap("position:relative")
expect(rel.position_relative).to_equal(true)
expect(rel.position_absolute).to_equal(false)
val abs = ap("position:absolute;left:10px;top:20px;right:30px;bottom:40px")
expect(abs.position_absolute).to_equal(true)
expect(abs.left_px).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(abs.top_px).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(abs.right_px).to_equal(30)  # oracle: 30 — named expected value from the requirement
expect(abs.bottom_px).to_equal(40)  # oracle: 40 — named expected value from the requirement
expect(ap("position:fixed").position_fixed).to_equal(true)
expect(ap("position:sticky").position_sticky).to_equal(true)
```

</details>

#### z-index and opacity

- z-index and opacity
- Verify: z-index and opacity
   - Expected: ap("z-index:7").z_index equals `7`
   - Expected: ap("opacity:0.5").opacity_pct equals `50`
   - Expected: ap("opacity:1").opacity_pct equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("z-index and opacity")
step("Verify: z-index and opacity")
expect(ap("z-index:7").z_index).to_equal(7)
expect(ap("opacity:0.5").opacity_pct).to_equal(50)
expect(ap("opacity:1").opacity_pct).to_equal(100)
```

</details>

### decl_apply flex

#### flex container properties

- flex container properties
- Verify: flex container properties
   - Expected: st.flex_direction equals `column`
   - Expected: st.flex_wrap equals `wrap`
   - Expected: st.justify_content equals `center`
   - Expected: st.align_items equals `center`
   - Expected: st.align_content equals `center`
   - Expected: st.gap_px equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("flex container properties")
step("Verify: flex container properties")
val st = ap("flex-direction:column;flex-wrap:wrap;justify-content:center;align-items:center;align-content:center;gap:9px")
expect(st.flex_direction).to_equal("column")
expect(st.flex_wrap).to_equal("wrap")
expect(st.justify_content).to_equal("center")
expect(st.align_items).to_equal("center")
expect(st.align_content).to_equal("center")
expect(st.gap_px).to_equal(9)  # oracle: 9 — named expected value from the requirement
```

</details>

#### row-gap and column-gap longhands

- row-gap and column-gap longhands
- Verify: row-gap and column-gap longhands
   - Expected: st.row_gap_px equals `3`
   - Expected: st.column_gap_px equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("row-gap and column-gap longhands")
step("Verify: row-gap and column-gap longhands")
val st = ap("row-gap:3px;column-gap:5px")
expect(st.row_gap_px).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.column_gap_px).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### flex item properties

- flex item properties
- Verify: flex item properties
   - Expected: st.flex_grow equals `2`
   - Expected: st.flex_shrink equals `3`
   - Expected: st.flex_basis_px equals `44`
   - Expected: st.order equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("flex item properties")
step("Verify: flex item properties")
val st = ap("flex-grow:2;flex-shrink:3;flex-basis:44px;order:5;align-self:end")
expect(st.flex_grow).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.flex_shrink).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.flex_basis_px).to_equal(44)  # oracle: 44 — named expected value from the requirement
expect(st.order).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### decl_apply overflow and visibility

#### overflow hidden and scroll axes

- overflow hidden and scroll axes
- Verify: overflow hidden and scroll axes
   - Expected: ap("overflow:hidden").overflow_hidden is true
   - Expected: ap("overflow-y:auto").overflow_auto_y is true
   - Expected: ap("overflow-y:scroll").overflow_scroll_y is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("overflow hidden and scroll axes")
step("Verify: overflow hidden and scroll axes")
expect(ap("overflow:hidden").overflow_hidden).to_equal(true)
expect(ap("overflow-y:auto").overflow_auto_y).to_equal(true)
expect(ap("overflow-y:scroll").overflow_scroll_y).to_equal(true)
```

</details>

#### visibility and content-visibility hidden

- visibility and content-visibility hidden
- Verify: visibility and content-visibility hidden
   - Expected: ap("visibility:hidden").visibility_hidden is true
   - Expected: ap("visibility:visible").visibility_hidden is false
   - Expected: ap("content-visibility:hidden").content_visibility_hidden is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("visibility and content-visibility hidden")
step("Verify: visibility and content-visibility hidden")
expect(ap("visibility:hidden").visibility_hidden).to_equal(true)
expect(ap("visibility:visible").visibility_hidden).to_equal(false)
expect(ap("content-visibility:hidden").content_visibility_hidden).to_equal(true)
```

</details>

#### text-overflow ellipsis and white-space nowrap

- text-overflow ellipsis and white-space nowrap
- Verify: text-overflow ellipsis and white-space nowrap
   - Expected: ap("text-overflow:ellipsis").text_overflow_ellipsis is true
   - Expected: ap("white-space:nowrap").white_space_nowrap is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("text-overflow ellipsis and white-space nowrap")
step("Verify: text-overflow ellipsis and white-space nowrap")
expect(ap("text-overflow:ellipsis").text_overflow_ellipsis).to_equal(true)
expect(ap("white-space:nowrap").white_space_nowrap).to_equal(true)
```

</details>

### decl_apply typography

#### font-size, family, weight, style, line-height

- font-size, family, weight, style, line-height
- Verify: font-size, family, weight, style, line-height
   - Expected: st.font_size equals `22`
   - Expected: st.font_family equals `Georgia`
   - Expected: st.bold is true
   - Expected: st.font_style_italic is true
   - Expected: st.line_height_px equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("font-size, family, weight, style, line-height")
step("Verify: font-size, family, weight, style, line-height")
val st = ap("font-size:22px;font-family:Georgia;font-weight:bold;font-style:italic;line-height:30px")
expect(st.font_size).to_equal(22)  # oracle: 22 — named expected value from the requirement
expect(st.font_family).to_equal("Georgia")
expect(st.bold).to_equal(true)
expect(st.font_style_italic).to_equal(true)
expect(st.line_height_px).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### numeric font-weight 700 is bold, 400 is not

- numeric font-weight 700 is bold, 400 is not
- Verify: numeric font-weight 700 is bold, 400 is not
   - Expected: ap("font-weight:700").bold is true
   - Expected: ap("font-weight:400").bold is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("numeric font-weight 700 is bold, 400 is not")
step("Verify: numeric font-weight 700 is bold, 400 is not")
expect(ap("font-weight:700").bold).to_equal(true)
expect(ap("font-weight:400").bold).to_equal(false)
```

</details>

#### font shorthand sets size and family

- font shorthand sets size and family
- Verify: font shorthand sets size and family
   - Expected: st.font_size equals `18`
   - Expected: st.font_family equals `Verdana`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("font shorthand sets size and family")
step("Verify: font shorthand sets size and family")
val st = ap("font:italic bold 18px/24px Verdana")
expect(st.font_size).to_equal(18)  # oracle: 18 — named expected value from the requirement
expect(st.font_family).to_equal("Verdana")
```

</details>

#### text-align and text-transform and text-indent

- text-align and text-transform and text-indent
- Verify: text-align and text-transform and text-indent
   - Expected: st.text_align equals `center`
   - Expected: st.text_transform equals `uppercase`
   - Expected: st.text_indent_px equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("text-align and text-transform and text-indent")
step("Verify: text-align and text-transform and text-indent")
val st = ap("text-align:center;text-transform:uppercase;text-indent:12px")
expect(st.text_align).to_equal("center")
expect(st.text_transform).to_equal("uppercase")
expect(st.text_indent_px).to_equal(12)  # oracle: 12 — named expected value from the requirement
```

</details>

#### letter-spacing and word-spacing

- letter-spacing and word-spacing
- Verify: letter-spacing and word-spacing
   - Expected: st.letter_spacing_px equals `3`
   - Expected: st.word_spacing_px equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("letter-spacing and word-spacing")
step("Verify: letter-spacing and word-spacing")
val st = apply_decls(renderer_default_style(), "letter-spacing:3px;word-spacing:5px", 16)
expect(st.letter_spacing_px).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.word_spacing_px).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### direction and writing-mode

- direction and writing-mode
- Verify: direction and writing-mode
   - Expected: st.direction_rtl is true
   - Expected: st.writing_mode equals `vertical-rl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("direction and writing-mode")
step("Verify: direction and writing-mode")
val st = ap("direction:rtl;writing-mode:vertical-rl")
expect(st.direction_rtl).to_equal(true)
expect(st.writing_mode).to_equal("vertical-rl")
```

</details>

#### font-variant-caps and font-kerning keywords are recorded

- font-variant-caps and font-kerning keywords are recorded
- Verify: font-variant-caps and font-kerning keywords are recorded
   - Expected: st.font_variant_caps equals `small-caps`
   - Expected: st.font_kerning equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("font-variant-caps and font-kerning keywords are recorded")
step("Verify: font-variant-caps and font-kerning keywords are recorded")
val st = ap("font-variant-caps:small-caps;font-kerning:none")
expect(st.font_variant_caps).to_equal("small-caps")
expect(st.font_kerning).to_equal("none")
```

</details>

### decl_apply text decoration

#### text-decoration line kinds

- text-decoration line kinds
- Verify: text-decoration line kinds
   - Expected: u.text_decoration_underline is true
   - Expected: l.text_decoration_line_through is true
   - Expected: o.text_decoration_overline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("text-decoration line kinds")
step("Verify: text-decoration line kinds")
val u = ap("text-decoration:underline")
expect(u.text_decoration_underline).to_equal(true)
val l = ap("text-decoration:line-through")
expect(l.text_decoration_line_through).to_equal(true)
val o = ap("text-decoration:overline")
expect(o.text_decoration_overline).to_equal(true)
```

</details>

#### text-decoration none clears underline

- text-decoration none clears underline
- Verify: text-decoration none clears underline
   - Expected: st.text_decoration_underline is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("text-decoration none clears underline")
step("Verify: text-decoration none clears underline")
val st = ap("text-decoration:underline;text-decoration:none")
expect(st.text_decoration_underline).to_equal(false)
```

</details>

#### decoration style, thickness and underline offset

- decoration style, thickness and underline offset
- Verify: decoration style, thickness and underline offset
   - Expected: st.text_decoration_style equals `dashed`
   - Expected: st.text_decoration_thickness_px equals `2`
   - Expected: st.text_underline_offset_px equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("decoration style, thickness and underline offset")
step("Verify: decoration style, thickness and underline offset")
val st = ap("text-decoration-style:dashed;text-decoration-thickness:2px;text-underline-offset:4px")
expect(st.text_decoration_style).to_equal("dashed")
expect(st.text_decoration_thickness_px).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.text_underline_offset_px).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### decl_apply backgrounds

#### background-color parses hex directly and keywords via the named table

- background-color parses hex directly and keywords via the named table
- Verify: background-color parses hex directly and keywords via the named table
   - Expected: hex.bg equals `0xFFFF0000u32`
   - Expected: kw.bg == renderer_default_style().bg is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("background-color parses hex directly and keywords via the named table")
step("Verify: background-color parses hex directly and keywords via the named table")
val hex = ap("background-color:#ff0000")
expect(hex.bg).to_equal(0xFFFF0000u32)
# 'red' resolves through the named-color table (a themed red, not #ff0000)
val kw = ap("background-color:red")
expect(kw.bg == renderer_default_style().bg).to_equal(false)
```

</details>

#### background repeat, attachment, clip, origin keywords

- background repeat, attachment, clip, origin keywords
- Verify: background repeat, attachment, clip, origin keywords
   - Expected: st.background_repeat equals `no-repeat`
   - Expected: st.background_attachment equals `fixed`
   - Expected: st.background_clip equals `padding-box`
   - Expected: st.background_origin equals `border-box`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("background repeat, attachment, clip, origin keywords")
step("Verify: background repeat, attachment, clip, origin keywords")
val st = ap("background-repeat:no-repeat;background-attachment:fixed;background-clip:padding-box;background-origin:border-box")
expect(st.background_repeat).to_equal("no-repeat")
expect(st.background_attachment).to_equal("fixed")
expect(st.background_clip).to_equal("padding-box")
expect(st.background_origin).to_equal("border-box")
```

</details>

#### background-size and position in px

- background-size and position in px
- Verify: background-size and position in px
   - Expected: st.background_size_w_px equals `40`
   - Expected: st.background_size_h_px equals `30`
   - Expected: st.background_position_x_px equals `10`
   - Expected: st.background_position_y_px equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("background-size and position in px")
step("Verify: background-size and position in px")
val st = ap("background-size:40px 30px;background-position:10px 20px")
expect(st.background_size_w_px).to_equal(40)  # oracle: 40 — named expected value from the requirement
expect(st.background_size_h_px).to_equal(30)  # oracle: 30 — named expected value from the requirement
expect(st.background_position_x_px).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(st.background_position_y_px).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### background-image url is recorded

- background-image url is recorded
- Verify: background-image url is recorded
   - Expected: st.background_image_uri contains `foo.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("background-image url is recorded")
step("Verify: background-image url is recorded")
val st = ap("background-image:url(foo.png)")
expect(st.background_image_uri.contains("foo.png")).to_equal(true)
```

</details>

#### background-image linear-gradient records from/to and the stop model

- background-image linear-gradient records from/to and the stop model
- Verify: background-image linear-gradient records from/to and the stop model
   - Expected: st.background_gradient_from equals `0xFFFF0000u32`
   - Expected: st.background_gradient_to equals `0xFF0000FFu32`
   - Expected: st.background_gradient_stop_colors.len() equals `2`
   - Expected: sh.background_gradient_from equals `0u32`
   - Expected: sh.bg_layers_raw contains `linear-gradient`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("background-image linear-gradient records from/to and the stop model")
step("Verify: background-image linear-gradient records from/to and the stop model")
val st = ap("background-image:linear-gradient(#ff0000,#0000ff)")
expect(st.background_gradient_from).to_equal(0xFFFF0000u32)
expect(st.background_gradient_to).to_equal(0xFF0000FFu32)
expect(st.background_gradient_stop_colors.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
# the background SHORTHAND keeps the layer raw instead of decoding here
val sh = ap("background:linear-gradient(to bottom,#ff0000,#0000ff)")
expect(sh.background_gradient_from).to_equal(0u32)
expect(sh.bg_layers_raw.contains("linear-gradient")).to_equal(true)
```

</details>

### decl_apply shadows and misc

#### box-shadow sets offsets and blur

- box-shadow sets offsets and blur
- Verify: box-shadow sets offsets and blur
   - Expected: st.box_shadow_x_px equals `2`
   - Expected: st.box_shadow_y_px equals `3`
   - Expected: st.box_shadow_blur_px equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("box-shadow sets offsets and blur")
step("Verify: box-shadow sets offsets and blur")
val st = ap("box-shadow:2px 3px 4px rgba(0,0,0,0.5)")
expect(st.box_shadow_x_px).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.box_shadow_y_px).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.box_shadow_blur_px).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### text-shadow sets offsets

- text-shadow sets offsets
- Verify: text-shadow sets offsets
   - Expected: st.text_shadow_x_px equals `1`
   - Expected: st.text_shadow_y_px equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("text-shadow sets offsets")
step("Verify: text-shadow sets offsets")
val st = ap("text-shadow:1px 2px #000000")
expect(st.text_shadow_x_px).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(st.text_shadow_y_px).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### cursor, caption-side, table-layout, vertical-align keywords

- cursor, caption-side, table-layout, vertical-align keywords
- Verify: cursor, caption-side, table-layout, vertical-align keywords
   - Expected: st.cursor equals `pointer`
   - Expected: st.caption_side equals `bottom`
   - Expected: st.table_layout equals `fixed`
   - Expected: st.vertical_align equals `middle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("cursor, caption-side, table-layout, vertical-align keywords")
step("Verify: cursor, caption-side, table-layout, vertical-align keywords")
val st = ap("cursor:pointer;caption-side:bottom;table-layout:fixed;vertical-align:middle")
expect(st.cursor).to_equal("pointer")
expect(st.caption_side).to_equal("bottom")
expect(st.table_layout).to_equal("fixed")
expect(st.vertical_align).to_equal("middle")
```

</details>

#### transition and animation longhands are recorded

- transition and animation longhands are recorded
- Verify: transition and animation longhands are recorded
   - Expected: st.transition_property equals `opacity`
   - Expected: st.transition_duration_ms equals `200`
   - Expected: st.animation_name equals `spin`
   - Expected: st.animation_duration_ms equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("transition and animation longhands are recorded")
step("Verify: transition and animation longhands are recorded")
val st = ap("transition-property:opacity;transition-duration:200ms;animation-name:spin;animation-duration:1s;animation-iteration-count:3")
expect(st.transition_property).to_equal("opacity")
expect(st.transition_duration_ms).to_equal(200)  # oracle: 200 — named expected value from the requirement
expect(st.animation_name).to_equal("spin")
expect(st.animation_duration_ms).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
```

</details>

### decl_apply logical border longhands (tranche 4)

#### border-block shorthand sets top+bottom width and color together

- border-block shorthand sets top+bottom width and color together
- Verify: border-block shorthand sets top+bottom width and color together
   - Expected: st.border_t equals `3`
   - Expected: st.border_b equals `3`
   - Expected: st.border_color_t equals `st.border_color_b`
   - Expected: st.border_color_t == renderer_default_style().border_color_t is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block shorthand sets top+bottom width and color together")
step("Verify: border-block shorthand sets top+bottom width and color together")
val st = ap("border-block:3px solid #112233")
expect(st.border_t).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_b).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_color_t).to_equal(st.border_color_b)
expect(st.border_color_t == renderer_default_style().border_color_t).to_equal(false)
```

</details>

#### border-block-start/end map to top/bottom independently

- border-block-start/end map to top/bottom independently
- Verify: border-block-start/end map to top/bottom independently
   - Expected: st.border_t equals `2`
   - Expected: st.border_b equals `5`
   - Expected: st.border_color_t == st.border_color_b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block-start/end map to top/bottom independently")
step("Verify: border-block-start/end map to top/bottom independently")
val st = ap("border-block-start:2px solid #ff0000;border-block-end:5px solid #00ff00")
expect(st.border_t).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.border_b).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(st.border_color_t == st.border_color_b).to_equal(false)
```

</details>

#### bare border-block:none disables top/bottom paint; a multi-token value does not

- bare border-block:none disables top/bottom paint; a multi-token value does not
- Verify: bare border-block:none disables top/bottom paint; a multi-token value does not
   - Expected: bare.border_t equals `0`
   - Expected: bare.border_b equals `0`
   - Expected: multi.border_t equals `4`
   - Expected: multi.border_b equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("bare border-block:none disables top/bottom paint; a multi-token value does not")
step("Verify: bare border-block:none disables top/bottom paint; a multi-token value does not")
# border_style_disables_paint matches only a BARE none/hidden value
val bare = ap("border:4px solid #112233;border-block:none")
expect(bare.border_t).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(bare.border_b).to_equal(0)  # oracle: 0 — named expected value from the requirement
val multi = ap("border-block:4px none #112233")
expect(multi.border_t).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(multi.border_b).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### border-inline shorthand sets left+right width, style and color

- border-inline shorthand sets left+right width, style and color
- Verify: border-inline shorthand sets left+right width, style and color
   - Expected: st.border_l equals `3`
   - Expected: st.border_r equals `3`
   - Expected: st.border_color_l equals `st.border_color_r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-inline shorthand sets left+right width, style and color")
step("Verify: border-inline shorthand sets left+right width, style and color")
val st = ap("border-inline:3px solid #112233")
expect(st.border_l).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_r).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_color_l).to_equal(st.border_color_r)
```

</details>

#### border-inline-start/end map to left/right and carry their style

- border-inline-start/end map to left/right and carry their style
- Verify: border-inline-start/end map to left/right and carry their style
   - Expected: st.border_l equals `1`
   - Expected: st.border_r equals `6`
   - Expected: st.border_color_l == st.border_color_r is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-inline-start/end map to left/right and carry their style")
step("Verify: border-inline-start/end map to left/right and carry their style")
val st = ap("border-inline-start:1px solid #ff0000;border-inline-end:6px solid #0000ff")
expect(st.border_l).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(st.border_r).to_equal(6)  # oracle: 6 — named expected value from the requirement
expect(st.border_color_l == st.border_color_r).to_equal(false)
```

</details>

#### border-inline-start with hidden style zeroes the left width

- border-inline-start with hidden style zeroes the left width
- Verify: border-inline-start with hidden style zeroes the left width
   - Expected: st.border_l equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-inline-start with hidden style zeroes the left width")
step("Verify: border-inline-start with hidden style zeroes the left width")
val st = ap("border-inline-start:7px hidden #ff0000")
expect(st.border_l).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### border-block-width and border-inline-width take two-value forms

- border-block-width and border-inline-width take two-value forms
- Verify: border-block-width and border-inline-width take two-value forms
   - Expected: st.border_t equals `1`
   - Expected: st.border_b equals `2`
   - Expected: st.border_l equals `3`
   - Expected: st.border_r equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block-width and border-inline-width take two-value forms")
step("Verify: border-block-width and border-inline-width take two-value forms")
val st = ap("border-block-width:1px 2px;border-inline-width:3px 4px;border-inline-style:solid")
expect(st.border_t).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(st.border_b).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.border_l).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(st.border_r).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### border-block-start/end-width single-side widths apply

- border-block-start/end-width single-side widths apply
- Verify: border-block-start/end-width single-side widths apply
   - Expected: st.border_t equals `9`
   - Expected: st.border_b equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block-start/end-width single-side widths apply")
step("Verify: border-block-start/end-width single-side widths apply")
val st = ap("border-block-start-width:9px;border-block-end-width:8px")
expect(st.border_t).to_equal(9)  # oracle: 9 — named expected value from the requirement
expect(st.border_b).to_equal(8)  # oracle: 8 — named expected value from the requirement
```

</details>

#### border-inline-start/end-width need a paintable inline style

- border-inline-start/end-width need a paintable inline style
- Verify: border-inline-start/end-width need a paintable inline style
   - Expected: st.border_l equals `5`
   - Expected: st.border_r equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-inline-start/end-width need a paintable inline style")
step("Verify: border-inline-start/end-width need a paintable inline style")
val st = ap("border-inline-style:solid;border-inline-start-width:5px;border-inline-end-width:6px")
expect(st.border_l).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(st.border_r).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### logical border colors mirror the physical color longhands

- logical border colors mirror the physical color longhands
- Verify: logical border colors mirror the physical color longhands
   - Expected: logical.border_color_t equals `phys.border_color_t`
   - Expected: logical.border_color_b equals `phys.border_color_b`
   - Expected: logical.border_color_l equals `phys.border_color_l`
   - Expected: logical.border_color_r equals `phys.border_color_r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("logical border colors mirror the physical color longhands")
step("Verify: logical border colors mirror the physical color longhands")
val phys = ap("border-top-color:#123456;border-bottom-color:#123456;border-left-color:#654321;border-right-color:#654321")
val logical = ap("border-block-color:#123456;border-inline-color:#654321")
expect(logical.border_color_t).to_equal(phys.border_color_t)
expect(logical.border_color_b).to_equal(phys.border_color_b)
expect(logical.border_color_l).to_equal(phys.border_color_l)
expect(logical.border_color_r).to_equal(phys.border_color_r)
```

</details>

#### border-block-start/end-color and border-inline-start/end-color set one side each

- border-block-start/end-color and border-inline-start/end-color set one side each
- Verify: border-block-start/end-color and border-inline-start/end-color set one side each
   - Expected: st.border_color_t == st.border_color_b is false
   - Expected: st.border_color_l == st.border_color_r is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block-start/end-color and border-inline-start/end-color set one side each")
step("Verify: border-block-start/end-color and border-inline-start/end-color set one side each")
val st = ap("border-block-start-color:#ff0000;border-block-end-color:#00ff00;border-inline-start-color:#0000ff;border-inline-end-color:#ffffff")
expect(st.border_color_t == st.border_color_b).to_equal(false)
expect(st.border_color_l == st.border_color_r).to_equal(false)
```

</details>

#### border-block-style and border-inline-style none disable their axes

- border-block-style and border-inline-style none disable their axes
- Verify: border-block-style and border-inline-style none disable their axes
   - Expected: st.border_t equals `0`
   - Expected: st.border_b equals `0`
   - Expected: st.border_l equals `0`
   - Expected: st.border_r equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block-style and border-inline-style none disable their axes")
step("Verify: border-block-style and border-inline-style none disable their axes")
val st = ap("border:3px solid #112233;border-block-style:none;border-inline-style:hidden")
expect(st.border_t).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_b).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_l).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_r).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### border-block-start-style/none zeroes only top; end-style only bottom

- border-block-start-style/none zeroes only top; end-style only bottom
- Verify: border-block-start-style/none zeroes only top; end-style only bottom
   - Expected: t.border_t equals `0`
   - Expected: t.border_b equals `2`
   - Expected: b.border_b equals `0`
   - Expected: b.border_t equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-block-start-style/none zeroes only top; end-style only bottom")
step("Verify: border-block-start-style/none zeroes only top; end-style only bottom")
val t = ap("border:2px solid #112233;border-block-start-style:none")
expect(t.border_t).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(t.border_b).to_equal(2)  # oracle: 2 — named expected value from the requirement
val b = ap("border:2px solid #112233;border-block-end-style:none")
expect(b.border_b).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.border_t).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### border-inline-start/end-style tokens land in the side style slots

- border-inline-start/end-style tokens land in the side style slots
- Verify: border-inline-start/end-style tokens land in the side style slots
   - Expected: st.border_l equals `2`
   - Expected: st.border_r equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-inline-start/end-style tokens land in the side style slots")
step("Verify: border-inline-start/end-style tokens land in the side style slots")
val st = ap("border:2px solid #112233;border-inline-start-style:dashed;border-inline-end-style:dotted")
expect(st.border_l).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(st.border_r).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### border-style shorthand none disables every side

- border-style shorthand none disables every side
- Verify: border-style shorthand none disables every side
   - Expected: st.border_w equals `0`
   - Expected: st.border_l equals `0`
   - Expected: st.border_t equals `0`
   - Expected: st.border_r equals `0`
   - Expected: st.border_b equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("border-style shorthand none disables every side")
step("Verify: border-style shorthand none disables every side")
val st = ap("border:3px solid #112233;border-style:none")
expect(st.border_w).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_l).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_t).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_r).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.border_b).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### decl_apply animation and transition shorthands (tranche 4)

#### animation shorthand decodes name, times, timing, count, direction, fill, play state

- animation shorthand decodes name, times, timing, count, direction, fill, play state
- Verify: animation shorthand decodes name, times, timing, count, direction, fill, play state
   - Expected: st.animation_name equals `spin`
   - Expected: st.animation_duration_ms equals `2000`
   - Expected: st.animation_delay_ms equals `500`
   - Expected: st.animation_timing_function equals `ease-in-out`
   - Expected: st.animation_iteration_count equals `3`
   - Expected: st.animation_direction equals `alternate`
   - Expected: st.animation_fill_mode equals `both`
   - Expected: st.animation_play_state equals `paused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("animation shorthand decodes name, times, timing, count, direction, fill, play state")
step("Verify: animation shorthand decodes name, times, timing, count, direction, fill, play state")
val st = ap("animation:spin 2s 500ms ease-in-out 3 alternate both paused")
expect(st.animation_name).to_equal("spin")
expect(st.animation_duration_ms).to_equal(2000)  # oracle: 2000 — named expected value from the requirement
expect(st.animation_delay_ms).to_equal(500)  # oracle: 500 — named expected value from the requirement
expect(st.animation_timing_function).to_equal("ease-in-out")
expect(st.animation_iteration_count).to_equal("3")
expect(st.animation_direction).to_equal("alternate")
expect(st.animation_fill_mode).to_equal("both")
expect(st.animation_play_state).to_equal("paused")
```

</details>

#### animation shorthand keyword defaults survive a minimal form

- animation shorthand keyword defaults survive a minimal form
- Verify: animation shorthand keyword defaults survive a minimal form
   - Expected: st.animation_name equals `fade`
   - Expected: st.animation_duration_ms equals `1000`
   - Expected: st.animation_delay_ms equals `0`
   - Expected: st.animation_direction equals `normal`
   - Expected: st.animation_play_state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("animation shorthand keyword defaults survive a minimal form")
step("Verify: animation shorthand keyword defaults survive a minimal form")
val st = ap("animation:fade 1s")
expect(st.animation_name).to_equal("fade")
expect(st.animation_duration_ms).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
expect(st.animation_delay_ms).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(st.animation_direction).to_equal("normal")
expect(st.animation_play_state).to_equal("running")
```

</details>

#### later animation longhands override the shorthand, earlier ones do not

- later animation longhands override the shorthand, earlier ones do not
- Verify: later animation longhands override the shorthand, earlier ones do not
   - Expected: late.animation_duration_ms equals `250`
   - Expected: late.animation_delay_ms equals `40`
   - Expected: late.animation_name equals `spin`
   - Expected: early.animation_duration_ms equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("later animation longhands override the shorthand, earlier ones do not")
step("Verify: later animation longhands override the shorthand, earlier ones do not")
val late = ap("animation:spin 2s;animation-duration:250ms;animation-delay:40ms")
expect(late.animation_duration_ms).to_equal(250)  # oracle: 250 — named expected value from the requirement
expect(late.animation_delay_ms).to_equal(40)  # oracle: 40 — named expected value from the requirement
expect(late.animation_name).to_equal("spin")
val early = ap("animation-duration:250ms;animation:spin 2s")
expect(early.animation_duration_ms).to_equal(2000)  # oracle: 2000 — named expected value from the requirement
```

</details>

#### animation-timing-function and iteration-count longhands after the shorthand win

- animation-timing-function and iteration-count longhands after the shorthand win
- Verify: animation-timing-function and iteration-count longhands after the shorthand win
   - Expected: st.animation_timing_function equals `ease-out`
   - Expected: st.animation_iteration_count equals `infinite`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("animation-timing-function and iteration-count longhands after the shorthand win")
step("Verify: animation-timing-function and iteration-count longhands after the shorthand win")
val st = ap("animation:spin 1s linear 2;animation-timing-function:ease-out;animation-iteration-count:infinite")
expect(st.animation_timing_function).to_equal("ease-out")
expect(st.animation_iteration_count).to_equal("infinite")
```

</details>

#### transition shorthand decodes property, duration, delay and timing

- transition shorthand decodes property, duration, delay and timing
- Verify: transition shorthand decodes property, duration, delay and timing
   - Expected: st.transition_property equals `opacity`
   - Expected: st.transition_duration_ms equals `300`
   - Expected: st.transition_delay_ms equals `100`
   - Expected: st.transition_timing_function equals `ease-in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("transition shorthand decodes property, duration, delay and timing")
step("Verify: transition shorthand decodes property, duration, delay and timing")
val st = ap("transition:opacity 300ms 100ms ease-in")
expect(st.transition_property).to_equal("opacity")
expect(st.transition_duration_ms).to_equal(300)  # oracle: 300 — named expected value from the requirement
expect(st.transition_delay_ms).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(st.transition_timing_function).to_equal("ease-in")
```

</details>

#### later transition longhands override the shorthand

- later transition longhands override the shorthand
- Verify: later transition longhands override the shorthand
   - Expected: st.transition_duration_ms equals `50`
   - Expected: st.transition_delay_ms equals `5`
   - Expected: st.transition_timing_function equals `linear`
   - Expected: st.transition_property equals `opacity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("later transition longhands override the shorthand")
step("Verify: later transition longhands override the shorthand")
val st = ap("transition:opacity 300ms;transition-duration:50ms;transition-timing-function:linear;transition-delay:5ms")
expect(st.transition_duration_ms).to_equal(50)  # oracle: 50 — named expected value from the requirement
expect(st.transition_delay_ms).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(st.transition_timing_function).to_equal("linear")
expect(st.transition_property).to_equal("opacity")
```

</details>

### decl_apply ordering and rejection

#### last declaration wins within one block

- last declaration wins within one block
- Verify: last declaration wins within one block
   - Expected: st.width_px equals `90`
   - Expected: st.fg equals `green.fg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("last declaration wins within one block")
step("Verify: last declaration wins within one block")
val st = ap("width:10px;width:90px;color:#ff0000;color:#00ff00")
expect(st.width_px).to_equal(90)  # oracle: 90 — named expected value from the requirement
val green = ap("color:#00ff00")
expect(st.fg).to_equal(green.fg)
```

</details>

#### an unparseable last width parses to 0 (last-wins, no CSS-style rollback)

- an unparseable last width parses to 0 (last-wins, no CSS-style rollback)
- Verify: an unparseable last width parses to 0 (last-wins, no CSS-style rollback)
   - Expected: st.width_px equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("an unparseable last width parses to 0 (last-wins, no CSS-style rollback)")
step("Verify: an unparseable last width parses to 0 (last-wins, no CSS-style rollback)")
# CSS would keep 50px; this applier is last-declaration-wins on the raw
# value, so 'banana' parses to 0. Documented current behavior.
val st = ap("width:50px;width:banana")
expect(st.width_px).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### unknown property names are ignored without disturbing neighbors

- unknown property names are ignored without disturbing neighbors
- Verify: unknown property names are ignored without disturbing neighbors
   - Expected: st.height_px equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("unknown property names are ignored without disturbing neighbors")
step("Verify: unknown property names are ignored without disturbing neighbors")
val st = ap("not-a-prop:12;height:33px")
expect(st.height_px).to_equal(33)  # oracle: 33 — named expected value from the requirement
```

</details>

#### whitespace and trailing semicolons are tolerated

- whitespace and trailing semicolons are tolerated
- Verify: whitespace and trailing semicolons are tolerated
   - Expected: st.width_px equals `25`
   - Expected: st.height_px equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("whitespace and trailing semicolons are tolerated")
step("Verify: whitespace and trailing semicolons are tolerated")
val st = ap("  width : 25px ;; height:14px ; ")
expect(st.width_px).to_equal(25)  # oracle: 25 — named expected value from the requirement
expect(st.height_px).to_equal(14)  # oracle: 14 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 68 |
| Active scenarios | 68 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-SIMPLE-WEB-HTML-LAYOUT-RENDERER-DECL-APPLY-COVERAGE-CLOSURE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b320f3b238524118c7ed37ff17d6e7e2c527360e1e664108857cdb8277267bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b320f3b238524118c7ed37ff17d6e7e2c527360e1e664108857cdb8277267bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b320f3b238524118c7ed37ff17d6e7e2c527360e1e664108857cdb8277267bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty declaration block returns the style unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a rule over the per-rule declaration quota is dropped wholesale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies width/height/min/max in px' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
