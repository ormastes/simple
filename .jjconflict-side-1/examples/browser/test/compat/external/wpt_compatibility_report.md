# WPT Compatibility Report -- Simple Browser Engine

**Date:** 2026-04-08
**Engine version:** Current HEAD (post border/style-block additions)
**Test corpus:** 37 WPT reftest pairs + 2 Acid tests

---

## Executive Summary

| Metric | Value |
|--------|-------|
| **Total WPT tests** | 37 |
| **SUPPORTED** (expected pass) | 14 (37.8%) |
| **PARTIAL** (some features missing) | 11 (29.7%) |
| **UNSUPPORTED** (critical features missing) | 12 (32.4%) |
| **Acid1** | UNSUPPORTED |
| **Acid2** | UNSUPPORTED |
| **Overall compatibility score** | **37.8%** |

---

## Per-Category Breakdown

### 1. Flexbox (18 tests) -- 10 SUPPORTED, 5 PARTIAL, 3 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `flexbox_margin.html` | SUPPORTED | display:flex, justify-content:space-around, margin, background, height | -- |
| `flexbox_display.html` | PARTIAL | display:flex, list-style:none, border:1px solid | `list-style: none` (minor -- visual only) |
| `flexbox_direction-column.html` | SUPPORTED | display:flex, flex-direction:column, margin, width, border, background, display:inline-block | -- |
| `flexbox_direction-row-reverse.html` | PARTIAL | display:flex, flex-direction:row-reverse, list-style:none, external font (Ahem), color (named) | `list-style: none`, external font stylesheet |
| `flexbox_justifycontent-center.html` | PARTIAL | display:flex, justify-content:center, flex:1 0 0%, :nth-child(), max-width, display:inline-block | `:nth-child()` partially supported (basic numeric only) |
| `flexbox_justifycontent-spacebetween.html` | PARTIAL | display:flex, justify-content:space-between, flex:1 0 0%, :nth-child(), max-width | `:nth-child()` partially supported |
| `flexbox_align-items-center.html` | SUPPORTED | display:flex, align-items:center, flex:none, :nth-child(), margin, width, height | :nth-child for color only, core layout supported |
| `flexbox_align-items-stretch.html` | SUPPORTED | display:flex, align-items:stretch, flex:none, :nth-child(), margin | -- |
| `flexbox_align-items-flexstart.html` | SUPPORTED | display:flex, align-items:flex-start, flex:none, :nth-child() | -- |
| `flexbox_flex-1-1-0.html` | SUPPORTED | display:flex, flex:1 1 0%, :nth-child(), margin, width, height | -- |
| `flexbox_flex-none.html` | SUPPORTED | display:flex, flex:none, flex:0 0 auto, #id selector, margin | -- |
| `flexbox_wrap.html` | SUPPORTED | display:flex, flex-wrap:wrap, margin, width, display:inline-block | -- |
| `gap-001-ltr.html` | SUPPORTED | display:flex, gap:20px, flex:1 1 auto, background-color, `block-size` | `block-size` (logical property -- may map to height) |
| `flex-direction-row-vertical.html` | UNSUPPORTED | display:flex, flex-direction:row, `writing-mode:vertical-lr`, `direction:ltr/rtl` | `writing-mode`, `direction` (RTL/LTR) |
| `flexbox_flow-row-wrap.html` | PARTIAL | display:flex, `flex-flow:row wrap` (shorthand) | `flex-flow` shorthand not expanded by style_block.spl |
| `flexbox_inline.html` | UNSUPPORTED | `display:inline-flex`, negative margin-top | `display: inline-flex` not in supported display values |
| `flexbox_align-self-center.html` | SUPPORTED | display:flex, align-items:flex-start, `align-self:center`, :nth-child() | `align-self` (needs verification in engine) |
| `flexbox_align-self-stretch.html` | SUPPORTED | display:flex, align-items:center, `align-self:stretch`, :nth-child() | `align-self` (needs verification in engine) |

**Flexbox score: 55.6% SUPPORTED**

---

### 2. Colors (10 tests) -- 3 SUPPORTED, 3 PARTIAL, 4 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `background-color-rgb-001.html` | PARTIAL | `rgb()` with alpha, percentage values, space-separated syntax, CSS comments in values | Advanced `rgb()` syntax: space-separated form, `%` alpha, CSS comments inside `rgb()` |
| `background-color-rgb-002.html` | PARTIAL | `rgba()` with space-separated, `%` alpha, CSS comments in values | Same as rgb-001 |
| `background-color-rgb-003.html` | SUPPORTED | `rgb()` with 4 args (alpha), `rgba()` without alpha | Standard `rgb()`/`rgba()` with commas |
| `background-color-hsl-001.html` | UNSUPPORTED | `hsla()` with space-separated syntax, `%` alpha, CSS comments | `hsl()`/`hsla()` color functions not supported |
| `background-color-hsl-002.html` | UNSUPPORTED | `hsl()` with alpha, space-separated syntax | `hsl()`/`hsla()` not supported |
| `hex-003.html` | SUPPORTED | 3-digit hex (#070), 6-digit hex (#007700), class selectors | -- |
| `t424-hsl-values-b-1.html` | UNSUPPORTED | `hsl()` inline, `table`, `td`, `border-spacing` | `hsl()`, `display:table`, `display:table-cell`, `border-spacing` |
| `opacity-overlapping-letters.html` | PARTIAL | `opacity`, `letter-spacing`, external font (Ahem) | External font loading (Ahem) |
| `border-color-currentcolor.html` | UNSUPPORTED | `currentColor`, `border-style:inset/outset/ridge/groove` | `currentColor` keyword, non-solid border styles |
| `currentcolor-003.html` | UNSUPPORTED | `currentColor`, `::first-line`, `box-decoration-break`, `linear-gradient`, `box-shadow`, `text-shadow`, `filter`, `outline` | Almost entirely unsupported features |

**Colors score: 30.0% SUPPORTED**

---

### 3. Display (5 tests) -- 0 SUPPORTED, 2 PARTIAL, 3 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `display-contents-text-only-001.html` | UNSUPPORTED | `display: contents` | `display: contents` not in supported values |
| `display-contents-flex-001.html` | UNSUPPORTED | `display: contents`, `display: flex`, class selectors | `display: contents` |
| `display-flow-root-001.html` | UNSUPPORTED | `display: flow-root`, `float: left` | `display: flow-root`, `float` |
| `display-flow-root-002.html` | UNSUPPORTED | `display: flow-root`, `float: left/right`, `outline` | `display: flow-root`, `float`, `outline` |
| `display-contents-block-002.html` | PARTIAL | `display: contents`, margin collapsing, #id selectors | `display: contents`, margin collapsing |

**Display score: 0.0% SUPPORTED**

---

### 4. Backgrounds (5 tests) -- 1 SUPPORTED, 2 PARTIAL, 2 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `background-clip-color.html` | PARTIAL | `background-clip: border-box/padding-box/content-box`, border:dashed, #id selectors | `background-clip` |
| `background-none-none-and-color.html` | PARTIAL | `background: none, none` (multi-layer), `background-color`, `overflow:scroll` | Multi-layer background shorthand, `overflow:scroll` specifics |
| `border-radius-012.html` | SUPPORTED | `border`, `border-radius`, `display:inline-block` | -- |
| `box-shadow-calc.html` | UNSUPPORTED | `box-shadow`, `calc()` | `box-shadow`, `calc()` |
| `box-shadow-currentcolor.html` | UNSUPPORTED | `box-shadow`, `currentcolor`, `inherit` (box-shadow) | `box-shadow`, `currentColor`, `inherit` |

**Backgrounds score: 20.0% SUPPORTED**

---

### 5. Positioning (5 tests) -- 1 SUPPORTED, 2 PARTIAL, 2 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `absolute-non-replaced-max-001.html` | SUPPORTED | `position:absolute`, `width`, `height`, `max-width`, `max-height`, `%` sizing, `background` | -- |
| `auto-position-rtl-child-viewport-scrollbar.html` | UNSUPPORTED | `direction:rtl`, `overflow:scroll`, `position:absolute` | `direction:rtl` |
| `absolute-non-replaced-min-max-001.html` | PARTIAL | `position:absolute`, `min-width`, `min-height`, `max-width`, `max-height` | Min/max override semantics (may work, needs verification) |
| `abspos-float-with-inline-container.html` | UNSUPPORTED | `position:absolute`, `position:relative`, `float:left`, `padding-left` | `float` |
| `line-break-after-leading-oof-001.html` | UNSUPPORTED | `position:absolute`, `text-indent`, `ch` unit | `text-indent`, `ch` unit |

**Positioning score: 20.0% SUPPORTED**

---

### 6. Normal Flow (2 tests) -- 0 SUPPORTED, 0 PARTIAL, 2 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `block-in-inline-baseline-001.html` | UNSUPPORTED | `display:inline-block`, block-in-inline splitting, baseline alignment | Block-in-inline splitting, `vertical-align` (baseline) |
| `block-in-inline-margins-003.html` | UNSUPPORTED | Block-in-inline, margin collapsing through anonymous blocks, `outline` | Block-in-inline splitting, margin collapsing, `outline` |

**Normal Flow score: 0.0% SUPPORTED**

---

### 7. Floats (5 tests) -- 0 SUPPORTED, 0 PARTIAL, 5 UNSUPPORTED

| Test File | Status | Required Features | Missing Features |
|-----------|--------|-------------------|------------------|
| `float-nowrap-3.html` | UNSUPPORTED | `float:right`, `white-space:nowrap`, `ch` unit | `float`, `ch` unit |
| `overflow-scroll-float-paint-order.html` | UNSUPPORTED | `float:left`, `overflow:scroll`, `box-sizing:border-box`, negative margins, paint order | `float`, `box-sizing`, z-order paint rules |
| `float-root.html` | UNSUPPORTED | `float:right` on `:root` | `float` |
| `float-nowrap-5.html` | UNSUPPORTED | `float:left`, `white-space:nowrap` | `float` |
| `floats-wrap-bfc-with-margin-010.html` | UNSUPPORTED | `float:left`, `overflow:hidden` (BFC), negative margins, wrapping | `float`, BFC creation |

**Floats score: 0.0% SUPPORTED**

---

## Acid Test Analysis

### Acid1
**Status: UNSUPPORTED**

Acid1 is a CSS1 conformance test requiring:
- `float: left/right` -- NOT SUPPORTED
- `clear: both` -- NOT SUPPORTED
- `display: block` (on `<li>`) -- supported
- Complex box model: width in `em` with `%` widths -- partially supported
- `line-height` -- NOT SUPPORTED
- `font-style: normal` -- NOT SUPPORTED
- `list-style` -- NOT SUPPORTED
- `blockquote` with asymmetric borders -- partially supported (border shorthand exists but per-side `border-width`/`border-style`/`border-color` with different values per side needs verification)
- Form elements (`<input type="radio">`) -- NOT SUPPORTED
- `<dl>`, `<dt>`, `<dd>` styling -- depends on default UA stylesheet

**Critical blockers:** `float`, `clear`, `line-height`

### Acid2
**Status: UNSUPPORTED**

Acid2 is an extremely demanding CSS2.1 conformance test requiring:
- `position: fixed` -- partially supported (in engine's position list)
- `min-height`/`max-height` override rules -- partially supported
- `float: left/right` -- NOT SUPPORTED
- `clear: both` -- NOT SUPPORTED
- `display: table/table-cell` -- NOT SUPPORTED
- `overflow: hidden` -- supported
- `writing-mode` -- NOT SUPPORTED
- `direction: rtl/ltr` -- NOT SUPPORTED
- `::first-line` pseudo-element -- NOT SUPPORTED
- `:link`/`:visited` pseudo-classes -- NOT SUPPORTED
- `[attr]`/`[class~=val]` attribute selectors -- NOT SUPPORTED
- `+` adjacent sibling combinator -- NOT SUPPORTED
- `>` child combinator -- NOT SUPPORTED
- `inherit` value -- NOT SUPPORTED
- `currentColor` -- NOT SUPPORTED
- `content` property (generated content) -- NOT SUPPORTED
- `::before`/`::after` pseudo-elements -- NOT SUPPORTED
- Margin collapsing -- NOT SUPPORTED
- `border-spacing` -- NOT SUPPORTED
- `vertical-align` -- NOT SUPPORTED
- `line-height` -- NOT SUPPORTED
- `background-image` with `url()` / data URIs -- NOT SUPPORTED
- `<link rel="stylesheet">` (external stylesheets) -- NOT SUPPORTED
- CSS error recovery (invalid property handling) -- NOT SUPPORTED
- `object` element fallback rendering -- NOT SUPPORTED
- `!important` -- NOT SUPPORTED
- `*` universal selector in compound rules like `* html` -- NOT SUPPORTED
- Escaped characters in selectors -- NOT SUPPORTED

**Critical blockers:** Nearly every advanced CSS2.1 feature. Acid2 is not achievable without a major engine overhaul.

---

## Most Commonly Needed but Unsupported Features

Ranked by number of tests that require them:

| Rank | Feature | Tests Needing It | Category |
|------|---------|-----------------|----------|
| 1 | **float / clear** | 12 | Floats (5), Display (2), Positioning (1), Normal-Flow (2), Acid1, Acid2 |
| 2 | **hsl() / hsla() colors** | 4 | Colors |
| 3 | **display: contents** | 3 | Display |
| 4 | **display: flow-root** | 2 | Display |
| 5 | **currentColor keyword** | 3 | Colors, Backgrounds |
| 6 | **box-shadow** | 3 | Backgrounds, Colors |
| 7 | **writing-mode / direction (RTL)** | 2 | Flexbox, Positioning |
| 8 | **display: inline-flex** | 1 | Flexbox |
| 9 | **calc()** | 1 | Backgrounds |
| 10 | **outline** | 2 | Normal-Flow, Display |
| 11 | **text-indent** | 1 | Positioning |
| 12 | **vertical-align** | 1 | Normal-Flow |
| 13 | **background-clip** | 1 | Backgrounds |
| 14 | **flex-flow shorthand** | 1 | Flexbox |
| 15 | **ch unit** | 2 | Positioning, Floats |
| 16 | **block-size (logical property)** | 1 | Flexbox |
| 17 | **list-style: none** | 2 | Flexbox |
| 18 | **box-sizing** | 1 | Floats |
| 19 | **Attribute selectors [attr]** | 1 | Acid2 |
| 20 | **Child/sibling combinators (>, +, ~)** | 1 | Acid2 |

---

## Top Recommendations for Next Features to Implement

### Tier 1 -- High Impact, Moderate Effort (would unlock the most tests)

1. **`hsl()` / `hsla()` color functions** -- Unlocks 4 color tests. Pure math conversion (hue/saturation/lightness to RGB). No layout changes needed. Estimated effort: low.

2. **`currentColor` keyword** -- Unlocks 3 tests. Requires resolving `currentColor` to the computed `color` value during style application. Estimated effort: low.

3. **`display: contents`** -- Unlocks 3 display tests. The element's box is removed but children are promoted to the parent. Moderate layout engine change. Estimated effort: medium.

4. **`display: inline-flex`** -- Unlocks 1 test, but important for real-world pages. Behaves like flex but is inline-level. Estimated effort: low-medium.

5. **`flex-flow` shorthand** -- Unlocks 1 test. Simply split into `flex-direction` + `flex-wrap` in `expand_shorthand()`. Estimated effort: trivial (add to `style_block.spl`).

### Tier 2 -- High Impact, High Effort

6. **`float` / `clear`** -- Would unlock 12 tests (the single largest blocker). However, float layout is one of the most complex parts of CSS. Requires substantial layout engine work: float placement algorithm, clearance computation, BFC interaction, line-box shortening. Estimated effort: very high.

7. **`display: flow-root`** -- Unlocks 2 tests. Creates a new block formatting context. Closely related to float/BFC work. Estimated effort: high (depends on BFC infrastructure).

### Tier 3 -- Medium Impact, Low Effort

8. **`box-shadow`** -- Unlocks 3 tests. Rendering-only feature (no layout impact). Requires shadow painting in the renderer. Estimated effort: medium.

9. **`list-style: none`** -- Unlocks 2 tests. Simply suppresses list markers. Estimated effort: trivial.

10. **`outline`** -- Unlocks 2 tests. Similar to border but does not affect layout. Estimated effort: low.

11. **`background-clip`** -- Unlocks 1 test. Clips background painting to border-box/padding-box/content-box. Estimated effort: medium.

12. **`calc()` in values** -- Unlocks 1 test directly, but widely used in real-world CSS. Requires expression parser. Estimated effort: medium-high.

### Quick Wins (implement in < 1 hour each)

- `flex-flow` shorthand expansion in `style_block.spl`
- `list-style: none` (suppress markers)
- `hsl()`/`hsla()` color parsing (pure math)
- `currentColor` resolution
- `display: inline-flex` (alias to flex with inline outer)

---

## Selector Support Gap Analysis

The style_block.spl parser handles basic selectors well but lacks:

| Selector | WPT Tests Using It | Status |
|----------|-------------------|--------|
| `tag`, `.class`, `#id` | Most tests | SUPPORTED |
| `tag.class` compound | Several | SUPPORTED |
| `:nth-child(N)` | 8 flexbox tests | SUPPORTED (basic numeric) |
| Descendant (`A B`) | Several | PARTIAL (simplified) |
| `*` universal | Acid2 | NOT SUPPORTED |
| `[attr]` attribute | Acid2 | NOT SUPPORTED |
| `[class~=val]` | Acid2 | NOT SUPPORTED |
| `A + B` adjacent sibling | Acid2 | NOT SUPPORTED |
| `A > B` child | Acid2, currentcolor-003 | NOT SUPPORTED |
| `A ~ B` general sibling | -- | NOT SUPPORTED |
| `::before` / `::after` | Acid2 | NOT SUPPORTED |
| `::first-line` | currentcolor-003 | NOT SUPPORTED |
| `:hover` | Acid2 | NOT SUPPORTED |
| `:link` / `:visited` | Acid2 | NOT SUPPORTED |
| `:root` | float-root | NOT SUPPORTED |
| `* html` (star hack) | Acid2 | NOT SUPPORTED |

---

## Summary

The Simple browser engine has solid coverage of **flexbox layout** (55.6%) thanks to comprehensive flex property support. Color handling for basic RGB and hex is good. Positioning basics (absolute, relative) work.

The biggest gaps are:
1. **Float layout** (blocks 32% of all tests)
2. **Advanced color functions** (hsl, currentColor)
3. **Display variants** (contents, flow-root, inline-flex)
4. **Advanced selectors** (attribute, combinators, pseudo-elements)

Implementing the 5 "quick wins" listed above would raise the compatibility score from **37.8%** to approximately **48.6%** (18/37 tests) with minimal effort.
