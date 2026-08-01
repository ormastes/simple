# CSS Box Shadow Rendering

> Proves admitted outer, multi-outer, and single-inset box shadows through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Box Shadow Rendering

Proves admitted outer, multi-outer, and single-inset box shadows through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves admitted outer, multi-outer, and single-inset box shadows through the
existing web semantic/layout owner, Draw IR metadata, and Engine2D pixels.
Mixed inset/outer stacks, multiple inset layers, and full filter-equivalent
blur remain outside this bounded profile.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS box-shadow lowering

#### should paint an offset outer shadow behind the border box

- Resolve the shadowed box in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
- Read exact outer-shadow ordering pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: pixels[10 + 4 * WIDTH] equals `0xFF16A34Au32`
   - Expected: pixels[2 + 2 * WIDTH] equals `0xFFFFFFFFu32`
   - Expected: pixels[14 + 2 * WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = "4px 3px 0 #16a34a"
val html = _shadow_html(shadow, "#111827")

step("Resolve the shadowed box in canonical web semantic and layout state")
_expect_web_layout(html)

step("Render HTML and CSS through canonical Draw IR")
val composition = _shadow_composition(html)
_draw_ir_panel(composition, shadow, "1")

step("Read exact outer-shadow ordering pixels through Engine2D")
val pixels = _pixels(html, composition)
expect(pixels[10 + 4 * WIDTH]).to_equal(0xFF16A34Au32)
expect(pixels[2 + 2 * WIDTH]).to_equal(0xFFFFFFFFu32)
expect(pixels[14 + 2 * WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

#### should preserve blur and spread length order

- Resolve blur and spread boxes in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact blur and spread coverage pixels through Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blur_shadow = "0px 0px 2px #dc2626"
val spread_shadow = "0px 0px 0px 2px #2563eb"
val blur_html = _shadow_html(blur_shadow, "#111827")
val spread_html = _shadow_html(spread_shadow, "#111827")

step("Resolve blur and spread boxes in canonical web semantic and layout state")
_expect_web_layout(blur_html)
_expect_web_layout(spread_html)

step("Render HTML and CSS through canonical Draw IR")
val blur_composition = _shadow_composition(blur_html)
val spread_composition = _shadow_composition(spread_html)
val blur_panel = _draw_ir_panel(
    blur_composition, blur_shadow, "1"
)
val spread_panel = _draw_ir_panel(
    spread_composition, spread_shadow, "1"
)
expect(_style_value(
    blur_panel, "box-shadow-blur-radius"
)).to_equal("2")
expect(_style_value(
    spread_panel, "box-shadow-blur-radius"
)).to_equal("0")

step("Read exact blur and spread coverage pixels through Engine2D")
expect(_pixels(
    blur_html, blur_composition
)[9 + WIDTH]).to_equal(0xFFDC2626u32)
expect(_pixels(
    spread_html, spread_composition
)[9 + WIDTH]).to_equal(0xFF2563EBu32)
```

</details>

#### should resolve admitted shadow color syntaxes before Draw IR

- Resolve color-bearing boxes in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
- Read exact resolved shadow colors through Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rgb_shadow = "0px 0px 0px 2px rgb(37, 99, 235)"
val rgba_shadow = "0px 0px 0px 2px rgba(37, 99, 235, 0.5)"
val named_shadow = "0px 0px 0px 2px rebeccapurple"
val hsl_shadow = "0px 0px 0px 2px hsl(120, 100%, 50%)"
val current_shadow = "0px 0px 0px 2px currentColor"
val rgb_html = _shadow_html(rgb_shadow, "#111827")
val rgba_html = _shadow_html(rgba_shadow, "#111827")
val named_html = _shadow_html(named_shadow, "#111827")
val hsl_html = _shadow_html(hsl_shadow, "#111827")
val current_html = _shadow_html(current_shadow, "#db2777")

step("Resolve color-bearing boxes in canonical web semantic and layout state")
_expect_web_layout(rgb_html)
_expect_web_layout(rgba_html)
_expect_web_layout(named_html)
_expect_web_layout(hsl_html)
_expect_web_layout(current_html)

step("Render HTML and CSS through canonical Draw IR")
val rgb_composition = _shadow_composition(rgb_html)
val rgba_composition = _shadow_composition(rgba_html)
val named_composition = _shadow_composition(named_html)
val hsl_composition = _shadow_composition(hsl_html)
val current_composition = _shadow_composition(current_html)
_draw_ir_panel(rgb_composition, rgb_shadow, "1")
_draw_ir_panel(rgba_composition, rgba_shadow, "1")
_draw_ir_panel(named_composition, named_shadow, "1")
_draw_ir_panel(hsl_composition, hsl_shadow, "1")
_draw_ir_panel(current_composition, current_shadow, "1")

step("Read exact resolved shadow colors through Engine2D")
expect(_pixels(
    rgb_html, rgb_composition
)[9 + WIDTH]).to_equal(0xFF2563EBu32)
expect(_pixels(
    rgba_html, rgba_composition
)[9 + WIDTH]).to_equal(0xFF92B1F5u32)
expect(_pixels(
    named_html, named_composition
)[9 + WIDTH]).to_equal(0xFF663399u32)
expect(_pixels(
    hsl_html, hsl_composition
)[9 + WIDTH]).to_equal(0xFF00FF00u32)
expect(_pixels(
    current_html, current_composition
)[9 + WIDTH]).to_equal(0xFFDB2777u32)
```

</details>

#### should paint both admitted outer shadow layers

- Resolve the layered shadow box in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
- Read one exact pixel from each shadow layer through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: pixels[10 + WIDTH] equals `0xFFDC2626u32`
   - Expected: pixels[1 + 8 * WIDTH] equals `0xFF2563EBu32`
   - Expected: pixels[2 + 2 * WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = (
    "4px 0px 0px #dc2626, 0px 4px 0px #2563eb"
)
val html = _shadow_html(shadow, "#111827")

step("Resolve the layered shadow box in canonical web semantic and layout state")
_expect_web_layout(html)

step("Render HTML and CSS through canonical Draw IR")
val composition = _shadow_composition(html)
_draw_ir_panel(composition, shadow, "2")

step("Read one exact pixel from each shadow layer through Engine2D")
val pixels = _pixels(html, composition)
expect(pixels[10 + WIDTH]).to_equal(0xFFDC2626u32)
expect(pixels[1 + 8 * WIDTH]).to_equal(0xFF2563EBu32)
expect(pixels[2 + 2 * WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

#### should paint a single inset shadow before the center fill

- Resolve the inset shadow box in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
-  draw ir panel
   - Artifact capture: after_step
- Read exact inset-edge and center pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: pixels[1] equals `0xFF16A34Au32`
   - Expected: pixels[4 + 3 * WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shadow = "inset 0px 0px 0px 2px #16a34a"
val html = _shadow_html(shadow, "#111827")

step("Resolve the inset shadow box in canonical web semantic and layout state")
_expect_web_layout(html)

step("Render HTML and CSS through canonical Draw IR")
val composition = _shadow_composition(html)
_draw_ir_panel(composition, shadow, "1")

step("Read exact inset-edge and center pixels through Engine2D")
val pixels = _pixels(html, composition)
expect(pixels[1]).to_equal(0xFF16A34Au32)
expect(pixels[4 + 3 * WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
