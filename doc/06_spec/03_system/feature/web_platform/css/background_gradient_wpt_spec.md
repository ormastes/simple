# CSS Linear Gradient Rendering

> Proves the admitted two-stop vertical and horizontal linear-gradient slice

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Linear Gradient Rendering

Proves the admitted two-stop vertical and horizontal linear-gradient slice

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the admitted two-stop vertical and horizontal linear-gradient slice
through canonical web semantic/layout state, Draw IR, and Engine2D pixels.
Radial, conic, and multi-gradient stacks remain explicit fail-closed RED rows.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS gradient lowering

#### should lower a vertical two-stop linear gradient

- "linear-gradient
   - Artifact capture: after_step
- Resolve linear-gradient stops in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: _style_value(panel, "background-layers-raw") equals ``
- Read exact vertical endpoint pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: pixels[1] equals `0xFFDC2626u32`
   - Expected: pixels[1 + 5 * WIDTH] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _gradient_html(
    "linear-gradient(180deg,#dc2626,#2563eb)"
)

step("Resolve linear-gradient stops in canonical web semantic and layout state")
_expect_web_layout(html)
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_gradient_from"
)).to_equal("4292617766")
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_gradient_to"
)).to_equal("4280640491")

step("Render HTML and CSS through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(
    html, WIDTH, HEIGHT
)
val panel = _draw_ir_panel(composition)
expect(_style_value(
    panel, "background-image"
)).to_equal("linear-gradient(4292617766,4280640491)")
expect(_style_value(panel, "background-layers-raw")).to_equal("")

step("Read exact vertical endpoint pixels through Engine2D")
val pixels = _gradient_pixels(html, composition)
expect(pixels[1]).to_equal(0xFFDC2626u32)
expect(pixels[1 + 5 * WIDTH]).to_equal(0xFF2563EBu32)
```

</details>

#### should lower a horizontal two-stop linear gradient

- "linear-gradient
   - Artifact capture: after_step
- Resolve horizontal stops in canonical web semantic and layout state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: _style_value(panel, "background-layers-raw") equals ``
- Read exact horizontal endpoint pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: pixels[WIDTH] equals `0xFFDC2626u32`
   - Expected: pixels[7 + WIDTH] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _gradient_html(
    "linear-gradient(90deg,#dc2626,#2563eb)"
)

step("Resolve horizontal stops in canonical web semantic and layout state")
_expect_web_layout(html)
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_gradient_from"
)).to_equal("4292617766")
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_gradient_to"
)).to_equal("4280640491")

step("Render HTML and CSS through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(
    html, WIDTH, HEIGHT
)
val panel = _draw_ir_panel(composition)
expect(_style_value(
    panel, "background-image"
)).to_equal("linear-gradient(4292617766,4280640491)")
expect(_style_value(panel, "background-layers-raw")).to_equal("")

step("Read exact horizontal endpoint pixels through Engine2D")
val pixels = _gradient_pixels(html, composition)
expect(pixels[WIDTH]).to_equal(0xFFDC2626u32)
expect(pixels[7 + WIDTH]).to_equal(0xFF2563EBu32)
```

</details>

#### should keep radial conic and stacked gradients fail closed

- "radial-gradient
   - Artifact capture: after_step
- "conic-gradient
   - Artifact capture: after_step
- "linear-gradient
   - Artifact capture: after_step
- "linear-gradient
   - Artifact capture: after_step
- Preserve unsupported gradient syntax in canonical web semantic state
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
-  expect web layout
   - Artifact capture: after_step
- "linear-gradient
   - Artifact capture: after_step
- "linear-gradient
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- "linear-gradient
   - Artifact capture: after_step
- "linear-gradient
   - Artifact capture: after_step
- Read exact solid fallback pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: radial_pixels[1 + WIDTH] equals `0xFFFFFFFFu32`
   - Expected: conic_pixels[1 + WIDTH] equals `0xFFFFFFFFu32`
   - Expected: stacked_pixels[1 + WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val radial = _gradient_html(
    "radial-gradient(#dc2626,#2563eb)"
)
val conic = _gradient_html(
    "conic-gradient(#dc2626,#2563eb)"
)
val stacked = _gradient_html(
    "linear-gradient(#dc2626,#2563eb)," +
    "linear-gradient(#16a34a,#9333ea)"
)

step("Preserve unsupported gradient syntax in canonical web semantic state")
_expect_web_layout(radial)
_expect_web_layout(conic)
_expect_web_layout(stacked)
expect(simple_web_layout_debug_style_by_id(
    radial, "panel", "background_layers_raw"
)).to_equal("radial-gradient(#dc2626,#2563eb)")
expect(simple_web_layout_debug_style_by_id(
    conic, "panel", "background_layers_raw"
)).to_equal("conic-gradient(#dc2626,#2563eb)")
expect(simple_web_layout_debug_style_by_id(
    stacked, "panel", "background_layers_raw"
)).to_equal(
    "linear-gradient(#dc2626,#2563eb)," +
    "linear-gradient(#16a34a,#9333ea)"
)

step("Render HTML and CSS through canonical Draw IR")
val radial_composition = simple_web_layout_render_html_draw_ir(
    radial, WIDTH, HEIGHT
)
val conic_composition = simple_web_layout_render_html_draw_ir(
    conic, WIDTH, HEIGHT
)
val stacked_composition = simple_web_layout_render_html_draw_ir(
    stacked, WIDTH, HEIGHT
)
val radial_panel = _draw_ir_panel(radial_composition)
val conic_panel = _draw_ir_panel(conic_composition)
val stacked_panel = _draw_ir_panel(stacked_composition)
expect(_style_value(
    radial_panel, "background-image"
)).to_equal("none")
expect(_style_value(
    conic_panel, "background-image"
)).to_equal("none")
expect(_style_value(
    stacked_panel, "background-image"
)).to_equal("none")
expect(_style_value(
    radial_panel, "background-layers-raw"
)).to_equal("radial-gradient(#dc2626,#2563eb)")
expect(_style_value(
    conic_panel, "background-layers-raw"
)).to_equal("conic-gradient(#dc2626,#2563eb)")
expect(_style_value(
    stacked_panel, "background-layers-raw"
)).to_equal(
    "linear-gradient(#dc2626,#2563eb)," +
    "linear-gradient(#16a34a,#9333ea)"
)

step("Read exact solid fallback pixels through Engine2D")
val radial_pixels = _gradient_pixels(radial, radial_composition)
val conic_pixels = _gradient_pixels(conic, conic_composition)
val stacked_pixels = _gradient_pixels(stacked, stacked_composition)
expect(radial_pixels[1 + WIDTH]).to_equal(0xFFFFFFFFu32)
expect(conic_pixels[1 + WIDTH]).to_equal(0xFFFFFFFFu32)
expect(stacked_pixels[1 + WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
