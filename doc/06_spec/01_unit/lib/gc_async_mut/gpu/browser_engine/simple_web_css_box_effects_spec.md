# Simple Web CSS Box Effects Specification

> Executable source: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl`

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 7 | 7 | 0 | 0 |

## Requirement mapping

| Requirement | Evidence |
|---|---|
| REQ-WEB-BROWSER-003 | CSS declaration parsing and cascade retain the later `outline-offset`. |
| REQ-WEB-BROWSER-004 | The computed outline fields are emitted on the card Draw IR command. |
| REQ-WEB-BROWSER-021 | The canonical CPU Draw IR executor paints the declared outline. |

## Scenario: should apply cascaded outline offset through Draw IR to CPU pixels

1. Render a card with `outline: 2px solid #ef4444` followed by
   `outline-offset: 3px`.
2. Assert its Draw IR computed style is `outline-width = 2` and
   `outline-offset = 3`.
3. Assert the CPU Draw IR renderer paints `0xFFEF4444` at `(3, 3)`, while the
   card interior at `(8, 8)` remains `0xFFFFFFFF`.

### Evidence boundary

This proves the HTML/CSS parser, cascade, layout-produced Draw IR and CPU Draw
IR raster path for this outline witness. It does not claim other Engine2D
backends or general CSS outline conformance.

<details>
<summary>Executable SSpec</summary>

```simple
step("Render a card whose outline offset is declared after the outline shorthand")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#card{display:block;margin:8px;width:10px;height:8px;" +
    "background:#ffffff;outline:2px solid #ef4444;outline-offset:3px}" +
    "</style></head><body><div id='card'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 32, 32)
val card = _draw_ir_command_by_id(composition.batches[0].commands, "card")
val pixels = simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
    html, 32, 32, "cpu")

step("Assert the computed offset survives Draw IR and moves the painted outline")
expect(_draw_ir_style_value(card, "outline-width")).to_equal("2")
expect(_draw_ir_style_value(card, "outline-offset")).to_equal("3")
expect(_pixel_at(pixels, 32, 3, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 32, 8, 8)).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario: should preserve bordered gradient text pixels through the CPU Draw IR adapter

1. Render a 32×24 document with a visible red border, a two-row green-to-blue
   gradient, and overflow-clipped dark text through both `cpu` and `cpu_simd`.
2. Assert both returned, post-shutdown pixel arrays have 768 entries and are
   byte-identical.
3. Assert the border and both gradient endpoint pixels are exact, text ink is
   present, the text Draw IR command has a clip, and the first outside pixel is
   white.

### Evidence boundary

This is adapter parity for the shared CPU Draw IR executor. It proves the
returned pixels remain usable after shutdown for this border/gradient/text/clip
fixture; it does not claim GPU backend parity or iframe DrawIR support.

<details>
<summary>Executable SSpec</summary>

```simple
step("Render one clipped web composition through CPU and CPU SIMD")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#card{display:block;width:12px;height:12px;border:2px solid " +
    "#ef4444;overflow:hidden;background:#ffffff}" +
    "#gradient{display:block;width:8px;height:2px;" +
    "background-image:linear-gradient(#22c55e,#1d4ed8)}" +
    "#copy{display:block;width:32px;height:8px;color:#111827;" +
    "font-size:8px;white-space:nowrap}" +
    "</style></head><body><section id='card'><div id='gradient'></div>" +
    "<span id='copy'>WIDE TEXT</span></section></body></html>"
)
val cpu = simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
    html, 32, 24, "cpu")
val simd = simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
    html, 32, 24, "cpu_simd")
val composition = simple_web_layout_render_html_draw_ir(html, 32, 24)
val copy = _draw_ir_command_by_id(composition.batches[0].commands, "copy")

step("Keep exact shared-executor pixels after adapter shutdown")
expect(cpu.len()).to_equal(32 * 24)
expect(simd.len()).to_equal(32 * 24)
expect(cpu).to_equal(simd)
expect(_pixel_at(cpu, 32, 0, 0)).to_equal(0xFFEF4444u32)
expect(_pixel_at(cpu, 32, 2, 2)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(cpu, 32, 2, 3)).to_equal(0xFF1D4ED8u32)
expect(cpu).to_contain(0xFF111827u32)
expect(copy.clip_rect.present).to_be(true)
expect(_pixel_at(cpu, 32, 16, 6)).to_equal(0xFFFFFFFFu32)
```

</details>
