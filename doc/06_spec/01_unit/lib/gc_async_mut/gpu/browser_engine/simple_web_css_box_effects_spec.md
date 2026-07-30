# Simple Web CSS Box Effects Specification

> Executable source: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl`

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 6 | 6 | 0 | 0 |

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
