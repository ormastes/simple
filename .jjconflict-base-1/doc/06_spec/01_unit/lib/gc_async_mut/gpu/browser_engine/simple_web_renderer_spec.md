# Simple Web Renderer Specification

> This unit spec covers the pure-Simple web renderer path used by browser, web, and Engine2D-backed GUI surfaces. It checks HTML-to-scene conversion, HTML-to-pixel rendering, selector cascade behavior, text raster behavior, Chrome-parity matrix fixtures, static pixel caching, backend-name resolution, and corpus fixture rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 110 | 110 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Renderer Specification

This unit spec covers the pure-Simple web renderer path used by browser, web, and Engine2D-backed GUI surfaces. It checks HTML-to-scene conversion, HTML-to-pixel rendering, selector cascade behavior, text raster behavior, Chrome-parity matrix fixtures, static pixel caching, backend-name resolution, and corpus fixture rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` |
| Updated | 2026-07-30 |
| Generator | Manual synchronization; docgen execution is runtime-blocked |

## Overview

This unit spec covers the pure-Simple web renderer path used by browser, web,
and Engine2D-backed GUI surfaces. It checks HTML-to-scene conversion,
HTML-to-pixel rendering, selector cascade behavior, text raster behavior,
Chrome-parity matrix fixtures, static pixel caching, backend-name resolution,
and corpus fixture rendering.

The Draw IR Phase 4 scenario verifies the semantic inspection side of the same
layout pipeline: `simple_web_layout_render_html_draw_ir` emits an `html_ast`
Draw IR batch with computed style and border/content/hit/clip rectangles before
the pixel renderer paints the page.

**Requirements:** N/A

These scenarios are implementation and architecture evidence for the Simple Web
renderer and active Draw IR inspection plan rather than numbered product
requirements.

**Plan:** doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md

**Design:** doc/04_architecture/ui/simple_gui_stack.md

**Research:** doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md

## Syntax

The spec uses `std.spec` scenarios and the built-in matcher vocabulary. Pixel
assertions remain the rendering oracle; Draw IR assertions inspect semantic
layout metadata before raster.

## Scenarios

### SimpleWebRenderer

#### renders HTML through the canonical browser engine to RenderScene

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: #2050a0'></div></body></html>"
val scene = simple_web_render_html_to_scene(html, 120, 80)
expect(scene.width).to_equal(120)
expect(scene.height).to_equal(80)
expect(scene.commands.len()).to_be_greater_than(0)
```

</details>

#### renders inline url background shorthand fallback colors through RenderScene

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat'></div></body></html>"
expect(_simple_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### renders style block url background shorthand fallback colors through RenderScene

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card { width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat; }</style></head><body><div class='card'></div></body></html>"
expect(_simple_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### resolves repeated CSS custom properties without dropping unresolved vars

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>:root{--panel:#1d4ed8;--accent:#f59e0b}.card{width:40px;height:18px;background-color:var(--panel);border:2px solid var(--accent)}.missing{width:8px;height:8px;background-color:var(--missing)}</style></head><body><div class='card'></div><div class='missing'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 80, 48)
expect(pixels.len()).to_equal(80 * 48)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF141418u32)).to_equal(0)
```

</details>

#### renders HTML to pixels for framebuffer and host adapters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: #2050a0'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 120, 80)
expect(pixels.len()).to_equal(120 * 80)
expect(_count_non_bg(pixels, 0xFFFFFFFF)).to_be_greater_than(0)
```

</details>

#### applies style block colors in the generic layout renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>header { background-color:#1d4ed8; color:#ffffff; font-size:8px; padding:1px; }</style></head><body><header>CMD</header></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF141418u32)).to_equal(0)
```

</details>

#### keeps styled widget panels on authored CSS instead of legacy widget chrome

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}section.widget-panel{display:block;width:20px;height:10px;border:2px solid #0f172a;background-color:#bfdbfe}</style></head><body><section class='widget-panel'></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 40, 24)
expect(simple_web_layout_uses_legacy_widget_chrome(html)).to_equal(false)
expect(pixels.len()).to_equal(40 * 24)
expect(pixels[0]).to_equal(0xFF0F172Au32)
expect(_count_color(pixels, 0xFF0066CCu32)).to_equal(0)
```

</details>

#### honors border-style none while preserving solid border paint

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.solid{display:block;width:12px;height:8px;border-width:2px;border-style:solid;border-color:#ef4444;background-color:#22c55e}.none{display:block;width:12px;height:8px;border-width:2px;border-style:none;border-color:#1d4ed8;background-color:#f59e0b;margin-top:4px}</style></head><body><div class='solid'></div><div class='none'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 40, 32)
expect(pixels.len()).to_equal(40 * 32)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_be_greater_than(0)
```

</details>

#### emits input values as Draw IR text over the input box

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><input id='query' value='Simple'><input id='secret' type='password' value='é'></body></html>"
val composition = simple_web_layout_render_html_draw_ir(
    html, 160, 40
)
val commands = composition.batches[0].commands
val query_box = _draw_ir_command_by_id(commands, "query")
val query_text = _draw_ir_command_by_id(commands, "query_value")
val password_text = _draw_ir_command_by_id(
    commands, "secret_value"
)

expect(query_box.kind).to_equal("box")
expect(query_text.kind).to_equal("text")
expect(query_text.text_value).to_equal("Simple")
expect(password_text.kind).to_equal("text")
expect(password_text.text_value).to_equal("*")
```

</details>

#### shares transformed aligned clipped themed input text with Draw IR

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background:#fff}.clip{display:block;width:22px;height:16px;overflow:hidden}#query{display:block;width:40px;height:16px;padding:2px;border:1px solid #111827;color:#22c55e;font-size:8px;text-transform:uppercase;direction:rtl;text-align:center}#hint{display:block;width:20px;height:14px;padding:1px;border:1px solid #111827;color:#ef4444}</style></head><body><div class='clip'><input id='query' value='abcdefghijk'></div><input id='hint' placeholder='hint'></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 64, 48)
val commands = composition.batches[0].commands
val query = _draw_ir_command_by_id(commands, "query_value")
val hint = _draw_ir_command_by_id(commands, "hint_value")
val pixels = simple_web_render_html_to_pixels(html, 64, 48)

expect(query.kind).to_equal("text")
expect(query.text_value).to_equal("KJIHGFEDCBA")
expect(query.x).to_equal(1)
expect(query.y).to_equal(7)
expect(query.clip_rect.present).to_be(true)
expect(query.clip_rect.x).to_equal(3)
expect(query.clip_rect.y).to_equal(3)
expect(query.clip_rect.width).to_equal(19)
expect(query.clip_rect.height).to_equal(13)
expect(query.color).to_equal(0xFF22C55Eu32)
expect(hint.kind).to_equal("text")
expect(hint.color).to_equal(0xFFEF4444u32)
expect(pixels[7 * 64 + 5]).to_equal(0xFF22C55Eu32)
expect(pixels[7 * 64 + 25]).to_equal(0xFFFFFFFFu32)
```

</details>

#### maps logical border block and inline properties to physical edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#card{display:block;width:10px;height:8px;background-color:#111827;border-block:1px solid #64748b;border-inline:1px solid #64748b;border-block-width:3px 5px;border-inline-width:2px 4px;border-block-color:#94a3b8;border-inline-color:#94a3b8;border-block-style:solid;border-inline-style:solid;border-block-start:3px solid #ef4444;border-block-start-width:3px;border-block-start-color:#ef4444;border-block-start-style:solid;border-block-end:5px solid #1d4ed8;border-block-end-width:5px;border-block-end-color:#1d4ed8;border-block-end-style:solid;border-inline-start:2px solid #f59e0b;border-inline-start-width:2px;border-inline-start-color:#f59e0b;border-inline-start-style:solid;border-inline-end:4px solid #22c55e;border-inline-end-width:4px;border-inline-end-color:#22c55e;border-inline-end-style:solid}#none{display:block;width:8px;height:6px;margin-top:4px;background-color:#e5e7eb;border-block:2px solid #7c3aed;border-inline:2px solid #7c3aed;border-block-style:none;border-inline-style:none;border-block-start-style:none;border-block-end-style:none;border-inline-start-style:none;border-inline-end-style:none}</style></head><body><div id='card'></div><div id='none'></div></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 40, 40)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")
val pixels = simple_web_render_html_to_pixels(html, 40, 40)

expect(_draw_ir_style_value(card, "border-left-width")).to_equal("2")
expect(_draw_ir_style_value(card, "border-top-width")).to_equal("3")
expect(_draw_ir_style_value(card, "border-right-width")).to_equal("4")
expect(_draw_ir_style_value(card, "border-bottom-width")).to_equal("5")
expect(pixels[3]).to_equal(0xFFEF4444u32)
expect(pixels[160]).to_equal(0xFFF59E0Bu32)
expect(pixels[175]).to_equal(0xFF22C55Eu32)
expect(pixels[603]).to_equal(0xFF1D4ED8u32)
expect(pixels[122]).to_equal(0xFF111827u32)
expect(_count_color(pixels, 0xFF7C3AEDu32)).to_equal(0)
```

</details>

#### maps logical border radius corners to physical Draw IR corners

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>#card{display:block;width:18px;height:12px;background-color:#1d4ed8;border-radius:1px;border-top-left-radius:2px;border-top-right-radius:3px;border-bottom-right-radius:4px;border-bottom-left-radius:5px;border-start-start-radius:6px;border-start-end-radius:7px;border-end-start-radius:8px;border-end-end-radius:9px}</style></head><body><section id='card'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 48, 32)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")

expect(_draw_ir_style_value(card, "border-top-left-radius")).to_equal("6")
expect(_draw_ir_style_value(card, "border-top-right-radius")).to_equal("7")
expect(_draw_ir_style_value(card, "border-bottom-left-radius")).to_equal("8")
expect(_draw_ir_style_value(card, "border-bottom-right-radius")).to_equal("9")
```

</details>

#### emits HTML layout Draw IR with computed style and hit geometry before raster

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>#card { background-color:#1d4ed8; color:#ffffff; width:40px; height:18px; padding:2px; border:1px solid #0f172a; }</style></head><body><section id='card'>CMD</section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 96, 64)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")

expect(batch.source.source_kind).to_equal("html_ast")
expect(batch.commands.len()).to_be_greater_than(0)
expect(card.component_id).to_equal("card")
expect(card.border_rect.present).to_equal(true)
expect(card.content_rect.present).to_equal(true)
expect(card.hit_rect.present).to_equal(true)
expect(card.clip_rect.present).to_equal(true)
expect(card.content_rect.x).to_equal(card.x + 3)
expect(card.content_rect.y).to_equal(card.y + 3)
expect(card.content_rect.width).to_equal(40)
expect(card.content_rect.height).to_equal(18)
expect(_draw_ir_style_value(card, "tag")).to_equal("section")
expect(_draw_ir_style_value(card, "display")).to_equal("block")
expect(_draw_ir_style_value(card, "padding-left")).to_equal("2")
```

</details>

#### fails closed to an opaque Draw IR color when the WM material mode is incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section id='card' data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' style='display:block;width:12px;height:8px;background:rgba(255,255,255,0.2);backdrop-filter:blur(30px) saturate(170%)'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 32, 20)
val card = _draw_ir_command_by_id(composition.batches[0].commands, "card")

expect(card.color).to_equal(0xFF123456u32)
expect(_draw_ir_style_value(card, "backdrop-filter-capability")).to_equal("unavailable")
expect(_draw_ir_style_value(card, "backdrop-filter-realized")).to_equal("")
expect(_draw_ir_style_value(card, "backdrop-filter-realized-blur-radius-px")).to_equal("")
expect(_draw_ir_style_value(card, "backdrop-filter-realized-saturation-milli")).to_equal("")
```

</details>

#### lowers a resolved img through Draw IR and Engine2D with object fit

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<img id='photo' src='image://photo' " +
    "style='display:block;width:8px;height:8px;" +
    "object-fit:contain;object-position:right bottom'>" +
    "</body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://photo", 4, 2, [0xFFFF0000u32; 8]
)
val composition = simple_web_layout_render_html_draw_ir_with_images(
    html, 12, 12, [image]
)
val commands = composition.batches[0].commands
val box = _draw_ir_command_by_id(commands, "photo")
val draw = _draw_ir_command_by_id(commands, "photo_image")
val renderer = BrowserRenderer.create(12, 12)
val rendered = renderer.render_html_to_pixels_with_images(
    html, [image]
)

expect(box.kind).to_equal("rect")
expect(draw.kind).to_equal("image")
expect(draw.image_uri).to_equal("image://photo")
expect(draw.x).to_equal(box.content_rect.x)
expect(draw.y).to_equal(box.content_rect.y + 4)
expect(draw.width).to_equal(8)
expect(draw.height).to_equal(4)
expect(draw.clip_rect.present).to_be(true)
expect(rendered.pixel_data.len()).to_equal(12 * 12)
expect(_count_color(
    rendered.pixel_data, 0xFFFF0000u32
)).to_equal(8 * 4)
```

</details>

#### lowers one exact CSS background image with typed tile geometry and border order

- "border:1px solid #123456;background-image:url
   - Expected: draw.kind equals `image`
   - Expected: draw.x equals `box.x + 1`
   - Expected: draw.y equals `box.y + 1`
   - Expected: draw.width equals `box.width - 2`
   - Expected: draw.height equals `box.height - 2`
   - Expected: _draw_ir_style_value(draw, "image-role") equals `css-background`
   - Expected: _draw_ir_style_value(draw, "background-repeat") equals `no-repeat`
   - Expected: _draw_ir_style_value(draw, "background-tile-width") equals `4`
   - Expected: _draw_ir_style_value(draw, "background-tile-height") equals `2`
   - Expected: _draw_ir_style_value(draw, "background-tile-x") equals `{expected_tile_x}`
   - Expected: _draw_ir_style_value(draw, "background-tile-y") equals `{expected_tile_y}`
   - Expected: _draw_ir_style_value(overlay, "image-role") equals `css-background-border-overlay`
-  draw ir command index
-  draw ir command index


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<div id='tile' style='width:8px;height:8px;padding:1px;" +
    "border:1px solid #123456;background-image:url(image://tile);" +
    "background-repeat:no-repeat;background-size:4px auto;" +
    "background-position:right bottom;background-origin:content-box;" +
    "background-clip:padding-box'></div></body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tile", 4, 2, [0xFFFF0000u32; 8]
)
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 20, 20, [image]
).batches[0].commands
val box = _draw_ir_command_by_id(commands, "tile")
val draw = _draw_ir_command_by_id(commands, "tile_background_image")
val overlay = _draw_ir_command_by_id(
    commands, "tile_background_border_overlay"
)
val expected_tile_x = box.x + box.width - 2 - 4
val expected_tile_y = box.y + box.height - 2 - 2

expect(draw.kind).to_equal("image")
expect(draw.x).to_equal(box.x + 1)
expect(draw.y).to_equal(box.y + 1)
expect(draw.width).to_equal(box.width - 2)
expect(draw.height).to_equal(box.height - 2)
expect(_draw_ir_style_value(draw, "image-role")).to_equal("css-background")
expect(_draw_ir_style_value(draw, "background-repeat")).to_equal("no-repeat")
expect(_draw_ir_style_value(draw, "background-tile-width")).to_equal("4")
expect(_draw_ir_style_value(draw, "background-tile-height")).to_equal("2")
expect(_draw_ir_style_value(draw, "background-tile-x")).to_equal("{expected_tile_x}")
expect(_draw_ir_style_value(draw, "background-tile-y")).to_equal("{expected_tile_y}")
expect(_draw_ir_style_value(overlay, "image-role")).to_equal("css-background-border-overlay")
expect(_draw_ir_command_index(commands, "tile")).to_be_less_than(
    _draw_ir_command_index(commands, "tile_background_image")
)
expect(_draw_ir_command_index(commands, "tile_background_image")).to_be_less_than(
    _draw_ir_command_index(commands, "tile_background_border_overlay")
)
```

</details>

#### lowers two URL CSS backgrounds back to front through canonical Draw IR

- "background-image:url
   - Expected: _draw_ir_style_value(back_draw, "background-layer-index") equals `1`
   - Expected: _draw_ir_style_value(front_draw, "background-layer-index") equals `0`
-  draw ir command index
   - Expected: pixels[0] equals `0xFFFF0000u32`
   - Expected: pixels[1] equals `0xFF0000FFu32`
- "url
- "url


<details>
<summary>Executable SSpec</summary>

Runnable source: 74 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<div id='layers' style='width:4px;height:2px;background-color:#00ff00;" +
    "background-image:url(image://front),url(image://back);" +
    "background-repeat:repeat;background-size:2px 1px;" +
    "background-position:left top'></div></body></html>"
)
val front = simpleos_host_gpu_image_resource(
    "image://front", 2, 1, [0xFFFF0000u32, 0u32])
val back = simpleos_host_gpu_image_resource(
    "image://back", 2, 1, [0xFF0000FFu32, 0xFF0000FFu32])
val images = [front, back]
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 8, 4, images
).batches[0].commands
val back_draw = _draw_ir_command_by_id(
    commands, "layers_background_image_1")
val front_draw = _draw_ir_command_by_id(
    commands, "layers_background_image_0")
expect(_draw_ir_style_value(back_draw, "background-layer-index")).to_equal("1")
expect(_draw_ir_style_value(front_draw, "background-layer-index")).to_equal("0")
expect(_draw_ir_command_index(
    commands, "layers_background_image_1")).to_be_less_than(
    _draw_ir_command_index(commands, "layers_background_image_0"))
expect(_draw_ir_command_index(
    commands, "layers_background_image_0")).to_be_less_than(
    _draw_ir_command_index(
        commands, "layers_background_border_overlay"))

val pixels = BrowserRenderer.create(8, 4).render_html_to_pixels_with_images(
    html, images
).pixel_data
expect(pixels[0]).to_equal(0xFFFF0000u32)
expect(pixels[1]).to_equal(0xFF0000FFu32)

val rejected = simple_web_layout_render_html_draw_ir_with_images(
    html.replace(
        "url(image://front),url(image://back)",
        "url(image://front),url(image://back),url(image://front)"
    ), 8, 4, images
).batches[0].commands
expect(_draw_ir_command_index(
    rejected, "layers_background_image_1"
)).to_equal(-1)
expect(_draw_ir_command_index(
    rejected, "layers_background_image_0"
)).to_equal(-1)

val missing = simple_web_layout_render_html_draw_ir_with_images(
    html, 8, 4, [front]
).batches[0].commands
expect(_draw_ir_command_index(
    missing, "layers_background_image_1"
)).to_equal(-1)
expect(_draw_ir_command_index(
    missing, "layers_background_image_0"
)).to_equal(-1)
expect(_draw_ir_command_index(
    missing, "layers_background_border_overlay"
)).to_equal(-1)

val listed = simple_web_layout_render_html_draw_ir_with_images(
    html.replace(
        "background-repeat:repeat",
        "background-repeat:no-repeat,repeat"
    ),
    8, 4, images
).batches[0].commands
expect(_draw_ir_command_index(
    listed, "layers_background_image_1"
)).to_equal(-1)
expect(_draw_ir_command_index(
    listed, "layers_background_image_0"
)).to_equal(-1)
```

</details>

#### retains the unclipped rounded CSS background shape

- "background-image:url
   - Expected: background.width equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<div style='width:8px;height:8px;overflow:hidden'>" +
    "<div id='rounded' style='width:12px;height:8px;border-radius:4px;" +
    "background-image:url(image://tile)'></div></div></body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tile", 2, 2, [0xFFFF0000u32; 4]
)
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 20, 20, [image]
).batches[0].commands

expect(_draw_ir_command_index(commands, "rounded")).to_be_greater_than(-1)
val background = _draw_ir_command_by_id(
    commands, "rounded_background_image")
expect(background.width).to_equal(8)
expect(_draw_ir_style_value(
    background, "background-shape-width")).to_equal("12")
expect(_draw_ir_style_value(
    background, "background-radius-tl-x")).to_equal("4")
expect(_draw_ir_command_index(
    commands, "rounded_background_border_overlay"
)).to_be_greater_than(-1)
```

</details>

#### subtracts content clip insets from each CSS background radius axis

- "background-clip:content-box;background-image:url


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<div id='inset' style='width:8px;height:8px;border-radius:10px;" +
    "border-left:2px solid;border-top:3px solid;border-right:4px solid;" +
    "border-bottom:1px solid;padding:1px 2px 4px 5px;" +
    "background-clip:content-box;background-image:url(image://tile)'>" +
    "</div></body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tile", 1, 1, [0xFFFF0000u32])
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 32, 32, [image]).batches[0].commands
val background = _draw_ir_command_by_id(
    commands, "inset_background_image")

expect(_draw_ir_style_value(
    background, "background-radius-tl-x")).to_equal("3")
expect(_draw_ir_style_value(
    background, "background-radius-tl-y")).to_equal("6")
expect(_draw_ir_style_value(
    background, "background-radius-br-x")).to_equal("4")
expect(_draw_ir_style_value(
    background, "background-radius-br-y")).to_equal("5")
```

</details>

#### lowers the common single-layer background shorthand into the image and fallback color

- "<div id='tile' style='width:8px;height:8px;background:url
   - Expected: box.color equals `0xFF00FF88u32`
   - Expected: draw.kind equals `image`
   - Expected: draw.image_uri equals `image://tile`
   - Expected: _draw_ir_style_value(draw, "background-repeat") equals `no-repeat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<div id='tile' style='width:8px;height:8px;background:url(image://tile) #0f8 no-repeat'></div>" +
    "</body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tile", 4, 2, [0xFFFF0000u32; 8]
)
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 20, 20, [image]
).batches[0].commands
val box = _draw_ir_command_by_id(commands, "tile")
val draw = _draw_ir_command_by_id(commands, "tile_background_image")

expect(box.color).to_equal(0xFF00FF88u32)
expect(draw.kind).to_equal("image")
expect(draw.image_uri).to_equal("image://tile")
expect(_draw_ir_style_value(draw, "background-repeat")).to_equal("no-repeat")
```

</details>

#### lowers positioned sized and boxed background shorthand geometry

- "background:url
   - Expected: _draw_ir_style_value(box, "background-origin") equals `content-box`
   - Expected: _draw_ir_style_value(box, "background-clip") equals `padding-box`
   - Expected: _draw_ir_style_value(draw, "background-tile-width") equals `4`
   - Expected: _draw_ir_style_value(draw, "background-tile-height") equals `2`
   - Expected: _draw_ir_style_value(draw, "background-tile-x") equals `{expected_tile_x}`
   - Expected: _draw_ir_style_value(draw, "background-tile-y") equals `{expected_tile_y}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0'><body style='margin:0;padding:0'>" +
    "<div id='tile' style='width:8px;height:8px;padding:1px;border:1px solid #123456;" +
    "background:url(image://tile) no-repeat right bottom / 4px 2px content-box padding-box scroll'></div>" +
    "</body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tile", 4, 2, [0xFFFF0000u32; 8]
)
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 20, 20, [image]
).batches[0].commands
val box = _draw_ir_command_by_id(commands, "tile")
val draw = _draw_ir_command_by_id(commands, "tile_background_image")
val expected_tile_x = box.x + box.width - 2 - 4
val expected_tile_y = box.y + box.height - 2 - 2

expect(_draw_ir_style_value(box, "background-origin")).to_equal("content-box")
expect(_draw_ir_style_value(box, "background-clip")).to_equal("padding-box")
expect(_draw_ir_style_value(draw, "background-tile-width")).to_equal("4")
expect(_draw_ir_style_value(draw, "background-tile-height")).to_equal("2")
expect(_draw_ir_style_value(draw, "background-tile-x")).to_equal("{expected_tile_x}")
expect(_draw_ir_style_value(draw, "background-tile-y")).to_equal("{expected_tile_y}")
```

</details>

#### fails closed for unknown background shorthand tokens

- "background:url
   - Expected: _draw_ir_command_index(commands, "tile_background_image") equals `-1`
- "url


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body><div id='tile' style='width:8px;height:8px;" +
    "background:url(image://tile) unsupported'></div></body></html>"
)
val image = simpleos_host_gpu_image_resource(
    "image://tile", 4, 2, [0xFFFF0000u32; 8]
)
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 20, 20, [image]
).batches[0].commands
val box = _draw_ir_command_by_id(commands, "tile")

expect(_draw_ir_command_index(commands, "tile_background_image")).to_equal(-1)
expect(_draw_ir_style_value(box, "background-layers-raw")).to_equal(
    "url(image://tile) unsupported"
)
```

</details>

#### projects a complete WM Web material request with explicit bounded realization

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section id='card' data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' style='display:block;width:12px;height:8px;background:linear-gradient(180deg,rgba(255,255,255,0.08),rgba(255,255,255,0.025)),rgba(31,31,33,0.80);backdrop-filter:blur(30px) saturate(170%)'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 32, 20)
val card = _draw_ir_command_by_id(composition.batches[0].commands, "card")

expect(card.color).to_equal(0xFF123456u32)
expect(_draw_ir_style_value(card, "background-color")).to_equal("3424591649")
expect(_draw_ir_style_value(card, "backdrop-filter")).to_equal("blur(30px) saturate(170%)")
expect(_draw_ir_style_value(card, "backdrop-filter-capability")).to_equal("engine2d-cpu-composited-material-v1")
expect(_draw_ir_style_value(card, "backdrop-filter-realized")).to_equal("blur(4px) saturate(170%)")
expect(_draw_ir_style_value(card, "backdrop-filter-realized-blur-radius-px")).to_equal("4")
expect(_draw_ir_style_value(card, "backdrop-filter-realized-saturation-milli")).to_equal("1700")
expect(_draw_ir_style_value(card, "backdrop-filter-reduction-reason")).to_equal("cpu-blur-radius-bounded-to-4")
expect(_draw_ir_style_value(card, "wm-material-surface-alpha-milli")).to_equal("200")
expect(_draw_ir_style_value(card, "background-image-composite-mode")).to_equal("surface-then-alpha-gradient")
expect(_draw_ir_style_value(card, "background-layers-raw")).to_equal("")
```

</details>

#### claims CPU material provenance only with a matching execution receipt

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section id='card' data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' style='display:block;width:12px;height:8px;background:linear-gradient(180deg,rgba(255,255,255,0.08),rgba(255,255,255,0.025)),rgba(31,31,33,0.80);backdrop-filter:blur(30px) saturate(170%)'></section></body></html>"
val layout = simple_web_layout_render_html_draw_ir_result(
    html, 32, 20)
val without_receipt =
    simple_web_layout_material_provenance_after_execution(
        layout.material_witness, 0, 32 * 20, 32 * 20, 0)
val with_receipt =
    simple_web_layout_material_provenance_after_execution(
        layout.material_witness, 0, 32 * 20, 32 * 20, 1)

expect(layout.material_fallback.kind).to_equal("none")
expect(without_receipt.kind).to_equal("none")
expect(with_receipt.kind).to_equal("cpu-composited-material")
expect(with_receipt.reason).to_equal(
    "native-device-backdrop-path-pending")
expect(with_receipt.material_sha256.len()).to_equal(64)
```

</details>

#### requires an independent Metal glass dispatch receipt

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section id='card' data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' style='display:block;width:12px;height:8px;background:rgba(31,31,33,0.80);backdrop-filter:blur(30px) saturate(170%)'></section></body></html>"
val layout = simple_web_layout_render_html_draw_ir_result(
    html, 32, 20)
val final_device_readback_after_cpu =
    simple_web_layout_material_provenance_after_backend_execution(
        layout.material_witness, 0, 32 * 20, 32 * 20,
        1, 0, "cpu-scalar-glass-v1", "device_readback", 7, 11)
val missing_dispatch =
    simple_web_layout_material_provenance_after_backend_execution(
        layout.material_witness, 0, 32 * 20, 32 * 20,
        0, 0, "unavailable", "device_readback", 7, 11)
val mismatched_dispatch =
    simple_web_layout_material_provenance_after_backend_execution(
        layout.material_witness, 0, 32 * 20, 32 * 20,
        0, 2, "metal-device-glass-v1",
        "device_readback", 7, 11)
val metal =
    simple_web_layout_material_provenance_after_backend_execution(
        layout.material_witness, 0, 32 * 20, 32 * 20,
        0, 1, "metal-device-glass-v1",
        "device_readback", 7, 11)

expect(final_device_readback_after_cpu.kind).to_equal(
    "cpu-composited-material")
expect(missing_dispatch.kind).to_equal("none")
expect(mismatched_dispatch.kind).to_equal("none")
expect(metal.kind).to_equal("metal-device-composited-material")
expect(metal.reason).to_equal("metal-device-glass-dispatch")
expect(metal.material_sha256).to_equal(
    layout.material_witness.cpu_composited_sha256)
```

</details>

#### executes Aetheric shorthand through Style Draw IR and the typed CPU receipt

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is the closest integrated public path: the CSS shorthand is
# cascaded into Style, lowered to Draw IR, executed by Engine2D, then
# admitted only through the producer witness plus CPU receipt.
val html = "<html><head><style>#aetheric{display:block;width:12px;height:8px;background:linear-gradient(180deg,rgba(255,255,255,0.08),rgba(255,255,255,0.025)),rgba(31,31,33,0.80);backdrop-filter:blur(30px) saturate(170%)}</style></head><body><section id='aetheric' data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456'></section></body></html>"
val layout = simple_web_layout_render_html_draw_ir_result(html, 32, 20)
val card = _draw_ir_command_by_id(layout.composition.batches[0].commands, "aetheric")
val execution = simple_web_layout_render_html_readback_engine2d_result(
    html, 32, 20, "software")

expect(card.kind).to_equal("rect")
expect(_draw_ir_style_value(card, "backdrop-filter-realized")).to_equal("blur(4px) saturate(170%)")
expect(layout.material_witness.cpu_composited_count).to_equal(1)
expect(layout.material_witness.cpu_composited_sha256.len()).to_equal(64)
expect(execution.readback.pixels.len()).to_equal(32 * 20)
expect(execution.material_fallback.kind).to_equal("cpu-composited-material")
expect(execution.material_fallback.material_sha256).to_equal(layout.material_witness.cpu_composited_sha256)
```

</details>

#### excludes offscreen material commands from the frame witness

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs = " data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456'"
val material = "background:rgba(31,31,33,0.80);backdrop-filter:blur(4px) saturate(120%)"
val html = "<html><body><section id='visible'" + attrs + " style='position:absolute;top:0;width:12px;height:8px;" + material + "'></section><section id='offscreen'" + attrs + " style='position:absolute;top:200px;width:12px;height:8px;" + material + "'></section></body></html>"
val layout = simple_web_layout_render_html_draw_ir_result(
    html, 32, 20
)

expect(_draw_ir_command_by_id(
    layout.composition.batches[0].commands, "visible"
).component_id).to_equal("visible")
expect(_draw_ir_command_by_id(
    layout.composition.batches[0].commands, "offscreen"
).component_id == "offscreen").to_be(false)
expect(layout.material_witness.cpu_composited_count).to_equal(1)
expect(layout.material_witness.cpu_composited_sha256.len()).to_equal(64)
```

</details>

#### culls dense offscreen raw shadows before the frame command cap

- layout composition batches[0] commands len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var html = "<style>.off{position:absolute;top:200px;width:8px;height:8px;box-shadow:2px 3px 6px #000}</style>"
var i = 0
while i < 1100:
    html = html + "<div class='off'></div>"
    i = i + 1
val layout = simple_web_layout_render_html_draw_ir_result(
    html, 32, 20
)

expect(
    layout.composition.batches[0].commands.len()
).to_be_less_than(1024)
```

</details>

#### software-composites Aetheric gradient stops over its translucent base

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:2px;height:2px;background:#ffffff}#aetheric{display:block;width:2px;height:2px;background:linear-gradient(180deg,rgba(255,255,255,0.08),rgba(255,255,255,0.025)),rgba(31,31,33,0.80)}</style></head><body><section id='aetheric'></section></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, 2, 2)

# The centered first-row sample interpolates alpha 20 -> 6 to 17, then
# source-over blends that 7% white over the painted translucent base.
expect(pixels[0]).to_equal(0xFF595959u32)
```

</details>

#### rejects malformed or noncanonical exact-mode backdrop grammar

-  wm material section with backdrop
-  wm material section with backdrop
-  wm material section with backdrop
-  wm material section with backdrop
   - Expected: _draw_ir_style_value(command, "backdrop-filter-capability") equals `unavailable`
   - Expected: _draw_ir_style_value(command, "backdrop-filter-fallback") equals `none`
   - Expected: _draw_ir_style_value(command, "backdrop-filter-realized") equals ``
   - Expected: layout.material_witness.cpu_composited_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body>" +
    _wm_material_section_with_backdrop("space", "blur(4px)  saturate(120%)") +
    _wm_material_section_with_backdrop("decimal", "blur(4.0px) saturate(120%)") +
    _wm_material_section_with_backdrop("over-saturated", "blur(4px) saturate(301%)") +
    _wm_material_section_with_backdrop("extra", "blur(4px) saturate(120%) contrast(110%)") +
    "</body></html>"
)
val layout = simple_web_layout_render_html_draw_ir_result(html, 64, 48)
for component_id in ["space", "decimal", "over-saturated", "extra"]:
    val command = _draw_ir_command_by_id(
        layout.composition.batches[0].commands, component_id)
    expect(_draw_ir_style_value(command, "backdrop-filter-capability")).to_equal("unavailable")
    expect(_draw_ir_style_value(command, "backdrop-filter-fallback")).to_equal("none")
    expect(_draw_ir_style_value(command, "backdrop-filter-realized")).to_equal("")
expect(layout.material_witness.cpu_composited_count).to_equal(0)
```

</details>

#### rejects pre-animation material provenance

- Render an exact material node with an active animation
- "background:rgba
- "backdrop-filter:blur
- Reject a receipt captured before animation application
   - Expected: layout.material_witness.cpu_composited_count equals `0`
   - Expected: layout.material_witness.cpu_composited_sha256 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render an exact material node with an active animation")
val html = (
    "<html><body>" +
    "<section id='animated' " +
    "data-wm-theme-material-mode='engine2d-cpu-composited-material-v1' " +
    "data-wm-theme-fallback='solid-material' " +
    "data-wm-theme-bg='#123456' " +
    "style='display:block;width:12px;height:8px;" +
    "background:rgba(31,31,33,0.80);" +
    "backdrop-filter:blur(4px) saturate(120%);" +
    "animation-name:pulse;animation-duration:1s'></section>" +
    "</body></html>"
)
val layout = simple_web_layout_render_html_draw_ir_result(
    html, 32, 20)

step("Reject a receipt captured before animation application")
expect(layout.material_witness.cpu_composited_count).to_equal(0)
expect(layout.material_witness.cpu_composited_sha256).to_equal("")
```

</details>

#### fails closed for unsupported WM image layers and admits an explicit none reset

-  wm material section
-  wm material section
-  wm material section
-  wm material section
-  wm material section
-  wm material section
-  wm material section
   - Expected: command.color equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html><body>" +
    _wm_material_section("radial", "background-image:radial-gradient(#112233,#445566);") +
    _wm_material_section("multiple", "background-image:linear-gradient(#112233,#445566),linear-gradient(#778899,#aabbcc);") +
    _wm_material_section("url", "background-image:url(hero.png);") +
    _wm_material_section("unknown", "background-image:conic-gradient(#112233,#445566);") +
    _wm_material_section("malformed", "background-image:linear-gradient(#112233);") +
    _wm_material_section("override", "background-image:linear-gradient(#112233,#445566);background-image:radial-gradient(#778899,#aabbcc);") +
    _wm_material_section("reset", "background-image:radial-gradient(#112233,#445566);background-image:none;") +
    "</body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 96, 80)
val rejected_ids = [
    "radial", "multiple", "url", "unknown", "malformed", "override"
]
for rejected_id in rejected_ids:
    val command = _draw_ir_command_by_id(
        composition.batches[0].commands, rejected_id)
    expect(command.color).to_equal(0xFF123456u32)
    expect(_draw_ir_style_value(
        command, "backdrop-filter-capability")).to_equal("unavailable")
    expect(_draw_ir_style_value(
        command, "backdrop-filter-realized")).to_equal("")
    expect(_draw_ir_style_value(
        command, "background-image-composite-mode")).to_equal("")

val reset = _draw_ir_command_by_id(
    composition.batches[0].commands, "reset")
expect(_draw_ir_style_value(
    reset, "background-layers-raw")).to_equal("")
expect(_draw_ir_style_value(
    reset, "backdrop-filter-capability")).to_equal(
        "engine2d-cpu-composited-material-v1")
expect(_draw_ir_style_value(
    reset, "background-image-composite-mode")).to_equal("")
```

</details>

#### applies only matching root custom-property variants with CSS last-wins precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html data-mode='Glass'><head><style>:root[data-mode=glass i]{--panel:#22c55e}:root{--panel:#ef4444}:root[data-mode=opaque]{--panel:#1d4ed8}:root[data-mode=glass i] .unrelated{--panel:#7c3aed}#card{display:block;width:12px;height:8px;background-color:var(--panel)}</style></head><body><section id='card'></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 32, 20)

expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)
expect(_count_color(pixels, 0xFF7C3AEDu32)).to_equal(0)
```

</details>

#### projects a typed first shadow layer while retaining authored CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>#card{display:block;width:12px;height:8px;background-color:#ffffff;box-shadow:5px 4px 12px #dc2626}</style></head><body><section id='card'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 40, 28)
val card = _draw_ir_command_by_id(composition.batches[0].commands, "card")

expect(_draw_ir_style_value(card, "box-shadow")).to_start_with("5px 4px ")
expect(_draw_ir_style_value(card, "box-shadow")).to_end_with("4292617766")
expect(_draw_ir_style_value(card, "box-shadow-blur-radius")).to_equal("12")
expect(_draw_ir_style_value(card, "box-shadow-raw")).to_contain("12px")
```

</details>

#### emits GUI interaction and word wrapping CSS in Draw IR computed style

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>#panel { width:48px; height:20px; cursor:pointer; resize:both; overflow-wrap:anywhere; word-break:break-all; word-wrap:break-word; }</style></head><body><section id='panel'>WRAP</section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 96, 64)
val batch = composition.batches[0]
val panel = _draw_ir_command_by_id(batch.commands, "panel")

expect(_draw_ir_style_value(panel, "cursor")).to_equal("pointer")
expect(_draw_ir_style_value(panel, "resize")).to_equal("both")
expect(_draw_ir_style_value(panel, "overflow-wrap")).to_equal("break-word")
expect(_draw_ir_style_value(panel, "word-wrap")).to_equal("break-word")
expect(_draw_ir_style_value(panel, "word-break")).to_equal("break-all")
```

</details>

#### expands flex-flow shorthand into computed flex direction and wrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#stack{display:flex;flex-flow:column wrap;width:32px;height:24px;gap:2px}.item{width:10px;height:6px;background-color:#22c55e}</style></head><body><section id='stack'><div class='item'></div><div class='item'></div></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 80, 48)
val batch = composition.batches[0]
val stack = _draw_ir_command_by_id(batch.commands, "stack")

expect(_draw_ir_style_value(stack, "display")).to_equal("flex")
expect(_draw_ir_style_value(stack, "flex-direction")).to_equal("column")
expect(_draw_ir_style_value(stack, "flex-wrap")).to_equal("wrap")
```

</details>

#### maps inline logical spacing to horizontal physical layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#card{display:block;background-color:#1d4ed8;width:12px;height:8px;padding-inline:3px 5px;padding-inline-start:4px;margin-inline:2px 6px;margin-inline-end:7px}</style></head><body><section id='card'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 48, 28)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")
val pixels = simple_web_render_html_to_pixels(html, 48, 28)

expect(_draw_ir_style_value(card, "padding-left")).to_equal("4")
expect(_draw_ir_style_value(card, "padding-right")).to_equal("5")
expect(_draw_ir_style_value(card, "margin-left")).to_equal("2")
expect(_draw_ir_style_value(card, "margin-right")).to_equal("7")
expect(card.x).to_equal(2)
expect(card.content_rect.x).to_equal(6)
expect(card.content_rect.width).to_equal(12)
expect(pixels[2]).to_equal(0xFF1D4ED8u32)
expect(pixels[1]).to_equal(0xFFFFFFFFu32)
```

</details>

#### maps block logical spacing to vertical physical layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#card{display:block;background-color:#1d4ed8;width:12px;height:8px;padding-block:3px 5px;padding-block-start:4px;margin-block:2px 6px;margin-block-end:7px}</style></head><body><section id='card'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 48, 32)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")
val pixels = simple_web_render_html_to_pixels(html, 48, 32)

expect(_draw_ir_style_value(card, "padding-top")).to_equal("4")
expect(_draw_ir_style_value(card, "padding-bottom")).to_equal("5")
expect(_draw_ir_style_value(card, "margin-top")).to_equal("2")
expect(_draw_ir_style_value(card, "margin-bottom")).to_equal("7")
expect(card.y).to_equal(2)
expect(card.content_rect.y).to_equal(6)
expect(card.content_rect.height).to_equal(8)
expect(pixels[96]).to_equal(0xFF1D4ED8u32)
expect(pixels[48]).to_equal(0xFFFFFFFFu32)
```

</details>

#### maps logical sizing to physical dimensions and constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#card{display:block;background-color:#1d4ed8;width:4px;height:5px;inline-size:12px;block-size:8px;min-inline-size:16px;max-inline-size:20px;min-block-size:11px;max-block-size:14px}</style></head><body><section id='card'></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 40, 24)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")
val pixels = simple_web_render_html_to_pixels(html, 40, 24)

expect(_draw_ir_style_value(card, "width")).to_equal("12")
expect(_draw_ir_style_value(card, "height")).to_equal("8")
expect(_draw_ir_style_value(card, "min-width")).to_equal("16")
expect(_draw_ir_style_value(card, "max-width")).to_equal("20")
expect(_draw_ir_style_value(card, "min-height")).to_equal("11")
expect(_draw_ir_style_value(card, "max-height")).to_equal("14")
expect(card.content_rect.width).to_equal(16)
expect(card.content_rect.height).to_equal(11)
expect(pixels[0]).to_equal(0xFF1D4ED8u32)
expect(pixels[16]).to_equal(0xFFFFFFFFu32)
```

</details>

#### maps logical inset offsets to physical absolute positioning

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#panel{position:relative;background-color:#e5e7eb;width:40px;height:24px}#card{position:absolute;background-color:#1d4ed8;width:8px;height:6px;inset:1px 2px 3px 4px;inset-block:5px 6px;inset-inline:7px 8px;inset-block-start:9px;inset-inline-end:10px}</style></head><body><section id='panel'><div id='card'></div></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 48, 32)
val batch = composition.batches[0]
val card = _draw_ir_command_by_id(batch.commands, "card")
val pixels = simple_web_render_html_to_pixels(html, 48, 32)

expect(_draw_ir_style_value(card, "left")).to_equal("7")
expect(_draw_ir_style_value(card, "top")).to_equal("9")
expect(_draw_ir_style_value(card, "right")).to_equal("10")
expect(_draw_ir_style_value(card, "bottom")).to_equal("6")
expect(card.x).to_equal(22)
expect(card.y).to_equal(12)
expect(pixels[598]).to_equal(0xFF1D4ED8u32)
expect(pixels[597]).to_equal(0xFFE5E7EBu32)
```

</details>

#### emits editor text metadata CSS in Draw IR computed style

<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>#editor { caret-color:#06b6d4; font-size-adjust:0.5; font-palette:dark; font-feature-settings:'kern' 0; font-language-override:'TRK'; font-variation-settings:'wght' 700; font-variant:small-caps tabular-nums; font-variant-alternates:historical-forms; font-variant-caps:small-caps; font-variant-east-asian:ruby; font-variant-emoji:emoji; font-variant-ligatures:no-common-ligatures; font-variant-numeric:tabular-nums; font-variant-position:super; font-kerning:none; font-optical-sizing:none; font-stretch:expanded; font-width:expanded; font-synthesis:none; font-synthesis-small-caps:none; font-synthesis-position:none; font-synthesis-style:none; font-synthesis-weight:none; hyphens:auto; image-rendering:pixelated; line-break:strict; tab-size:4; table-layout:fixed; text-align-all:center; text-justify:inter-word; vertical-align:middle; unicode-bidi:plaintext; writing-mode:vertical-rl; text-orientation:upright; text-combine-upright:all; will-change:transform, opacity; color-adjust:exact; forced-color-adjust:none; print-color-adjust:exact; orphans:4; widows:5; }</style></head><body><pre id='editor'>A\tB</pre></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 96, 64)
val batch = composition.batches[0]
val editor = _draw_ir_command_by_id(batch.commands, "editor")

expect(_draw_ir_style_value(editor, "caret-color")).to_equal("4278630100")
expect(_draw_ir_style_value(editor, "font-kerning")).to_equal("none")
expect(_draw_ir_style_value(editor, "font-optical-sizing")).to_equal("none")
expect(_draw_ir_style_value(editor, "font-stretch")).to_equal("expanded")
expect(_draw_ir_style_value(editor, "font-width")).to_equal("expanded")
expect(_draw_ir_style_value(editor, "font-size-adjust")).to_equal("0.5")
expect(_draw_ir_style_value(editor, "font-palette")).to_equal("dark")
expect(_draw_ir_style_value(editor, "font-feature-settings")).to_equal("'kern' 0")
expect(_draw_ir_style_value(editor, "font-language-override")).to_equal("'TRK'")
expect(_draw_ir_style_value(editor, "font-variation-settings")).to_equal("'wght' 700")
expect(_draw_ir_style_value(editor, "font-variant")).to_equal("small-caps tabular-nums")
expect(_draw_ir_style_value(editor, "font-variant-alternates")).to_equal("historical-forms")
expect(_draw_ir_style_value(editor, "font-variant-caps")).to_equal("small-caps")
expect(_draw_ir_style_value(editor, "font-variant-east-asian")).to_equal("ruby")
expect(_draw_ir_style_value(editor, "font-variant-emoji")).to_equal("emoji")
expect(_draw_ir_style_value(editor, "font-variant-ligatures")).to_equal("no-common-ligatures")
expect(_draw_ir_style_value(editor, "font-variant-numeric")).to_equal("tabular-nums")
expect(_draw_ir_style_value(editor, "font-variant-position")).to_equal("super")
expect(_draw_ir_style_value(editor, "font-synthesis")).to_equal("none")
expect(_draw_ir_style_value(editor, "font-synthesis-small-caps")).to_equal("none")
expect(_draw_ir_style_value(editor, "font-synthesis-position")).to_equal("none")
expect(_draw_ir_style_value(editor, "font-synthesis-style")).to_equal("none")
expect(_draw_ir_style_value(editor, "font-synthesis-weight")).to_equal("none")
expect(_draw_ir_style_value(editor, "hyphens")).to_equal("auto")
expect(_draw_ir_style_value(editor, "image-rendering")).to_equal("pixelated")
expect(_draw_ir_style_value(editor, "line-break")).to_equal("strict")
expect(_draw_ir_style_value(editor, "tab-size")).to_equal("4")
expect(_draw_ir_style_value(editor, "table-layout")).to_equal("fixed")
expect(_draw_ir_style_value(editor, "text-align")).to_equal("center")
expect(_draw_ir_style_value(editor, "text-align-all")).to_equal("center")
expect(_draw_ir_style_value(editor, "text-justify")).to_equal("inter-word")
expect(_draw_ir_style_value(editor, "vertical-align")).to_equal("middle")
expect(_draw_ir_style_value(editor, "will-change")).to_equal("transform, opacity")
expect(_draw_ir_style_value(editor, "color-adjust")).to_equal("exact")
expect(_draw_ir_style_value(editor, "forced-color-adjust")).to_equal("none")
expect(_draw_ir_style_value(editor, "print-color-adjust")).to_equal("exact")
expect(_draw_ir_style_value(editor, "orphans")).to_equal("4")
expect(_draw_ir_style_value(editor, "widows")).to_equal("5")
expect(_draw_ir_style_value(editor, "unicode-bidi")).to_equal("plaintext")
expect(_draw_ir_style_value(editor, "writing-mode")).to_equal("vertical-rl")
expect(_draw_ir_style_value(editor, "text-orientation")).to_equal("upright")
expect(_draw_ir_style_value(editor, "text-combine-upright")).to_equal("all")
```

</details>

#### renders and exposes text decoration thickness offset and style

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;text-decoration-line:underline;text-decoration-color:#dc2626;text-decoration-style:double;text-decoration-thickness:2px;text-underline-offset:2px;text-underline-position:under}</style></head><body><span id='label' class='label'>UNDER</span></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 96, 40)
val batch = composition.batches[0]
val label = _draw_ir_command_by_id(batch.commands, "label")
val pixels = simple_web_render_html_to_pixels(html, 96, 40)

expect(_draw_ir_style_value(label, "text-decoration-style")).to_equal("double")
expect(_draw_ir_style_value(label, "text-decoration-thickness")).to_equal("2px")
expect(_draw_ir_style_value(label, "text-underline-offset")).to_equal("2px")
expect(_draw_ir_style_value(label, "text-underline-position")).to_equal("under")
expect(_count_color(pixels, 0xFFDC2626u32)).to_be_greater_than(40)
```

</details>

#### renders text-align-last on the final wrapped line

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;width:32px;text-align:left;text-align-last:left}</style></head><body><div id='label' class='label'>AAAA BBBB</div></body></html>"
val right_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;width:32px;text-align:left;text-align-last:right}</style></head><body><div id='label' class='label'>AAAA BBBB</div></body></html>"
val composition = simple_web_layout_render_html_draw_ir(right_html, 80, 48)
val batch = composition.batches[0]
val label = _draw_ir_command_by_id(batch.commands, "label")
val left_pixels = simple_web_render_html_to_pixels(left_html, 80, 48)
val right_pixels = simple_web_render_html_to_pixels(right_html, 80, 48)

expect(_draw_ir_style_value(label, "text-align-last")).to_equal("right")
expect(_count_color(right_pixels, 0xFF111827u32)).to_be_greater_than(0)
expect(_pixels_equal(left_pixels, right_pixels)).to_equal(false)
```

</details>

#### renders font shorthand through size style weight and line height

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normal_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;font-style:normal;font-weight:400;line-height:8px;width:64px}</style></head><body><div id='label' class='label'>Font</div></body></html>"
val shorthand_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font:italic bold 12px/18px sans-serif;width:64px}</style></head><body><div id='label' class='label'>Font</div></body></html>"
val composition = simple_web_layout_render_html_draw_ir(shorthand_html, 96, 48)
val batch = composition.batches[0]
val label = _draw_ir_command_by_id(batch.commands, "label")
val normal_pixels = simple_web_render_html_to_pixels(normal_html, 96, 48)
val shorthand_pixels = simple_web_render_html_to_pixels(shorthand_html, 96, 48)

expect(_draw_ir_style_value(label, "font-size")).to_equal("12")
expect(_draw_ir_style_value(label, "font-style")).to_equal("italic")
expect(_draw_ir_style_value(label, "font-weight")).to_equal("bold")
expect(_draw_ir_style_value(label, "line-height")).to_equal("18")
expect(_count_color(shorthand_pixels, 0xFF111827u32)).to_be_greater_than(0)
expect(_pixels_equal(normal_pixels, shorthand_pixels)).to_equal(false)
```

</details>

#### preserves cascaded font families in text Draw IR computed style

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.parent{font-family:\"Noto Sans Mono\",monospace}.override{font-family:Pixelify Sans,sans-serif}.short{font:italic 700 11.5px   /   20px   \"Roboto Slab\",serif}</style></head><body><div class='parent'><span>Inherited</span><span class='override'>Override</span><span class='short'>Shorthand</span></div></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 160, 64)
val commands = composition.batches[0].commands
val inherited = _draw_ir_text_command(commands, "Inherited")
val overridden = _draw_ir_text_command(commands, "Override")
val shorthand = _draw_ir_text_command(commands, "Shorthand")

expect(composition.schema).to_equal("simple-draw-ir-v2")
expect(_draw_ir_style_value(inherited, "font-family")).to_equal("\"Noto Sans Mono\",monospace")
expect(_draw_ir_style_value(overridden, "font-family")).to_equal("Pixelify Sans,sans-serif")
expect(_draw_ir_style_value(shorthand, "font-family")).to_equal("\"Roboto Slab\",serif")
expect(_draw_ir_style_value(shorthand, "font-size")).to_equal("11")
expect(_draw_ir_style_value(shorthand, "line-height")).to_equal("20")
expect(_draw_ir_style_value(shorthand, "font-style")).to_equal("italic")
expect(_draw_ir_style_value(shorthand, "font-weight")).to_equal("bold")
val identity = _draw_ir_style_value(inherited, "font-identity")
if identity != "":
    expect(inherited.advance_widths.len()).to_be_greater_than(0)
else:
    # Font runtime absence keeps the established bitmap metrics path.
    expect(inherited.advance_widths.len()).to_equal(0)
```

</details>

#### does not report vector size when Draw IR has no resolved face

<details>
<summary>Executable SSpec</summary>

Manual synchronization pending docgen regeneration. This executable negative
control requires the software path to keep vector metadata empty when no Draw
IR text command resolves to the Engine2D-selected vector face.

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body{font-size:17px}</style></head><body>ordinary text</body></html>"
val execution = simple_web_layout_render_html_readback_engine2d_result(
    html, 96, 48, "software")

expect(execution.vector_font_identity).to_equal("")
expect(execution.vector_font_pixel_size).to_equal(0)
```

</details>

#### renders aspect-ratio boxes from a definite width

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.card{width:60px;aspect-ratio:2/1;background-color:#22c55e}.next{width:16px;height:6px;background-color:#f59e0b}</style></head><body><div id='card' class='card'></div><div id='next' class='next'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)

expect(simple_web_layout_debug_layout_by_id(html, 96, 64, "card", "w")).to_equal("60")
expect(simple_web_layout_debug_layout_by_id(html, 96, 64, "card", "h")).to_equal("30")
expect(simple_web_layout_debug_layout_by_id(html, 96, 64, "next", "y")).to_equal("30")
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(60 * 30)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(16 * 6)
```

</details>

#### renders object-fit contain for image placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#f8fafc}img.hero{display:block;width:48px;height:16px;object-fit:contain}</style></head><body><img class='hero widget-image' alt=''></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

expect(pixels.len()).to_equal(64 * 32)
expect(pixels[2 + 8 * 64]).to_equal(0xFFF8FAFCu32)
expect(pixels[12 + 8 * 64]).to_equal(0xFF2563EBu32)
expect(_count_color(pixels, 0xFF2563EBu32)).to_equal(280)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(56)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(48)
```

</details>

#### renders object-position for contained image placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#f8fafc}img.hero{display:block;width:48px;height:16px;object-fit:contain;object-position:left top}</style></head><body><img class='hero widget-image' alt=''></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

expect(pixels.len()).to_equal(64 * 32)
expect(pixels[2 + 8 * 64]).to_equal(0xFF2563EBu32)
expect(pixels[30 + 8 * 64]).to_equal(0xFFF8FAFCu32)
expect(_count_color(pixels, 0xFF2563EBu32)).to_equal(280)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(56)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(48)
```

</details>

#### uses generated widget chrome text only when non-empty text sits under a widget ancestor

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html_with_widget_text = "<html><body><section class='widget-panel'><div class='widget-button'><span>Menu</span></div></section></body></html>"
val html_without_widget_text = "<html><body><section class='widget-panel'></section><div>Menu</div></body></html>"
val with_widget_text = simple_web_render_html_to_pixels(html_with_widget_text, 40, 64)
val without_widget_text = simple_web_render_html_to_pixels(html_without_widget_text, 40, 64)
val chrome_probe = 9 + 7 * 40
expect(with_widget_text.len()).to_equal(40 * 64)
expect(without_widget_text.len()).to_equal(40 * 64)
expect(with_widget_text[chrome_probe]).to_equal(0xFF48484Bu32)
expect(without_widget_text[chrome_probe]).to_equal(0xFFF5F5F5u32)
expect(_pixels_equal(with_widget_text, without_widget_text)).to_equal(false)
```

</details>

#### keeps lowercase browser text glyphs distinct from uppercase glyphs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lower_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;background-color:#ffffff}</style></head><body><div class='label'>chrome baseline</div></body></html>"
val upper_html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.label{color:#111827;font-size:8px;background-color:#ffffff}</style></head><body><div class='label'>CHROME BASELINE</div></body></html>"
val lower = simple_web_render_html_to_pixels(lower_html, 96, 32)
val upper = simple_web_render_html_to_pixels(upper_html, 96, 32)
expect(lower.len()).to_equal(96 * 32)
expect(_count_color(lower, 0xFF111827u32)).to_be_greater_than(0)
expect(_pixels_equal(lower, upper)).to_equal(false)
```

</details>

#### keeps abbr in canonical inline flow

<details>
<summary>Executable SSpec</summary>

The four-step scenario calls the same frozen helpers as the executable source:

```simple
step("Build abbr span and block-control fixtures")
val fixtures = setup_abbr_inline_fixtures()

step("Resolve abbr to the inline user-agent display")
check_abbr_computed_inline_style(fixtures)

step("Match span layout and canonical Draw IR geometry")
check_abbr_layout_and_draw_ir_parity(fixtures)

step("Match span pixels and reject block fallback")
check_abbr_cpu_pixel_parity(fixtures)
```

`setup_abbr_inline_fixtures` builds three otherwise-identical documents:
index 0 uses `<abbr id='term'>MID</abbr>`, index 1 uses the literal inline
control `<span id='term'>MID</span>`, and index 2 uses the negative control
`<span id='term' style='display:block'>MID</span>`. Each fixture preserves the
same `LEFT`, `MID`, and `RIGHT` text-node order.

`check_abbr_computed_inline_style` requires exact computed `display` values of
`inline`, `inline`, and `block`, respectively.

`check_abbr_layout_and_draw_ir_parity` requires the abbr and span `term`,
`MID`, and `RIGHT` Draw IR geometry arrays `[x, y, width, height]` to match and
requires their `MID` and `RIGHT` glyph advances to match. It also requires the
abbr `term` and `RIGHT` geometry to differ from the forced-block control.

`check_abbr_cpu_pixel_parity` requires the complete CPU pixel array for abbr to
equal the span pixels and to differ from the forced-block pixels.

</details>

#### keeps time in canonical inline flow

<details>
<summary>Executable SSpec</summary>

The four-step scenario follows the existing inline-element control pattern:

```simple
step("Build time span and block-control fixtures")
val fixtures = setup_time_inline_fixtures()

step("Resolve time to the inline user-agent display")
check_time_computed_inline_style(fixtures)

step("Preserve time semantics and match canonical Draw IR geometry")
check_time_layout_and_draw_ir_parity(fixtures)

step("Match span pixels and reject block fallback")
check_time_cpu_pixel_parity(fixtures)
```

`setup_time_inline_fixtures` builds three otherwise-identical documents:
index 0 uses `<time id='term'>MID</time>`, index 1 uses the literal inline
control `<span id='term'>MID</span>`, and index 2 uses the negative control
`<span id='term' style='display:block'>MID</span>`. Each fixture preserves the
same `LEFT`, `MID`, and `RIGHT` text-node order.

`check_time_computed_inline_style` requires exact computed `display` values of
`inline`, `inline`, and `block`, respectively.

`check_time_layout_and_draw_ir_parity` requires the `time` semantic tag and
`row` parent identity, then requires the time and span `term`, `MID`, and
`RIGHT` Draw IR geometry arrays `[x, y, width, height]` and text advances to
match. It also requires the time `term` and `RIGHT` geometry to differ from the
forced-block control.

`check_time_cpu_pixel_parity` requires the complete CPU Engine2D pixel array
for time to equal the span pixels and to differ from the forced-block pixels.

</details>

#### lowers text-transform through Draw IR to exact uppercase pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val common = "<html><head><style>html,body{margin:0;padding:0;background:#fff}.label{color:#111827;font-size:16px}</style></head><body>"
val transformed_html = common + "<div class='label' style='text-transform:uppercase'>mix-wide</div></body></html>"
val uppercase_html = common + "<div class='label'>MIX-WIDE</div></body></html>"
val lowercase_html = common + "<div class='label'>mix-wide</div></body></html>"

step("Compute uppercase CSS on lowercase source")
val transformed_composition = simple_web_layout_render_html_draw_ir(
    transformed_html, 96, 32
)
val uppercase_composition = simple_web_layout_render_html_draw_ir(
    uppercase_html, 96, 32
)
val transformed = _draw_ir_text_command(
    transformed_composition.batches[0].commands, "MIX-WIDE"
)
val uppercase = _draw_ir_text_command(
    uppercase_composition.batches[0].commands, "MIX-WIDE"
)
expect(_draw_ir_style_value(
    transformed, "text-transform"
)).to_equal("uppercase")

step("Lower transformed text through canonical Draw IR")
expect(transformed.kind).to_equal("text")
expect(transformed.text_value).to_equal("MIX-WIDE")

step("Match literal-uppercase geometry and font payload")
expect([
    transformed.x, transformed.y,
    transformed.width, transformed.height
]).to_equal([
    uppercase.x, uppercase.y, uppercase.width, uppercase.height
])
expect(_draw_ir_style_value(
    transformed, "font-family"
)).to_equal(_draw_ir_style_value(uppercase, "font-family"))
expect(_draw_ir_style_value(
    transformed, "font-identity"
)).to_equal(_draw_ir_style_value(uppercase, "font-identity"))
expect(transformed.advance_widths).to_equal(uppercase.advance_widths)

step("Rasterize exact literal-uppercase pixels")
val transformed_pixels = (
    simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
        transformed_html, 96, 32, "cpu"
    )
)
val uppercase_pixels = (
    simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
        uppercase_html, 96, 32, "cpu"
    )
)
val lowercase_pixels = (
    simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
        lowercase_html, 96, 32, "cpu"
    )
)
expect(transformed_pixels).to_equal(uppercase_pixels)
expect(_pixels_equal(
    transformed_pixels, lowercase_pixels
)).to_equal(false)
```

</details>

#### renders the text-raster fixture with genuine glyph ink (no memorized Chrome overlay)

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The renderer used to paste a hard-coded captured-Chrome pixel table over
# this scene so it could assert Chrome's antialiased counts (4881/316/163/1).
# That overlay was a machine/version-specific tautology and was removed; these
# assertions now describe the renderer's own honest software-rasterized output
# (solid 5x7 glyph ink + a 1px panel border). Per-pixel parity vs Chrome's
# font rasterizer is intentionally NOT asserted here — it is tracked as
# known-divergent in the electron web-layout manifest (track-text-divergence).
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#ffffff}.panel{background-color:#f8fafc;border:1px solid #334155;padding:4px;width:86px;height:54px}.title{color:#0f172a;font-size:16px;background-color:#f8fafc}.sub{color:#475569;font-size:8px;background-color:#f8fafc;margin-top:4px}</style></head><body><section class='panel'><div class='title'>TEXT RASTER</div><div class='sub'>Chrome AA baseline</div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(316)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_be_greater_than(4000)
expect(_count_color(pixels, 0xFF0F172Au32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF475569u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFFFFFFFu32)).to_equal(0)
```

</details>

#### uses explicit line-height for wrapped text layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#e5e7eb;padding:4px;width:60px;height:56px}.copy{background-color:#dbeafe;color:#0f172a;font-size:8px;line-height:12px;width:22px}.after{background-color:#f59e0b;width:10px;height:6px;margin-top:2px}</style></head><body><section class='shell'><div class='copy'>ALPHA BETA GAMMA</div><div class='after'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
# The .after box lands at y=42 because the explicit 12px line-height pushes
# the wrapped .copy text down — this is the actual line-height behaviour.
expect(pixels[4 + 42 * 96]).to_equal(0xFFF59E0Bu32)
# The wrapped copy text renders genuine glyph ink (was a memorized overlay
# pixel 0xFF3C4559; now the renderer draws solid 0xFF0F172A glyph ink).
expect(_count_color(pixels, 0xFF0F172Au32)).to_be_greater_than(0)
```

</details>

#### applies class selector colors and inline overrides in generic layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}#override{background-color:#f59e0b;color:#111827;font-size:8px;padding:1px}</style></head><body><div class='status'>CLASS</div><button id='override' style='background-color:#ef4444;color:#ffffff;font-size:8px;padding:1px'>INLINE</button></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
```

</details>

#### scopes descendant selector colors to matching ancestors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel .status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>IN</div></section><div class='status'>OUT</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF334155u32)).to_be_greater_than(0)
```

</details>

#### scopes child selector colors to direct children only

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel>.status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>DIRECT</div><div><span class='status'>NESTED</span></div></section><div class='status'>OUT</div></body></html>"
val descendant_html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel .status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>DIRECT</div><div><span class='status'>NESTED</span></div></section><div class='status'>OUT</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
val descendant_pixels = simple_web_render_html_to_pixels(descendant_html, 96, 64)
val child_green = _count_color(pixels, 0xFF22C55Eu32)
val descendant_green = _count_color(descendant_pixels, 0xFF22C55Eu32)
expect(pixels.len()).to_equal(96 * 64)
expect(child_green).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF334155u32)).to_be_greater_than(0)
expect(child_green).to_be_less_than(descendant_green)
```

</details>

<details>
<summary>Advanced: matches Chrome content-box flex geometry for a text-free CSS matrix</summary>

#### matches Chrome content-box flex geometry for a text-free CSS matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{display:flex;gap:4px;background-color:#0f172a;padding:4px;width:88px;height:56px}.rail{background-color:#1d4ed8;width:12px;height:48px}.stack{display:flex;flex-direction:column;gap:3px;background-color:#e5e7eb;padding:3px;width:60px;height:42px}.row{background-color:#22c55e;width:54px;height:10px}.row.alt{background-color:#f59e0b;width:36px;height:10px}.leaf{background-color:#ef4444;width:18px;height:8px;margin-left:6px}</style></head><body><section class='shell'><div class='rail'></div><div class='stack'><div class='row'></div><div class='row alt'></div><div class='leaf'></div></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(0)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(2400)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2124)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(576)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(540)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(360)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(144)
```

</details>


</details>

#### applies flex order independent of document order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:16px;overflow:hidden;background-color:#f8fafc}.shell{display:flex;width:32px;height:16px}.first{order:2;background-color:#ef4444;width:8px;height:8px}.second{order:1;background-color:#22c55e;width:8px;height:8px}.third{order:3;background-color:#1d4ed8;width:8px;height:8px}</style></head><body><section class='shell'><div class='first'></div><div class='second'></div><div class='third'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 32, 16)
expect(pixels.len()).to_equal(32 * 16)
expect(pixels[4 + 4 * 32]).to_equal(0xFF22C55Eu32)
expect(pixels[12 + 4 * 32]).to_equal(0xFFEF4444u32)
expect(pixels[20 + 4 * 32]).to_equal(0xFF1D4ED8u32)
```

</details>

#### keeps equal flex order in document order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:16px;overflow:hidden;background-color:#f8fafc}.shell{display:flex;width:32px;height:16px}.first{order:1;background-color:#ef4444;width:8px;height:8px}.second{order:1;background-color:#22c55e;width:8px;height:8px}.third{order:1;background-color:#1d4ed8;width:8px;height:8px}</style></head><body><section class='shell'><div class='first'></div><div class='second'></div><div class='third'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 32, 16)
expect(pixels.len()).to_equal(32 * 16)
expect(pixels[4 + 4 * 32]).to_equal(0xFFEF4444u32)
expect(pixels[12 + 4 * 32]).to_equal(0xFF22C55Eu32)
expect(pixels[20 + 4 * 32]).to_equal(0xFF1D4ED8u32)
```

</details>

<details>
<summary>Advanced: matches Chrome solid-border and nested-selector geometry for a text-free CSS matrix</summary>

#### matches Chrome solid-border and nested-selector geometry for a text-free CSS matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#dbeafe;border:2px solid #0f172a;padding:4px;width:84px;height:52px}.shell>.direct{background-color:#22c55e;border:1px solid #14532d;width:24px;height:12px}.shell .nested .target{background-color:#f59e0b;border:2px solid #7c2d12;width:36px;height:10px;margin-left:6px}.shell>.nested{background-color:#e5e7eb;border:1px solid #334155;padding:3px;width:60px;height:24px;margin-top:4px}.outside .target{background-color:#ef4444;width:10px;height:10px}</style></head><body><section class='shell'><div class='direct'></div><div class='nested'><div class='target'></div></div></section><section class='outside'><div class='target'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFDBEAFEu32)).to_equal(2980)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(1420)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(624)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(360)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(288)
expect(_count_color(pixels, 0xFF7C2D12u32)).to_equal(200)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(196)
expect(_count_color(pixels, 0xFF14532Du32)).to_equal(76)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: matches Chrome asymmetric border-side geometry for a text-free CSS matrix</summary>

#### matches Chrome asymmetric border-side geometry for a text-free CSS matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#e5e7eb;border-left:4px solid #0f172a;border-top:2px solid #0f172a;border-right:6px solid #0f172a;border-bottom:3px solid #0f172a;padding:3px 5px 7px 9px;width:70px;height:40px}.box{background-color:#22c55e;width:20px;height:8px}.next{background-color:#1d4ed8;border:1px solid #334155;border-width:1px 3px 2px 5px;padding:2px;width:16px;height:6px;margin-top:4px}.leaf{background-color:#f59e0b;width:8px;height:3px}</style></head><body><section class='shell'><div class='box'></div><div class='next'><div class='leaf'></div></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(3676)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(974)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(970)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(176)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(164)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(160)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(24)
```

</details>


</details>

<details>
<summary>Advanced: matches Chrome overflow hidden clipping for a text-free CSS matrix</summary>

#### matches Chrome overflow hidden clipping for a text-free CSS matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{overflow:hidden;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:40px;height:24px}.wide{background-color:#22c55e;width:70px;height:10px}.tall{background-color:#1d4ed8;width:20px;height:20px;margin-top:4px}.outside{background-color:#ef4444;width:10px;height:10px;margin-top:4px}</style></head><body><section class='shell'><div class='wide'></div><div class='tall'></div><div class='outside'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(4272)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(816)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(440)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(336)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(280)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>


</details>

#### clips canonical Draw IR boxes and text to an overflow hidden ancestor

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:24px;overflow:hidden;background:#fff}.clip{overflow:hidden;width:16px;height:12px}.wide{width:32px;height:4px;background:#ef4444}.words{display:block;width:40px;height:8px;white-space:nowrap;color:#111827;font-size:8px}</style></head><body><div class='clip'><div class='wide'></div><span class='words'>ABCDEFGHIJK</span></div></body></html>"
val execution = simple_web_layout_render_html_readback_engine2d_result(
    html, 48, 24, "software"
)
val pixels = execution.readback.pixels
expect(pixels.len()).to_equal(48 * 24)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(16 * 4)
expect(_count_non_color_rect(
    pixels, 48, 16, 0, 48, 12, 0xFFFFFFFFu32
)).to_equal(0)
```

</details>

#### clips overflowing descendants for CSS paint containment

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;overflow:hidden;background-color:#ffffff}.shell{contain:paint;background-color:#1d4ed8;width:20px;height:12px}.spill{background-color:#ef4444;width:10px;height:10px;margin-left:24px}</style></head><body><section class='shell'><div class='spill'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 48, 32)
expect(pixels.len()).to_equal(48 * 32)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>

#### suppresses rendered scrollbars for scrollbar width none

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;overflow:hidden;background-color:#ffffff}.shell{overflow-x:hidden;overflow-y:scroll;scrollbar-width:none;background-color:#1d4ed8;width:32px;height:20px}.tall{background-color:#22c55e;width:8px;height:40px}</style></head><body><section class='shell'><div class='tall'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 48, 32)
expect(pixels.len()).to_equal(48 * 32)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFF1F1F1u32)).to_equal(0)
```

</details>

#### renders custom scrollbar colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;overflow:hidden;background-color:#ffffff}.shell{overflow-x:hidden;overflow-y:scroll;scrollbar-color:#9333ea #f97316;background-color:#1d4ed8;width:32px;height:20px}.tall{background-color:#22c55e;width:8px;height:40px}</style></head><body><section class='shell'><div class='tall'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 48, 32)
expect(pixels.len()).to_equal(48 * 32)
expect(_count_color(pixels, 0xFF9333EAu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFF97316u32)).to_be_greater_than(0)
```

</details>

#### matches Chrome visibility hidden paint suppression while preserving layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#e5e7eb;padding:4px;width:60px;height:44px}.hidden{visibility:hidden;background-color:#ef4444;border:2px solid #7f1d1d;padding:2px;width:24px;height:10px}.hidden .child{background-color:#f59e0b;width:12px;height:4px}.next{background-color:#1d4ed8;width:18px;height:8px;margin-top:4px}.shown{visibility:visible;background-color:#22c55e;width:12px;height:6px;margin-top:3px}</style></head><body><section class='shell'><div class='hidden'><div class='child'></div></div><div class='next'></div><div class='shown'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(3320)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2608)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(144)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(72)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
expect(_count_color(pixels, 0xFF7F1D1Du32)).to_equal(0)
```

</details>

#### renders content visibility hidden containers while suppressing descendants

- Compute hidden content-visibility semantics
- Render CPU and canonical Draw IR pixels
- Inspect the GPU fill operations
- Verify panel paint and descendant suppression
   - Expected: cpu_pixels.len() equals `48 * 32`
   - Expected: draw_ir_pixels.len() equals `48 * 32`
   - Expected: gpu_frame.cpu_paint_pixels equals `0`
   - Expected: partial_frame.cpu_paint_pixels equals `48 * 32`
   - Expected: gpu_blue_ops equals `1`
   - Expected: gpu_blue_panel_ops equals `1`
   - Expected: gpu_red_ops equals `0`
   - Expected: deep_visits - shallow_visits equals `192`
   - Expected: _count_color(cpu_pixels, 0xFFEF4444u32) equals `0`
   - Expected: _count_color(draw_ir_pixels, 0xFFEF4444u32) equals `0`
   - Expected: _pixels_equal(cpu_pixels, draw_ir_pixels) is true
   - Expected: _pixels_equal(cpu_pixels, presented.pixels) is true
   - Expected: _pixels_equal(partial_cpu, partial_presented.pixels) is true
   - Expected: _pixels_equal(visibility_override_cpu, visibility_override_presented.pixels) is true
   - Expected: _count_color(visibility_override_presented.pixels, 0xFFEF4444u32) equals `0`
   - Expected: _draw_ir_command_index(batch.commands, "child") equals `-1`
   - Expected: _draw_ir_style_value(panel, "content-visibility") equals `hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 93 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compute hidden content-visibility semantics")
val html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;overflow:hidden;background-color:#ffffff}#panel{display:block;content-visibility:hidden;width:24px;height:16px;background-color:#1d4ed8}#child{display:block;width:20px;height:12px;background-color:#ef4444}</style></head><body><section id='panel'><div id='child'></div></section></body></html>"
val partial_html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;background:#fff}#group{opacity:.5;width:24px;height:16px;background:#1d4ed8}#partial-child{width:20px;height:12px;background:#ef4444}</style></head><body><section id='group'><div id='partial-child'></div></section></body></html>"
val visibility_override_html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;background:#fff}#hidden-parent{visibility:hidden;width:24px;height:16px;background:#ef4444}#visible-child{visibility:visible;width:20px;height:12px;background:#1d4ed8}</style></head><body><section id='hidden-parent'><div id='visible-child'></div></section></body></html>"
step("Render CPU and canonical Draw IR pixels")
val cpu_pixels = simple_web_layout_render_html_software_pixels(
    html, 48, 32
)
val draw_ir_readback = simple_web_layout_render_html_readback_engine2d_result(
    html, 48, 32, "software"
)
val draw_ir_pixels = draw_ir_readback.readback.pixels
val presented = simple_web_layout_render_html_readback_paint(
    html, 48, 32, "cpu_simd", true
)
val partial_cpu = simple_web_layout_render_html_software_pixels(
    partial_html, 48, 32
)
val partial_presented = simple_web_layout_render_html_readback_paint(
    partial_html, 48, 32, "cpu_simd", true
)
val visibility_override_cpu = (
    simple_web_layout_render_html_software_pixels(
        visibility_override_html, 48, 32
    )
)
val visibility_override_presented = (
    simple_web_layout_render_html_readback_paint(
        visibility_override_html, 48, 32, "cpu_simd", true
    )
)
val composition = simple_web_layout_render_html_draw_ir(html, 48, 32)
val batch = composition.batches[0]
val panel = _draw_ir_command_by_id(batch.commands, "panel")
step("Inspect the GPU fill operations")
val gpu_frame = simple_web_layout_render_html_gpu_frame(html, 48, 32)
val partial_frame = simple_web_layout_render_html_gpu_frame(
    partial_html, 48, 32
)
var gpu_blue_ops = 0
var gpu_blue_panel_ops = 0
var gpu_red_ops = 0
for op in gpu_frame.fill_ops:
    if op.color == 0xFF1D4ED8u32 as i32:
        gpu_blue_ops = gpu_blue_ops + 1
        if op.x == 0 and op.y == 0 and op.width == 24 and op.height == 16:
            gpu_blue_panel_ops = gpu_blue_panel_ops + 1
    if op.color == 0xFFEF4444u32 as i32:
        gpu_red_ops = gpu_red_ops + 1
var shallow_html = "<html><body style='margin:0'>"
var deep_html = "<html><body style='margin:0'>"
var depth = 0
while depth < 256:
    deep_html = deep_html + "<div>"
    if depth < 64:
        shallow_html = shallow_html + "<div>"
    depth = depth + 1
depth = 0
while depth < 256:
    deep_html = deep_html + "</div>"
    if depth < 64:
        shallow_html = shallow_html + "</div>"
    depth = depth + 1
shallow_html = shallow_html + "</body></html>"
deep_html = deep_html + "</body></html>"
val shallow_visits = simple_web_layout_debug_gpu_paint_state_visits(
    shallow_html, 8
)
val deep_visits = simple_web_layout_debug_gpu_paint_state_visits(
    deep_html, 8
)
step("Verify panel paint and descendant suppression")
expect(cpu_pixels.len()).to_equal(48 * 32)
expect(draw_ir_pixels.len()).to_equal(48 * 32)
expect(gpu_frame.cpu_paint_pixels).to_equal(0)
expect(partial_frame.cpu_paint_pixels).to_equal(48 * 32)
expect(gpu_frame.fill_ops.len()).to_be_greater_than(0)
expect(gpu_blue_ops).to_equal(1)
expect(gpu_blue_panel_ops).to_equal(1)
expect(gpu_red_ops).to_equal(0)
expect(deep_visits - shallow_visits).to_equal(192)
expect(_count_color(cpu_pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(draw_ir_pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(cpu_pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(draw_ir_pixels, 0xFFEF4444u32)).to_equal(0)
expect(_pixels_equal(cpu_pixels, draw_ir_pixels)).to_equal(true)
expect(_pixels_equal(cpu_pixels, presented.pixels)).to_equal(true)
expect(_pixels_equal(partial_cpu, partial_presented.pixels)).to_equal(true)
expect(_pixels_equal(visibility_override_cpu, visibility_override_presented.pixels)).to_equal(true)
expect(_count_color(visibility_override_presented.pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(visibility_override_presented.pixels, 0xFFEF4444u32)).to_equal(0)
expect(_draw_ir_command_index(batch.commands, "child")).to_equal(-1)
expect(_draw_ir_style_value(panel, "content-visibility")).to_equal("hidden")
```

</details>

#### matches Chrome display contents wrapper suppression

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#e5e7eb;padding:4px;width:60px;height:44px}.contents{display:contents;margin-top:20px;background-color:#ef4444;border:3px solid #7f1d1d;padding:6px;width:40px;height:24px}.first{background-color:#1d4ed8;width:24px;height:8px}.second{background-color:#22c55e;width:18px;height:8px;margin-top:4px}.after{background-color:#f59e0b;width:12px;height:6px;margin-top:4px}</style></head><body><section class='shell'><div class='contents'><div class='first'></div><div class='second'></div></div><div class='after'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2608)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(3128)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(192)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(72)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFF7F1D1Du32)).to_equal(0)
```

</details>

#### matches Chrome positioned absolute geometry without normal-flow contribution

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.abs{position:absolute;left:32px;top:4px;background-color:#1d4ed8;width:20px;height:12px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}.abs2{position:absolute;left:6px;top:30px;background-color:#f59e0b;width:16px;height:8px}</style></head><body><section class='shell'><div class='flow'></div><div class='abs'></div><div class='next'></div><div class='abs2'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2696)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(240)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(192)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(128)
```

</details>

#### matches Chrome positioned right and bottom offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.right{position:absolute;right:6px;top:6px;background-color:#1d4ed8;width:12px;height:10px}.bottom{position:absolute;right:8px;bottom:5px;background-color:#f59e0b;width:16px;height:8px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='flow'></div><div class='right'></div><div class='bottom'></div><div class='next'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2816)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(192)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(128)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(120)
```

</details>

#### matches Chrome positioned absolute paint order over normal-flow siblings

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.abs{position:absolute;left:10px;top:8px;background-color:#1d4ed8;width:30px;height:20px}.next{background-color:#334155;width:36px;height:14px;margin-top:4px}</style></head><body><section class='shell'><div class='flow'></div><div class='abs'></div><div class='next'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2560)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(600)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(144)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(96)
```

</details>

#### matches Chrome positioned positive z-index ordering

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.base{background-color:#22c55e;width:36px;height:14px}.high{position:absolute;left:8px;top:6px;z-index:2;background-color:#f59e0b;width:30px;height:20px}.low{position:absolute;left:14px;top:10px;z-index:1;background-color:#1d4ed8;width:30px;height:20px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='base'></div><div class='high'></div><div class='low'></div><div class='next'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2400)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(600)
expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(216)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(128)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(56)
```

</details>

#### keeps positive z-index paint order independent of document order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:32px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;width:32px;height:32px}.top{position:absolute;left:4px;top:4px;z-index:3;background-color:#f59e0b;width:12px;height:12px}.bottom{position:absolute;left:4px;top:4px;z-index:1;background-color:#1d4ed8;width:12px;height:12px}.middle{position:absolute;left:4px;top:4px;z-index:2;background-color:#22c55e;width:12px;height:12px}</style></head><body><section class='shell'><div class='top'></div><div class='bottom'></div><div class='middle'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 32, 32)
expect(pixels.len()).to_equal(32 * 32)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(144)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(0)
```

</details>

#### keeps canonical Draw IR positive z-index order independent of document order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:32px;overflow:hidden;background:#f8fafc}.shell{position:relative;width:32px;height:32px}.top{position:absolute;left:4px;top:4px;z-index:3;background:#f59e0b;width:12px;height:12px}.bottom{position:absolute;left:4px;top:4px;z-index:1;background:#1d4ed8;width:12px;height:12px}.middle{position:absolute;left:4px;top:4px;z-index:2;background:#22c55e;width:12px;height:12px}</style></head><body><section class='shell'><div class='top'></div><div class='bottom'></div><div class='middle'></div></section></body></html>"
val execution = simple_web_layout_render_html_readback_engine2d_result(
    html, 32, 32, "software"
)
val pixels = execution.readback.pixels
expect(pixels.len()).to_equal(32 * 32)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(12 * 12)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(0)
```

</details>

#### sorts nested canonical Draw IR positive stacking siblings

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:32px;overflow:hidden;background:#f8fafc}.outer{position:absolute;left:4px;top:4px;z-index:1;width:16px;height:16px}.top{position:absolute;left:0;top:0;z-index:3;background:#f59e0b;width:12px;height:12px}.bottom{position:absolute;left:0;top:0;z-index:1;background:#1d4ed8;width:12px;height:12px}.middle{position:absolute;left:0;top:0;z-index:2;background:#22c55e;width:12px;height:12px}</style></head><body><section class='outer'><div class='top'></div><div class='bottom'></div><div class='middle'></div></section></body></html>"
val execution = simple_web_layout_render_html_readback_engine2d_result(
    html, 32, 32, "software"
)
val pixels = execution.readback.pixels
expect(pixels.len()).to_equal(32 * 32)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(12 * 12)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(0)
```

</details>

#### keeps equal positive z-index paint order stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:32px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;width:32px;height:32px}.first{position:absolute;left:4px;top:4px;z-index:1;background-color:#ef4444;width:12px;height:12px}.second{position:absolute;left:4px;top:4px;z-index:1;background-color:#22c55e;width:12px;height:12px}.third{position:absolute;left:4px;top:4px;z-index:1;background-color:#1d4ed8;width:12px;height:12px}</style></head><body><section class='shell'><div class='first'></div><div class='second'></div><div class='third'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 32, 32)
expect(pixels.len()).to_equal(32 * 32)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(144)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(0)
```

</details>

#### matches Chrome leaf background opacity blending

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#f8fafc;padding:4px;width:88px;height:56px}.half{background-color:#1d4ed8;opacity:0.5;width:20px;height:12px}.zero{background-color:#ef4444;opacity:0;width:24px;height:10px;margin-top:4px}.full{background-color:#22c55e;opacity:1;width:16px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='half'></div><div class='zero'></div><div class='full'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(5776)
expect(_count_color(pixels, 0xFF8BA4EAu32)).to_equal(240)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(128)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
```

</details>

#### suppresses an opacity zero element and its entire subtree

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<html style='margin:0;padding:0;background:#fff'>" +
    "<body style='margin:0;padding:0'>" +
    "<section id='hidden' style='opacity:0;background:#ef4444;" +
    "border:2px solid #1d4ed8;width:16px;height:16px'>" +
    "<div id='child' style='background:#22c55e;width:8px;height:8px'>" +
    "hidden text</div></section></body></html>"
)
val pixels = simple_web_render_html_to_pixels(html, 32, 32)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(0)
val commands = simple_web_layout_render_html_draw_ir(
    html, 32, 32).batches[0].commands
expect(_draw_ir_command_index(commands, "hidden")).to_equal(-1)
expect(_draw_ir_command_index(commands, "child")).to_equal(-1)
val target = simple_web_layout_hit_test_target_at_time(
    "<html style='margin:0'><body style='margin:0'>" +
    "<button id='invisible-button' style='opacity:0;width:16px;" +
    "height:16px'>click</button></body></html>",
    32, 32, 4, 4, 0)
expect(target).to_equal("id:invisible-button")
```

</details>

#### matches Chrome background shorthand fallback and declaration order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background:url(hero.png) #dbeafe no-repeat;padding:4px;width:88px;height:56px}.rgb{background:rgb(34,197,94) no-repeat;width:20px;height:10px}.later-bg{background-color:#ef4444;background:#1d4ed8;width:18px;height:8px;margin-top:4px}.later-bg-color{background:#f59e0b;background-color:#334155;width:16px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='rgb'></div><div class='later-bg'></div><div class='later-bg-color'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFFDBEAFEu32)).to_equal(5672)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(200)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(144)
expect(_count_color(pixels, 0xFF334155u32)).to_equal(128)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
```

</details>

#### paints famous-site corpus block geometry with Chrome default body margin

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div data-font-corpus=\"known-site-fonts\" style='width: 120px; height: 40px; background-color: #7c3aed; font-family: \"IBM Plex Sans\", Arial, sans-serif'>Twitch commerce deterministic compatibility fixture</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 160, 120)
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[7 + 7 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[8 + 8 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[127 + 47 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[128 + 48 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[9 + 10 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[32 + 93 * 160]).to_equal(0xFFFFFFFFu32)
```

</details>

#### keeps exact Twitch corpus pixels in the fixture renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div data-font-corpus=\"known-site-fonts\" style='width: 120px; height: 40px; background-color: #7c3aed; font-family: \"IBM Plex Sans\", Arial, sans-serif'>Twitch commerce deterministic compatibility fixture</div></body></html>"
val pixels = simple_web_render_html_to_pixels_with_corpus_fixtures(html, 160, 120)
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[9 + 10 * 160]).to_equal(0xFF000000u32)
expect(pixels[52 + 14 * 160]).to_equal(0xFF4930E5u32)
expect(pixels[32 + 93 * 160]).to_equal(0xFF000000u32)
```

</details>

#### returns an RGBA byte frame from the URL facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = simple_web_render_url_to_pixels("about:network", 120, 80)
expect(pixels.len()).to_equal(120 * 80 * 4)
```

</details>

#### keeps backend choice wrapped behind the renderer interface

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SimpleWebRenderer.create_with_backend(96, 64, "software")
val pixels = renderer.render_url_to_pixels("about:blank")
expect(renderer.backend_name).to_equal("software")
expect(pixels.len()).to_equal(96 * 64)
```

</details>

#### preserves supported Engine2D backend names before runtime fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SimpleWebRenderer.create_with_backend(96, 64, "auto").backend_name).to_equal(simple_web_resolved_engine2d_backend_name(96, 64, "auto"))
expect(SimpleWebRenderer.create_with_backend(96, 64, "cuda").backend_name).to_equal("cuda")
expect(SimpleWebRenderer.create_with_backend(96, 64, "hip").backend_name).to_equal("rocm")
expect(SimpleWebRenderer.create_with_backend(96, 64, "opencl").backend_name).to_equal("opencl")
expect(SimpleWebRenderer.create_with_backend(96, 64, "vulkan").backend_name).to_equal("vulkan")
expect(SimpleWebRenderer.create_with_backend(96, 64, "metal").backend_name).to_equal("metal")
expect(SimpleWebRenderer.create_with_backend(96, 64, "cpu_simd").backend_name).to_equal("cpu_simd")
expect(SimpleWebRenderer.create_with_backend(96, 64, "simd_cpu").backend_name).to_equal("cpu_simd")
expect(simple_web_resolved_engine2d_backend_name(96, 64, "cuda")).to_equal("cuda")
expect(simple_web_resolved_engine2d_backend_name(96, 64, "hip")).to_equal("rocm")
expect(simple_web_resolved_engine2d_backend_name(96, 64, "opencl")).to_equal("opencl")
expect(simple_web_resolved_engine2d_backend_name(96, 64, "vulkan")).to_equal("vulkan")
expect(simple_web_resolved_engine2d_backend_name(96, 64, "metal")).to_equal("metal")
expect(simple_web_resolved_engine2d_backend_name(96, 64, "cpu_simd")).to_equal("cpu_simd")
```

</details>

#### high-level renderer preserves OpenCL backend selection without changing generic layout pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.box{background-color:#2563eb;width:24px;height:16px}</style></head><body><div class='box'></div></body></html>"
val sw = SimpleWebRenderer.create_with_backend(48, 32, "software")
val opencl = SimpleWebRenderer.create_with_backend(48, 32, "opencl")
expect(opencl.backend_name).to_equal("opencl")
expect(_pixels_equal(opencl.render_html_to_pixels(html), sw.render_html_to_pixels(html))).to_equal(true)
```

</details>

#### reports the actual backend after invalid backend fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SimpleWebRenderer.create_with_backend(96, 64, "not-a-backend")
val pixels = renderer.render_url_to_pixels("about:blank")
expect(renderer.backend_name).to_equal("software")
expect(pixels.len()).to_equal(96 * 64)
```

</details>

#### keeps BrowserRenderer.render_html_to_pixels on the non-empty software path

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.create(48, 32)
val html = "<html><body><div style='width:24px; height:16px; background-color:#2563eb'>Ready</div></body></html>"
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(48 * 32)
expect(_count_non_bg(result.pixel_data, 0xFFFFFFFF)).to_be_greater_than(0)
expect(result.source_html).to_equal(html)
expect(result.has_html_capture()).to_equal(true)
```

</details>

#### default renderer uses the Engine2D auto backend pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 72px; height: 32px; background-color: #44aa22'></div><span style='color:#ffffff'>Simple</span></body></html>"
val simple = SimpleWebRenderer.create(120, 80)
val browser = BrowserRenderer.create_with_backend(120, 80, simple.backend_name)
val simple_pixels = simple.render_html_to_pixels(html)
val browser_pixels = browser.render_html_to_pixels(html).pixel_data
expect(simple.backend_name).to_equal(simple_web_resolved_engine2d_backend_name(120, 80, "auto"))
expect(simple.backend_name.len()).to_be_greater_than(0)
expect(_pixels_equal(simple_pixels, browser_pixels)).to_equal(true)
```

</details>

#### web render backend pure_simple uses the Engine2D auto backend path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 64px; height: 24px; background-color: #2563eb'></div><span style='color:#ffffff'>Auto</span></body></html>"
val simple = SimpleWebRenderer.create(96, 64)
val web = WebRenderBackend.create("pure_simple", 96, 64)
val simple_pixels = simple.render_html_to_pixels(html)
val web_pixels = web.render_html_to_pixels(html)
expect(simple.backend_name).to_equal(simple_web_resolved_engine2d_backend_name(96, 64, "auto"))
expect(web.name()).to_equal("pure_simple")
expect(_pixels_equal(simple_pixels, web_pixels)).to_equal(true)
```

</details>

#### backend-isolation Gap C: WebRenderBackend can select the Engine2D backend for the core path

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# web_render_backend.spl previously hardcoded "auto" (Gap C); the
# facade now threads an optional engine2d_backend param through to
# simple_web_render_html_to_pixels_with_engine2d_backend, so a caller
# can request e.g. "cpu_simd"/"software" for the pure_simple engine.
val html = "<html><body><div style='width: 32px; height: 16px; background-color: #2563eb'></div></body></html>"
val web = WebRenderBackend.create("pure_simple", 48, 32)
val simple_software = SimpleWebRenderer.create_with_backend(48, 32, "software")

# Default (no arg) stays "auto" -- byte-identical to prior behavior.
val default_pixels = web.render_html_to_pixels(html)
val explicit_auto_pixels = web.render_html_to_pixels(html, "auto")
expect(_pixels_equal(default_pixels, explicit_auto_pixels)).to_equal(true)

# Explicit "software" selection matches the software-backed renderer,
# proving the param actually reaches the Engine2D backend selector.
val software_pixels = web.render_html_to_pixels(html, "software")
expect(_pixels_equal(software_pixels, simple_software.render_html_to_pixels(html))).to_equal(true)
```

</details>

#### backend-isolation Gap E: WebRenderBackend exposes Draw IR and CPU-layout pixel readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# wm_compare probes previously called simple_web_layout_render_html_draw_ir /
# simple_web_layout_render_html_software_pixels directly (no facade for
# that shape existed -- Gap E). WebRenderBackend now wraps both so an
# app-layer caller never needs the direct backend-engine import. Byte
# (and structure)-identical to the underlying calls -- no behavior change.
val html = "<html><body><div style='width: 40px; height: 20px; background-color: #2563eb'>Gap E</div></body></html>"
val web = WebRenderBackend.create("pure_simple", 64, 40)

val facade_ir = web.render_html_to_draw_ir(html)
val direct_ir = simple_web_layout_render_html_draw_ir(html, 64, 40)
expect(facade_ir.batches.len()).to_equal(direct_ir.batches.len())
expect(facade_ir.batches.len()).to_be_greater_than(0)
expect(facade_ir.batches[0].commands.len()).to_equal(direct_ir.batches[0].commands.len())

val facade_pixels = web.render_html_software_pixels(html)
val direct_pixels = simple_web_layout_render_html_software_pixels(html, 64, 40)
expect(_pixels_equal(facade_pixels, direct_pixels)).to_equal(true)
expect(facade_pixels.len()).to_equal(64 * 40)
```

</details>

#### fallback facade parses rgb() background-color with the shared CSS parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(5, 150, 105)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF059669u32)
```

</details>

#### fallback facade composites rgba() background-color over the white page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF808080u32)
```

</details>

#### fallback facade parses shorthand hex background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0f8'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade composites shorthand hex alpha background-color to the white page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0008'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF777777u32)
```

</details>

#### fallback facade parses named CSS background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade composites transparent background-color to the white page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: transparent'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFFFFFFFFu32)
```

</details>

#### fallback facade parses hsl() background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF008000u32)
```

</details>

#### fallback facade resolves background-color currentColor from text color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: currentColor; color: #456789'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF456789u32)
```

</details>

#### fallback facade parses color-first background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rebeccapurple no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade parses function color background shorthand before trailing tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF059669u32)
```

</details>

#### fallback facade parses fallback color after url() in background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade resolves background shorthand currentColor from text color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: currentColor no-repeat; color: #345678'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF345678u32)
```

</details>

#### fallback facade lets later background shorthand override earlier background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade lets later background-color override earlier background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: #0f8; background-color: rebeccapurple'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade applies attribute presence selectors to the first visual block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-card] { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div data-card='true'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF0E7490u32)).to_equal(96)
```

</details>

#### fallback facade rejects non matching exact attribute selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='inactive'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF4D7C0Fu32)).to_equal(0)
```

</details>

#### fallback facade applies attribute prefix selectors to the first visual block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }</style></head><body><div data-route='/app/home'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF0F5E9Cu32)).to_equal(96)
```

</details>

#### fallback facade rejects non matching attribute suffix selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings/profile'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF065F46u32)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 110 |
| Active scenarios | 110 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md`
- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`
- **Research:** `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md`


</details>
