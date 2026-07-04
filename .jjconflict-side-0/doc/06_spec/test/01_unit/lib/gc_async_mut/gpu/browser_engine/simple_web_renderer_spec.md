# Simple Web Renderer Specification

> This unit spec covers the pure-Simple web renderer path used by browser, web, and Engine2D-backed GUI surfaces. It checks HTML-to-scene conversion, HTML-to-pixel rendering, selector cascade behavior, text raster behavior, Chrome-parity matrix fixtures, static pixel caching, backend-name resolution, and corpus fixture rendering.

<!-- sdn-diagram:id=simple_web_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_renderer_spec -> std
simple_web_renderer_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 79 | 79 | 0 | 0 |

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

<details>
<summary>Rendered scenario source</summary>

> val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}#stack{display:flex;flex-flow:column wrap;width:32px;height:24px;gap:2px}.ite$width$</style></head><body><section id='stack'><div class='item'></div><div class='item'></div></section></body></html>"<br>
> val composition = simple_web_layout_render_html_draw_ir(html, 80, 48)<br>
> val batch = composition.batches[0]<br>
> val stack = _draw_ir_command_by_id(batch.commands, "stack")<br>
> <br>
> expect(_draw_ir_style_value(stack, "display")).to_equal("flex")<br>
> expect(_draw_ir_style_value(stack, "flex-direction")).to_equal("column")<br>
> expect(_draw_ir_style_value(stack, "flex-wrap")).to_equal("wrap")

</details>

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>html,body{margin:0;padding:0;width:48px;height:32px;overflow:hidden;background-color:#ffffff}#panel{display:block;content-visibility:hidden;width:24px;height:16px;background-color:#1d4ed8}#child{display:block;width:20px;height:12px;background-color:#ef4444}</style></head><body><section id='panel'><div id='child'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 48, 32)
val composition = simple_web_layout_render_html_draw_ir(html, 48, 32)
val batch = composition.batches[0]
val panel = _draw_ir_command_by_id(batch.commands, "panel")
expect(pixels.len()).to_equal(48 * 32)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
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

<details>
<summary>Rendered scenario source</summary>

> val html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.flow{background-color:#22c55e;width:18px;height:8px}.right{position:absolute;right:6px;top:6px;background-color:#1d4ed8;width:12px;height:10px}.botto$position$.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='flow'></div><div class='right'></div><div class='bottom'></div><div class='next'></div></section></body></html>"<br>
> val pixels = simple_web_render_html_to_pixels(html, 96, 64)<br>
> expect(pixels.len()).to_equal(96 * 64)<br>
> expect(_count_color(pixels, 0xFFE5E7EBu32)).to_equal(2816)<br>
> expect(_count_color(pixels, 0xFFF8FAFCu32)).to_equal(2256)<br>
> expect(_count_color(pixels, 0xFF0F172Au32)).to_equal(488)<br>
> expect(_count_color(pixels, 0xFF334155u32)).to_equal(192)<br>
> expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(144)<br>
> expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(128)<br>
> expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(120)

</details>

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

<details>
<summary>Rendered scenario source</summary>

> val html = "<html><head><style>html,body{margin:0;padding:0;width:32px;height:32px;overflow:hidden;background-color:#f8fafc}.shell{position:relative;width:32px;height:32px}.top{position:absolute;left:4px;top:4px;z-index:3;background-color:#f59e0b;width:12px;height:12px}.botto$position$.middle{position:absolute;left:4px;top:4px;z-index:2;background-color:#22c55e;width:12px;height:12px}</style></head><body><section class='shell'><div class='top'></div><div class='bottom'></div><div class='middle'></div></section></body></html>"<br>
> val pixels = simple_web_render_html_to_pixels(html, 32, 32)<br>
> expect(pixels.len()).to_equal(32 * 32)<br>
> expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(144)<br>
> expect(_count_color(pixels, 0xFF1D4ED8u32)).to_equal(0)<br>
> expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(0)

</details>

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
| Total scenarios | 79 |
| Active scenarios | 79 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md](doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)
- **Research:** [doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md](doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md)


</details>
