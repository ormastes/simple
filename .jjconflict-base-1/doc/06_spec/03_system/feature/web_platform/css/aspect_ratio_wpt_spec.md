# CSS `aspect-ratio` Canonical Rendering

> Mirrored manual for `test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl`.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

| Manual status | Value |
|-------|-------|
| Source | `test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl` |
| Docgen | Pending — no admitted pure-Simple runner provenance is available |
| Runtime result | Not executed |

## Scope

This scenario proves a bounded production path for CSS `aspect-ratio`: a
width-led `2 / 1` box and height-led `1 / 2` box pass through canonical HTML
layout, `DrawIrComposition`, and Engine2D. It does not claim general CSS or
qualified runtime execution.

## Requirement traceability

- `REQ-WEB-BROWSER-003`: resolves the selected CSS declarations into 32×16 and
  12×24 layout boxes.
- `REQ-WEB-BROWSER-004`: lowers those boxes through canonical Draw IR and
  Engine2D without skipped commands.
- `REQ-WEB-BROWSER-021`: supplies the executable modern SSpec and this mirror.

## Scenario

### should resolve width-led and height-led ratios through Engine2D

1. **Resolve width-led and height-led ratios in canonical web layout**
   - `#wide` resolves authored `width:32px; aspect-ratio:2 / 1` to 32×16.
   - `#tall` resolves authored `height:24px; aspect-ratio:1 / 2` to 12×24.
2. **Retain both ratio boxes in canonical HTML semantics and Draw IR**
   - Draw IR source is `html_ast`.
   - `wide` geometry is `[0,0,32,16]`, `tall` geometry is `[0,16,12,24]`.
   - Computed Draw IR styles retain `2 / 1` and `1 / 2` respectively.
3. **Render ratio-resolved Draw IR through the canonical Engine2D backend**
   - No commands are skipped.
   - The exact blue and red component-pixel counts are 512 and 288.

## Evidence boundary

This is a handwritten mirror pending `simple spipe-docgen`. A qualified
pure-Simple runner and its provenance remain required before doc generation or
treating it as runtime PASS.

## Complete executable scenario reproduction

Runnable source: `test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl`.

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
"""# CSS `aspect-ratio` Canonical Rendering

This bounded scenario exercises the production HTML/CSS path for both width-led
and height-led aspect ratios: HTML semantics, resolved layout, Draw IR, and
Engine2D pixels. It is source/spec/manual evidence only until an admitted
pure-Simple runner executes it.
"""

use std.spec.*
use std.common.ui.draw_ir.{DrawIrCommand}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{
    SimpleWebLayoutDrawIrResult,
    simple_web_layout_debug_layout_by_id,
    simple_web_layout_render_html_draw_ir_result
}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}

val ASPECT_RATIO_HTML = (
    "<style>html,body{margin:0}" +
    "#wide{display:block;width:32px;aspect-ratio:2 / 1;" +
    "background-color:#2563eb}" +
    "#tall{display:block;height:24px;aspect-ratio:1 / 2;" +
    "background-color:#dc2626}</style>" +
    "<div id='wide'></div><div id='tall'></div>"
)

fn _aspect_command(
    result: SimpleWebLayoutDrawIrResult, component_id: text
) -> DrawIrCommand:
    for command in result.composition.batches[0].commands:
        if command.component_id == component_id:
            return command
    fail("missing aspect-ratio Draw IR command: {component_id}")
    result.composition.batches[0].commands[0]

fn _aspect_style(command: DrawIrCommand, key: text) -> text:
    for property in command.computed_style:
        if property.key == key:
            return property.value
    fail("missing aspect-ratio style: {key}")
    ""

fn _aspect_color_count(pixels: [u32], color: u32) -> i32:
    var count = 0
    for pixel in pixels:
        if pixel == color:
            count = count + 1
    count

describe "REQ-WEB-BROWSER-003/004/021: CSS aspect-ratio":
    # @manual: show
    # @capture(html)
    # @capture(artifact)
    it "should resolve width-led and height-led ratios through Engine2D":
        step("Resolve width-led and height-led ratios in canonical web layout")
        expect(simple_web_layout_debug_layout_by_id(
            ASPECT_RATIO_HTML, 64, 64, "wide", "w"
        )).to_equal("32")
        expect(simple_web_layout_debug_layout_by_id(
            ASPECT_RATIO_HTML, 64, 64, "wide", "h"
        )).to_equal("16")
        expect(simple_web_layout_debug_layout_by_id(
            ASPECT_RATIO_HTML, 64, 64, "tall", "w"
        )).to_equal("12")
        expect(simple_web_layout_debug_layout_by_id(
            ASPECT_RATIO_HTML, 64, 64, "tall", "h"
        )).to_equal("24")

        step("Retain both ratio boxes in canonical HTML semantics and Draw IR")
        val result = simple_web_layout_render_html_draw_ir_result(
            ASPECT_RATIO_HTML, 64, 64
        )
        val wide = _aspect_command(result, "wide")
        val tall = _aspect_command(result, "tall")
        expect(result.composition.batches[0].source.source_kind).to_equal("html_ast")
        expect([wide.x, wide.y, wide.width, wide.height]).to_equal([0, 0, 32, 16])
        expect([tall.x, tall.y, tall.width, tall.height]).to_equal([0, 16, 12, 24])
        expect(_aspect_style(wide, "aspect-ratio")).to_equal("2 / 1")
        expect(_aspect_style(tall, "aspect-ratio")).to_equal("1 / 2")

        step("Render ratio-resolved Draw IR through the canonical Engine2D backend")
        val raster = Engine2dCompositorBackend.create_named(64, 64, "software")
        val rendered = raster.render_draw_ir_composition(
            result.composition, []
        )
        raster.shutdown()
        expect(rendered.skipped_command_count).to_equal(0)
        expect(_aspect_color_count(rendered.pixels, 0xFF2563EBu32)).to_equal(512)
        expect(_aspect_color_count(rendered.pixels, 0xFFDC2626u32)).to_equal(288)
```
