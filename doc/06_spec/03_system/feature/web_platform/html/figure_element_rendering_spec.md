# Figure Element Rendering

Status: **DRAFT / EVIDENCE-BLOCKED**

Handwritten complete mirror of
`test/03_system/feature/web_platform/html/figure_element_rendering_spec.spl`.
The source and manual are structurally complete, but the known unavailable
qualified pure-Simple runner prevents runtime execution and admitted docgen.

| Metadata | Value |
|---|---|
| Tests | 1 |
| Active | 1 |
| Stubs | 0 (static source audit) |
| Manual provenance | Handwritten complete mirror; docgen pending |
| Runtime provenance | Pending admitted pure-Simple runner |

## Requirement mapping

| Requirement | Executable scenario | Coverage |
|---|---|---|
| REQ-WEB-BROWSER-002 | `should lower figure UA margins through Draw IR to pixels` | HTML semantic body parentage |
| REQ-WEB-BROWSER-004 | `should lower figure UA margins through Draw IR to pixels` | Web layout → `DrawIrComposition` → Engine2D |
| REQ-WEB-BROWSER-021 | `should lower figure UA margins through Draw IR to pixels` | Modern executable SSpec and complete mirrored manual |

## Scope

`figure` receives the selected HTML user-agent block and four-side margin
defaults, then follows the canonical HTML semantic tree → Web layout →
`DrawIrComposition` → `Engine2dCompositorBackend` path. The fixture does not
override margins, so this bounded scenario does not claim author-cascade
precedence, caption placement, accessibility behavior, aggregate conformance,
or qualified runtime execution.

## Scenario

The fixture is an 80 × 48 marginless page with a 24 × 8 green `<figure>`.

1. **Parse figure as a body child** — semantic parentage is `body > figure`.
2. **Apply selected figure user-agent margins** — display is `block` and
   margins are `[40,16,40,16]`.
3. **Lower the figure box to exact Draw IR geometry** — the layout box and
   Draw IR command are `[40,16,24,8]`, with `tag=figure` and `display=block`.
4. **Rasterize the Draw IR figure box** — `(41,17)` is `#16a34a`, `(39,17)`
   remains white, and no Draw IR command is skipped.

## Boundary

This corrects only the selected UA-default profile. `figcaption` remains a
normal block child; special figure/caption semantics, full HTML/CSS
conformance, admitted docgen, and qualified execution remain open.

## Complete executable reproduction

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
"""Selected `<figure>` UA-default rendering through Web semantics, Draw IR, and Engine2D.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`
"""

use std.spec.*
use common.ui.draw_ir.{DrawIrCommand, DrawIrComposition}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}
use std.gc_async_mut.gpu.browser_engine.dom_accessors.{
    be_dom_get_tag, be_dom_path_for_route
}
use std.gc_async_mut.gpu.browser_engine.html_tree_builder.{
    html_tree_builder_build
}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{
    HNode, SimpleWebLayoutDrawIrResult,
    simple_web_layout_render_html_draw_ir_result
}
use test.system.browser_dom_identity_helpers.{system_dom_identity_index, system_dom_route}

val WIDTH: i32 = 80
val HEIGHT: i32 = 48

fn _figure_html() -> text:
    (
        "<style>html,body{margin:0;background:#ffffff}" +
        "figure{width:24px;height:8px;background:#16a34a}</style>" +
        "<body id='body'><figure id='figure'></figure></body>"
    )

fn _node_index(nodes: [HNode], component_id: text) -> i32:
    var index = 0
    for node in nodes:
        if node.id_attr == component_id:
            return index
        index = index + 1
    fail("missing Web semantic node: {component_id}")
    -1

fn _command(
    composition: DrawIrComposition, component_id: text
) -> DrawIrCommand:
    for batch in composition.batches:
        for command in batch.commands:
            if command.component_id == component_id:
                return command
    fail("missing Draw IR command: {component_id}")
    composition.batches[0].commands[0]

fn _style(command: DrawIrCommand, key: text) -> text:
    for property in command.computed_style:
        if property.key == key:
            return property.value
    fail("missing Draw IR computed style: {key}")
    ""

fn _geometry(
    result: SimpleWebLayoutDrawIrResult, component_id: text
) -> [i32]:
    val index = _node_index(result.hit_index.nodes, component_id)
    [
        result.hit_index.boxes.bx[index], result.hit_index.boxes.by[index],
        result.hit_index.boxes.bw[index], result.hit_index.boxes.bh[index]
    ]

fn _check_figure_semantics(html: text):
    val root = html_tree_builder_build(html)
    val identity_index = system_dom_identity_index(root)
    val figure_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "figure"))
    val body_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "body"))
    expect(figure_path.len()).to_be_greater_than(1)
    expect(be_dom_get_tag(figure_path[figure_path.len() - 1])).to_equal(
        "figure"
    )
    expect(figure_path[figure_path.len() - 2].node_id).to_equal(
        body_path[body_path.len() - 1].node_id
    )

fn _check_figure_ua_style(result: SimpleWebLayoutDrawIrResult):
    val figure_index = _node_index(result.hit_index.nodes, "figure")
    val style = result.hit_index.styles[figure_index]
    expect(style.display).to_equal("block")
    expect([
        style.margin_l, style.margin_t, style.margin_r, style.margin_b
    ]).to_equal([40, 16, 40, 16])

fn _check_figure_draw_ir(result: SimpleWebLayoutDrawIrResult):
    expect(_geometry(result, "figure")).to_equal([40, 16, 24, 8])
    val command = _command(result.composition, "figure")
    expect([
        command.x, command.y, command.width, command.height
    ]).to_equal([40, 16, 24, 8])
    expect(_style(command, "tag")).to_equal("figure")
    expect(_style(command, "display")).to_equal("block")

fn _check_figure_pixels(result: SimpleWebLayoutDrawIrResult):
    val raster = Engine2dCompositorBackend.create_named(
        WIDTH, HEIGHT, "software"
    )
    val frame = raster.render_draw_ir_composition(result.composition, [])
    raster.shutdown()
    expect(frame.skipped_command_count).to_equal(0)
    expect(frame.pixels.len()).to_equal(WIDTH * HEIGHT)
    expect(frame.pixels[17 * WIDTH + 41]).to_equal(0xFF16A34Au32)
    expect(frame.pixels[17 * WIDTH + 39]).to_equal(0xFFFFFFFFu32)

describe "Production figure element rendering":
    # @manual: show
    # @capture(html)
    # @capture(protocol)
    # @capture(gui)
    # @req REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
    it "should lower figure UA margins through Draw IR to pixels":
        val html = _figure_html()

        step("Parse figure as a body child")
        _check_figure_semantics(html)

        step("Apply selected figure user-agent margins")
        val result = simple_web_layout_render_html_draw_ir_result(
            html, WIDTH, HEIGHT
        )
        _check_figure_ua_style(result)

        step("Lower the figure box to exact Draw IR geometry")
        _check_figure_draw_ir(result)

        step("Rasterize the Draw IR figure box")
        _check_figure_pixels(result)
```
