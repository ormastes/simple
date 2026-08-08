# Blockquote Element Rendering

Status: **DRAFT / EVIDENCE-BLOCKED**

Handwritten mirror of
`test/03_system/feature/web_platform/html/blockquote_element_rendering_spec.spl`.
It is a complete source reproduction, but has not been generated or validated
by SPipe docgen and does not claim qualified runtime execution.

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
| REQ-WEB-BROWSER-002 | `should lower blockquote UA margins through Draw IR to pixels` | HTML semantic body parentage |
| REQ-WEB-BROWSER-004 | `should lower blockquote UA margins through Draw IR to pixels` | Web layout → `DrawIrComposition` → Engine2D |
| REQ-WEB-BROWSER-021 | `should lower blockquote UA margins through Draw IR to pixels` | Modern executable SSpec and mirrored manual |

## Scope

`blockquote` receives the selected HTML user-agent block and four-side margin
defaults, then follows the canonical HTML semantic tree → Web layout →
`DrawIrComposition` → `Engine2dCompositorBackend` path. The fixture does not
override margins, so this bounded scenario does not claim author-cascade
precedence or cover REQ-WEB-BROWSER-003.

## Scenario

The fixture is an 80 × 48 marginless page with a 24 × 8 green `<blockquote>`.

1. **Parse blockquote as a body child** — semantic parentage is `body > blockquote`.
2. **Apply selected blockquote user-agent margins** — display is `block` and
   margins are `[40,16,40,16]`.
3. **Lower the blockquote box to exact Draw IR geometry** — the layout box and
   Draw IR command are `[40,16,24,8]`, with `tag=blockquote` and `display=block`.
4. **Rasterize the Draw IR blockquote box** — `(41,17)` is `#16a34a`, `(39,17)`
   remains white, and no Draw IR command is skipped.

## Boundary

This corrects only the selected UA-default profile. It does not claim author
cascade precedence, full quotation semantics, accessibility behavior, or
qualified runner admission.

## Complete executable reproduction

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
"""Selected `<blockquote>` UA-default rendering through Web semantics, Draw IR, and Engine2D."""

use std.spec.*
use common.ui.draw_ir.{DrawIrCommand, DrawIrComposition}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}
use std.gc_async_mut.gpu.browser_engine.dom_accessors.{be_dom_get_tag, be_dom_path_for_route}
use std.gc_async_mut.gpu.browser_engine.html_tree_builder.{html_tree_builder_build}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{HNode, SimpleWebLayoutDrawIrResult, simple_web_layout_render_html_draw_ir_result}
use test.system.browser_dom_identity_helpers.{system_dom_identity_index, system_dom_route}

val WIDTH: i32 = 80
val HEIGHT: i32 = 48

fn _node_index(nodes: [HNode], component_id: text) -> i32:
    var index = 0
    for node in nodes:
        if node.id_attr == component_id:
            return index
        index = index + 1
    fail("missing Web semantic node: {component_id}")
    -1

fn _command(composition: DrawIrComposition, component_id: text) -> DrawIrCommand:
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

fn _geometry(result: SimpleWebLayoutDrawIrResult, component_id: text) -> [i32]:
    val index = _node_index(result.hit_index.nodes, component_id)
    [result.hit_index.boxes.bx[index], result.hit_index.boxes.by[index], result.hit_index.boxes.bw[index], result.hit_index.boxes.bh[index]]

describe "Production blockquote element rendering":
    # @manual: show
    # @capture(html)
    # @capture(protocol)
    # @capture(gui)
    # @req REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
    it "should lower blockquote UA margins through Draw IR to pixels":
        val html = (
            "<style>html,body{margin:0;background:#ffffff}" +
            "blockquote{width:24px;height:8px;background:#16a34a}</style>" +
            "<body id='body'><blockquote id='quote'></blockquote></body>"
        )

        step("Parse blockquote as a body child")
        val root = html_tree_builder_build(html)
        val identity_index = system_dom_identity_index(root)
        val quote_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "quote"))
        val body_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "body"))
        expect(quote_path.len()).to_be_greater_than(1)
        expect(be_dom_get_tag(quote_path[quote_path.len() - 1])).to_equal("blockquote")
        expect(quote_path[quote_path.len() - 2].node_id).to_equal(body_path[body_path.len() - 1].node_id)

        step("Apply selected blockquote user-agent margins")
        val result = simple_web_layout_render_html_draw_ir_result(html, WIDTH, HEIGHT)
        val quote_index = _node_index(result.hit_index.nodes, "quote")
        val style = result.hit_index.styles[quote_index]
        expect(style.display).to_equal("block")
        expect([style.margin_l, style.margin_t, style.margin_r, style.margin_b]).to_equal([40, 16, 40, 16])

        step("Lower the blockquote box to exact Draw IR geometry")
        expect(_geometry(result, "quote")).to_equal([40, 16, 24, 8])
        val command = _command(result.composition, "quote")
        expect([command.x, command.y, command.width, command.height]).to_equal([40, 16, 24, 8])
        expect(_style(command, "tag")).to_equal("blockquote")
        expect(_style(command, "display")).to_equal("block")

        step("Rasterize the Draw IR blockquote box")
        val raster = Engine2dCompositorBackend.create_named(WIDTH, HEIGHT, "software")
        val frame = raster.render_draw_ir_composition(result.composition, [])
        raster.shutdown()
        expect(frame.skipped_command_count).to_equal(0)
        expect(frame.pixels.len()).to_equal(WIDTH * HEIGHT)
        expect(frame.pixels[17 * WIDTH + 41]).to_equal(0xFF16A34Au32)
        expect(frame.pixels[17 * WIDTH + 39]).to_equal(0xFFFFFFFFu32)
```
