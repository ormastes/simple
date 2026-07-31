# Header Element Rendering

Status: **DRAFT / EVIDENCE-BLOCKED**

Handwritten mirror of
`test/03_system/feature/web_platform/html/header_element_rendering_spec.spl`.
It is complete source reproduction, but has not been generated or validated by
SPipe docgen and does not claim qualified runtime execution.

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
| REQ-WEB-BROWSER-002 | `should lower the header block default through Draw IR to pixels` | HTML semantic parentage |
| REQ-WEB-BROWSER-004 | `should lower the header block default through Draw IR to pixels` | Web layout → `DrawIrComposition` → Engine2D |
| REQ-WEB-BROWSER-021 | `should lower the header block default through Draw IR to pixels` | Modern executable SSpec and mirrored manual |

## Scope

`header` receives its HTML user-agent `display:block` default, then follows
the canonical HTML semantic tree → Web layout → `DrawIrComposition` →
`Engine2dCompositorBackend` path. This covers the bounded `REQ-WEB-BROWSER-002`,
`004`, and `021` profile in
`doc/03_plan/sys_test/html_css_spec_traceability.md`.

## Scenario

The fixture is a marginless 64 × 32 page with a green `<header>` whose authored
size is 40 × 12.

1. **Parse header as a body child** — semantic tree parentage is `body > header`.
2. **Apply the header user-agent block default** — computed display is `block`.
3. **Lower the header box to exact Draw IR geometry** — both the layout box and
   Draw IR command are `[0,0,40,12]`, with `tag=header` and `display=block`.
4. **Rasterize the Draw IR header box** — `(1,1)` is `#16a34a`, `(41,1)` stays
   white, and no Draw IR command is skipped.

## Boundary

This bounds only the existing block default. It does not claim full HTML
sectioning semantics, accessibility-outline behavior, landmark semantics, or
qualified runner admission.

## Complete executable reproduction

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
"""Selected `<header>` block-default rendering through Web semantics, Draw IR, and Engine2D.

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

val WIDTH: i32 = 64
val HEIGHT: i32 = 32

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

describe "Production header element rendering":
    # @manual: show
    # @capture(html)
    # @capture(protocol)
    # @capture(gui)
    # @req REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
    it "should lower the header block default through Draw IR to pixels":
        val html = (
            "<style>html,body{margin:0;background:#ffffff}" +
            "header{width:40px;height:12px;background:#16a34a}</style>" +
            "<body id='body'><header id='header'></header></body>"
        )

        step("Parse header as a body child")
        val root = html_tree_builder_build(html)
        val identity_index = system_dom_identity_index(root)
        val header_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "header"))
        val body_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "body"))
        expect(header_path.len()).to_be_greater_than(1)
        expect(be_dom_get_tag(header_path[header_path.len() - 1])).to_equal("header")
        expect(header_path[header_path.len() - 2].node_id).to_equal(
            body_path[body_path.len() - 1].node_id
        )

        step("Apply the header user-agent block default")
        val result = simple_web_layout_render_html_draw_ir_result(
            html, WIDTH, HEIGHT
        )
        val header_index = _node_index(result.hit_index.nodes, "header")
        expect(result.hit_index.styles[header_index].display).to_equal("block")

        step("Lower the header box to exact Draw IR geometry")
        expect(_geometry(result, "header")).to_equal([0, 0, 40, 12])
        val command = _command(result.composition, "header")
        expect([command.x, command.y, command.width, command.height]).to_equal(
            [0, 0, 40, 12]
        )
        expect(_style(command, "tag")).to_equal("header")
        expect(_style(command, "display")).to_equal("block")

        step("Rasterize the Draw IR header box")
        val raster = Engine2dCompositorBackend.create_named(
            WIDTH, HEIGHT, "software"
        )
        val frame = raster.render_draw_ir_composition(result.composition, [])
        raster.shutdown()
        expect(frame.skipped_command_count).to_equal(0)
        expect(frame.pixels.len()).to_equal(WIDTH * HEIGHT)
        expect(frame.pixels[1 * WIDTH + 1]).to_equal(0xFF16A34Au32)
        expect(frame.pixels[1 * WIDTH + 41]).to_equal(0xFFFFFFFFu32)
```
