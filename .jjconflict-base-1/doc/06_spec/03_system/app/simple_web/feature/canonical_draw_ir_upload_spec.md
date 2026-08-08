# Canonical Simple Web Draw IR Upload

Status: **DRAFT / EVIDENCE-BLOCKED**

Handwritten complete mirror of
`test/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.spl`.
Static review is possible; qualified pure-Simple execution and docgen remain
pending.

| Metadata | Value |
|---|---|
| Tests | 1 |
| Active | 1 |
| Stubs | 0 (static source audit) |
| Runtime provenance | Not claimed |

## Requirement mapping

| Requirement | Coverage |
|---|---|
| REQ-WEB-BROWSER-001 | No browser-private Draw IR painter on the upload route |
| REQ-WEB-BROWSER-004 | One WebIR composition reaches canonical Engine2D execution |
| REQ-WEB-BROWSER-021 | Modern executable SSpec and complete mirrored manual |

## Scenario

1. **Build one canonical web composition** — Web layout emits one structured
   `html-layout` composition containing the exact blue 40 × 12 panel.
2. **Submit it through the upload route** — the composition stays byte-for-byte
   identical and exactly two canonical submissions occur: upload oracle and
   comparison frame.
3. **Read back the selected Engine2D frame** — the actual Engine2D result
   receipt records the selected `cpu` Draw IR plan, `cpu_mirror` readback,
   `html-layout` composition, zero skips, and 2,048 pixels.
4. **Match structured Draw IR and exact pixels** — every pixel is checked:
   exactly 480 pixels inside `[0,0,40,12]` are `#2563eb` and the remaining
   1,568 pixels are white.

## Boundary

This scenario proves the software upload-bound WebIR/DrawIR route, its actual
Engine2D comparison receipt, and its bounded per-sample call count. It does not
claim a physical GPU device readback or that the requested backend string alone
is selection evidence.

## Complete executable reproduction

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-001 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
"""Canonical Simple Web Draw IR upload routing.

The upload-bound route must execute the exact WebIR-produced
`DrawIrComposition` through Engine2D. It must not reconstruct pixels through a
browser-private painter before selecting the Engine2D frame.
"""

use std.spec.*
use common.ui.draw_ir.{DrawIrCommand, DrawIrComposition}
use common.ui.draw_ir_sdn.{draw_ir_to_sdn}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{
    simple_web_layout_render_html_draw_ir
}
use std.gc_async_mut.gpu.browser_engine.simple_web_layout_engine2d_fast.{
    web_draw_ir_gpu_route_canonical_submission_count,
    web_draw_ir_gpu_route_last_comparison_receipt,
    web_draw_ir_gpu_route_last_evidence,
    web_draw_ir_gpu_route_policy_consult_count,
    web_draw_ir_gpu_route_policy_reset,
    web_draw_ir_gpu_route_sample
}

val WIDTH: i32 = 64
val HEIGHT: i32 = 32

fn _command(
    composition: DrawIrComposition, component_id: text
) -> DrawIrCommand:
    for batch in composition.batches:
        for command in batch.commands:
            if command.component_id == component_id:
                return command
    fail("missing Draw IR command: {component_id}")
    composition.batches[0].commands[0]

fn setup_canonical_upload_fixture() -> DrawIrComposition:
    val html = (
        "<style>html,body{margin:0;background:#ffffff}" +
        "#panel{width:40px;height:12px;background:#2563eb}</style>" +
        "<body><div id='panel'></div></body>"
    )
    val composition = simple_web_layout_render_html_draw_ir(
        html, WIDTH, HEIGHT)
    expect(composition.composition_id).to_equal("html-layout")
    expect(composition.scene_key).to_equal("simple-web-html-layout")
    val panel = _command(composition, "panel")
    expect([
        panel.x, panel.y, panel.width, panel.height
    ]).to_equal([0, 0, 40, 12])
    expect(panel.color).to_equal(0xFF2563EBu32)
    composition

fn check_same_composition_submitted(
    composition: DrawIrComposition
) -> [u32]:
    val structured_before = draw_ir_to_sdn(composition)
    web_draw_ir_gpu_route_policy_reset()
    val pixels = web_draw_ir_gpu_route_sample(
        composition, WIDTH, HEIGHT, "software")
    expect(draw_ir_to_sdn(composition)).to_equal(structured_before)
    expect(web_draw_ir_gpu_route_policy_consult_count()).to_equal(1)
    # One canonical Engine2D upload oracle plus one canonical comparison frame.
    expect(web_draw_ir_gpu_route_canonical_submission_count()).to_equal(2)
    pixels

fn check_backend_receipt_selected():
    val receipt = web_draw_ir_gpu_route_last_comparison_receipt()
    expect(receipt).to_start_with(
        "backend=cpu;source=cpu_mirror;composition_id=html-layout;")
    expect(receipt).to_contain(";skipped=0;pixels=2048")
    val evidence = web_draw_ir_gpu_route_last_evidence()
    expect(evidence.sample_count).to_equal(1)
    expect(evidence.commands_complete).to_equal(true)
    expect(evidence.pixels_match).to_equal(true)

fn check_upload_pixels_exact(pixels: [u32]):
    expect(pixels.len()).to_equal(WIDTH * HEIGHT)
    var blue_count = 0
    var white_count = 0
    var y = 0
    while y < HEIGHT:
        var x = 0
        while x < WIDTH:
            val expected = if x < 40 and y < 12:
                0xFF2563EBu32
            else:
                0xFFFFFFFFu32
            expect(pixels[y * WIDTH + x]).to_equal(expected)
            if expected == 0xFF2563EBu32:
                blue_count = blue_count + 1
            else:
                white_count = white_count + 1
            x = x + 1
        y = y + 1
    expect(blue_count).to_equal(40 * 12)
    expect(white_count).to_equal(WIDTH * HEIGHT - 40 * 12)

describe "Simple Web canonical Draw IR upload":
    # @manual: show
    # @capture(html)
    # @capture(protocol)
    # @capture(gui)
    # @req REQ-WEB-BROWSER-001 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-021
    it "should submit the WebIR composition once per measured Engine2D lane":
        step("Build one canonical web composition")
        val composition = setup_canonical_upload_fixture()

        step("Submit it through the upload route")
        val pixels = check_same_composition_submitted(composition)

        step("Read back the selected Engine2D frame")
        check_backend_receipt_selected()

        step("Match structured Draw IR and exact pixels")
        check_upload_pixels_exact(pixels)
```
