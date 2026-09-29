# mark_element_rendering_spec

> Selected `<mark>` UA highlighting through Web semantics, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mark_element_rendering_spec

Selected `<mark>` UA highlighting through Web semantics, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/mark_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<mark>` UA highlighting through Web semantics, Draw IR, and Engine2D.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

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
    HNode, simple_web_layout_render_html_draw_ir_result
}
use test.system.browser_dom_identity_helpers.{
    system_dom_identity_index, system_dom_route
}

### Production mark element rendering

#### should lower the mark UA highlight through Draw IR to pixels

- should lower the mark UA highlight through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse mark with the row as its immediate parent
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: be_dom_get_tag(mark_path[mark_path.len() - 1]) equals `mark`
- Apply inline yellow and black mark defaults before author CSS
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: mark.hit_index.styles[mark_index].display equals `inline`
   - Expected: mark.hit_index.styles[mark_index].bg equals `YELLOW`
   - Expected: mark.hit_index.styles[mark_index].fg equals `BLACK`
- Lower mark and following text to exact inline Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 6 expected checks
   - Expected: _mark_geometry(mark_term) equals `[32, 8, 24, 16]`
   - Expected: _mark_geometry(mark_mid) equals `[32, 8, 24, 16]`
   - Expected: _mark_geometry(mark_right) equals `[56, 8, 40, 16]`
   - Expected: _mark_geometry(mark_mid) equals `_mark_geometry(span_mid)`
   - Expected: mark_mid.advance_widths equals `span_mid.advance_widths`
   - Expected: _mark_style(mark_term, "display") equals `inline`
- Rasterize the exact mark highlight and discriminating controls
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: mark_pixels.len() equals `WIDTH * HEIGHT`
   - Expected: mark_pixels equals `span_pixels`
   - Expected: mark_pixels[23 * WIDTH + 55] equals `YELLOW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 128 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower the mark UA highlight through Draw IR to pixels")
val common = (
    "<style>html,body{margin:0;padding:0;background:#fff}" +
    "body{padding-top:8px}#row{font-size:16px;color:#111827}" +
    "</style><body id='body'><div id='row'>"
)
val suffix = "</div></body>"
val mark_html = (
    common + "LEFT<mark id='term'>MID</mark>RIGHT" + suffix
)
val styled_span_html = (
    common + "LEFT<span id='term' style='" +
    "display:inline;background:#ffff00;color:#000'>MID</span>" +
    "RIGHT" + suffix
)
val block_html = (
    common + "LEFT<span id='term' style='" +
    "display:block;background:#ffff00;color:#000'>MID</span>" +
    "RIGHT" + suffix
)
val transparent_html = (
    common + "LEFT<span id='term'>MID</span>RIGHT" + suffix
)
val override_html = (
    common + "LEFT<mark id='term' style='" +
    "display:block;background:#2563eb;color:#fff'>MID</mark>" +
    "RIGHT" + suffix
)

step("Parse mark with the row as its immediate parent")
val root = html_tree_builder_build(mark_html)
val identity_index = system_dom_identity_index(root)
val row_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "row")
)
val mark_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "term")
)
expect(mark_path.len()).to_be_greater_than(1)
expect(row_path.len()).to_be_greater_than(0)
expect(be_dom_get_tag(mark_path[mark_path.len() - 1])).to_equal("mark")
expect(mark_path[mark_path.len() - 2].node_id).to_equal(
    row_path[row_path.len() - 1].node_id
)

step("Apply inline yellow and black mark defaults before author CSS")
val mark = simple_web_layout_render_html_draw_ir_result(
    mark_html, WIDTH, HEIGHT
)
val styled_span = simple_web_layout_render_html_draw_ir_result(
    styled_span_html, WIDTH, HEIGHT
)
val block = simple_web_layout_render_html_draw_ir_result(
    block_html, WIDTH, HEIGHT
)
val transparent = simple_web_layout_render_html_draw_ir_result(
    transparent_html, WIDTH, HEIGHT
)
val override = simple_web_layout_render_html_draw_ir_result(
    override_html, WIDTH, HEIGHT
)
val mark_index = _mark_node_index(mark.hit_index.nodes, "term")
val override_index = _mark_node_index(
    override.hit_index.nodes, "term"
)
expect(mark.hit_index.styles[mark_index].display).to_equal("inline")
expect(mark.hit_index.styles[mark_index].bg).to_equal(YELLOW)
expect(mark.hit_index.styles[mark_index].fg).to_equal(BLACK)
expect(override.hit_index.styles[override_index].display).to_equal(
    "block"
)
expect(override.hit_index.styles[override_index].bg).to_equal(
    0xFF2563EBu32
)
expect(override.hit_index.styles[override_index].fg).to_equal(
    0xFFFFFFFFu32
)

        step("Parse mark with the row as its immediate parent")
        val root = html_tree_builder_build(mark_html)
        val identity_index = system_dom_identity_index(root)
        val row_path = be_dom_path_for_route(
            root, identity_index, system_dom_route(identity_index, "row")
        )
        val mark_path = be_dom_path_for_route(
            root, identity_index, system_dom_route(identity_index, "term")
        )
        expect(mark_path.len()).to_be_greater_than(1)
        expect(row_path.len()).to_be_greater_than(0)
        expect(be_dom_get_tag(mark_path[mark_path.len() - 1])).to_equal("mark")
        expect(mark_path[mark_path.len() - 2].node_id).to_equal(
            row_path[row_path.len() - 1].node_id
        )

step("Rasterize the exact mark highlight and discriminating controls")
val mark_pixels = _mark_pixels(mark.composition)
val span_pixels = _mark_pixels(styled_span.composition)
val block_pixels = _mark_pixels(block.composition)
val transparent_pixels = _mark_pixels(transparent.composition)
expect(mark_pixels.len()).to_equal(WIDTH * HEIGHT)
expect(mark_pixels).to_equal(span_pixels)
expect(mark_pixels).not.to_equal(block_pixels)
expect(mark_pixels).not.to_equal(transparent_pixels)
expect(mark_pixels[23 * WIDTH + 55]).to_equal(YELLOW)
val yellow_count = _mark_color_count(mark_pixels, YELLOW)
expect(yellow_count).to_be_greater_than(0)
expect(yellow_count).to_equal(
    _mark_color_count(span_pixels, YELLOW)
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `592ea31560567138a5c4b6999764c1fc1fb6812a157bf172fab8048b4badd5e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `592ea31560567138a5c4b6999764c1fc1fb6812a157bf172fab8048b4badd5e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `592ea31560567138a5c4b6999764c1fc1fb6812a157bf172fab8048b4badd5e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/feature/web_platform/html/mark_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/mark_element_rendering_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/mark_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/mark_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/mark_element_rendering_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower the mark UA highlight through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/mark_element_rendering_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower the mark UA highlight through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
