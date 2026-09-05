# small_element_rendering_spec

> Selected `<small>` UA sizing through Web semantics, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# small_element_rendering_spec

Selected `<small>` UA sizing through Web semantics, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/small_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<small>` UA sizing through Web semantics, Draw IR, and Engine2D.

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
    HNode, SimpleWebLayoutDrawIrResult,
    simple_web_layout_render_html_draw_ir_result
}
use test.system.browser_dom_identity_helpers.{
    system_dom_identity_index, system_dom_route
}

### Production small element rendering

#### should lower the small UA font size through Draw IR to pixels

- should lower the small UA font size through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse small as an inline body child
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: be_dom_get_tag(small_path[small_path.len() - 1]) equals `small`
- Apply the small user-agent font size
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: result.hit_index.styles[small_index].display equals `inline`
   - Expected: result.hit_index.styles[small_index].font_size equals `13`
- Lower small text to exact Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 7 expected checks
   - Expected: _small_geometry(result, "lead") equals `[0, 8, 8, 16]`
   - Expected: _small_geometry(result, "small") equals `[8, 11, 7, 13]`
   - Expected: _small_style(command, "tag") equals `small`
   - Expected: _small_style(command, "display") equals `inline`
   - Expected: _small_style(command, "font-size") equals `13`
   - Expected: [text_command.x, text_command.y] equals `[8, 11]`
   - Expected: _small_style(text_command, "font-size") equals `13`
- Rasterize absolute small-element pixels
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 5 expected checks
   - Expected: frame.skipped_command_count equals `0`
   - Expected: frame.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: frame.pixels[8 * WIDTH + 8] equals `0xFFFFFFFFu32`
   - Expected: frame.pixels[11 * WIDTH + 15] equals `0xFFFFFFFFu32`
   - Expected: frame.pixels[22 * WIDTH + 14] equals `0xFFDC2626u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower the small UA font size through Draw IR to pixels")
val html = (
    "<style>html,body{margin:0;font-size:16px;background:#ffffff}" +
    "body{padding-top:8px}</style><body id='body'>" +
    "<span id='lead'>A</span>" +
    "<small id='small' style='background:#dc2626'>B</small></body>"
)

        step("Parse small as an inline body child")
        val root = html_tree_builder_build(html)
        val identity_index = system_dom_identity_index(root)
        val body_path = be_dom_path_for_route(
            root, identity_index, system_dom_route(identity_index, "body")
        )
        val small_path = be_dom_path_for_route(
            root, identity_index, system_dom_route(identity_index, "small")
        )
        expect(small_path.len()).to_be_greater_than(1)
        expect(be_dom_get_tag(small_path[small_path.len() - 1])).to_equal("small")
        expect(small_path[small_path.len() - 2].node_id).to_equal(
            body_path[body_path.len() - 1].node_id
        )

step("Apply the small user-agent font size")
val result = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, HEIGHT
)
val small_index = _small_node_index(result.hit_index.nodes, "small")
expect(result.hit_index.styles[small_index].display).to_equal("inline")
expect(result.hit_index.styles[small_index].font_size).to_equal(13)

step("Lower small text to exact Draw IR geometry")
expect(_small_geometry(result, "lead")).to_equal([0, 8, 8, 16])
expect(_small_geometry(result, "small")).to_equal([8, 11, 7, 13])
val command = _small_command(result.composition, "small")
expect([command.x, command.y, command.width, command.height]).to_equal(
    [8, 11, 7, 13]
)
expect(_small_style(command, "tag")).to_equal("small")
expect(_small_style(command, "display")).to_equal("inline")
expect(_small_style(command, "font-size")).to_equal("13")
val text_command = _small_text_command(result.composition, "B")
expect([text_command.x, text_command.y]).to_equal([8, 11])
expect(_small_style(text_command, "font-size")).to_equal("13")

step("Rasterize absolute small-element pixels")
val raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val frame = raster.render_draw_ir_composition(result.composition, [])
raster.shutdown()
expect(frame.skipped_command_count).to_equal(0)
expect(frame.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(frame.pixels[8 * WIDTH + 8]).to_equal(0xFFFFFFFFu32)
expect(frame.pixels[11 * WIDTH + 15]).to_equal(0xFFFFFFFFu32)
expect(frame.pixels[22 * WIDTH + 14]).to_equal(0xFFDC2626u32)
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

- Canonical SPipe generation for source `cd4785bf10e3a69d061766e036efb9f7348fa71efde27bdbd7e7b92a0f692d9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd4785bf10e3a69d061766e036efb9f7348fa71efde27bdbd7e7b92a0f692d9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd4785bf10e3a69d061766e036efb9f7348fa71efde27bdbd7e7b92a0f692d9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/web_platform/html/small_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/small_element_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/small_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/small_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/small_element_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/small_element_rendering_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower the small UA font size through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/small_element_rendering_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower the small UA font size through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
