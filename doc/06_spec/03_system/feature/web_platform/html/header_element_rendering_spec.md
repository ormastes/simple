# header_element_rendering_spec

> Selected `<header>` block-default rendering through Web semantics, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# header_element_rendering_spec

Selected `<header>` block-default rendering through Web semantics, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/header_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<header>` block-default rendering through Web semantics, Draw IR, and Engine2D.

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
use test.system.browser_dom_identity_helpers.{system_dom_identity_index, system_dom_route}

### Production header element rendering

#### should lower the header block default through Draw IR to pixels

- should lower the header block default through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse header as a body child
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: be_dom_get_tag(header_path[header_path.len() - 1]) equals `header`
- Apply the header user-agent block default
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: result.hit_index.styles[header_index].display equals `block`
- Lower the header box to exact Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: _geometry(result, "header") equals `[0, 0, 40, 12]`
   - Expected: _style(command, "tag") equals `header`
   - Expected: _style(command, "display") equals `block`
- Rasterize the Draw IR header box
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: frame.skipped_command_count equals `0`
   - Expected: frame.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: frame.pixels[1 * WIDTH + 1] equals `0xFF16A34Au32`
   - Expected: frame.pixels[1 * WIDTH + 41] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

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

- Canonical SPipe generation for source `0ae9615054a626b0b71aae44be7fc84d2e4b767c69cc532917d55e3c4dec561d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ae9615054a626b0b71aae44be7fc84d2e4b767c69cc532917d55e3c4dec561d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ae9615054a626b0b71aae44be7fc84d2e4b767c69cc532917d55e3c4dec561d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/web_platform/html/header_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/header_element_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/header_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/header_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/header_element_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/header_element_rendering_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower the header block default through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/header_element_rendering_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower the header block default through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
