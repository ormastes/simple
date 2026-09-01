# blockquote_element_rendering_spec

> Selected `<blockquote>` UA-default rendering through Web semantics, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# blockquote_element_rendering_spec

Selected `<blockquote>` UA-default rendering through Web semantics, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/blockquote_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<blockquote>` UA-default rendering through Web semantics, Draw IR, and Engine2D.

## Scenarios

### Production blockquote element rendering

#### should lower blockquote UA margins through Draw IR to pixels

- should lower blockquote UA margins through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse blockquote as a body child
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: be_dom_get_tag(quote_path[quote_path.len() - 1]) equals `blockquote`
   - Expected: quote_path[quote_path.len() - 2].node_id equals `body_path[body_path.len() - 1].node_id`
- Apply selected blockquote user-agent margins
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: style.display equals `block`
   - Expected: [style.margin_l, style.margin_t, style.margin_r, style.margin_b] equals `[40, 16, 40, 16]`
- Lower the blockquote box to exact Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: _geometry(result, "quote") equals `[40, 16, 24, 8]`
   - Expected: [command.x, command.y, command.width, command.height] equals `[40, 16, 24, 8]`
   - Expected: _style(command, "tag") equals `blockquote`
   - Expected: _style(command, "display") equals `block`
- Rasterize the Draw IR blockquote box
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: frame.skipped_command_count equals `0`
   - Expected: frame.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: frame.pixels[17 * WIDTH + 41] equals `0xFF16A34Au32`
   - Expected: frame.pixels[17 * WIDTH + 39] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower blockquote UA margins through Draw IR to pixels")
val html = (
    "<style>html,body{margin:0;background:#ffffff}" +
    "blockquote{width:24px;height:8px;background:#16a34a}</style>" +
    "<body id='body'><blockquote id='quote'></blockquote></body>"
)

use std.spec.*
use common.ui.draw_ir.{DrawIrCommand, DrawIrComposition}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}
use std.gc_async_mut.gpu.browser_engine.dom_accessors.{be_dom_get_tag, be_dom_path_for_route}
use std.gc_async_mut.gpu.browser_engine.html_tree_builder.{html_tree_builder_build}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{HNode, SimpleWebLayoutDrawIrResult, simple_web_layout_render_html_draw_ir_result}
use test.system.browser_dom_identity_helpers.{system_dom_identity_index, system_dom_route}

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

- Canonical SPipe generation for source `13663917aae57f1333f5e115c43c56c4b4fb655d40311c6dc5f23efbd995faa3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13663917aae57f1333f5e115c43c56c4b4fb655d40311c6dc5f23efbd995faa3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13663917aae57f1333f5e115c43c56c4b4fb655d40311c6dc5f23efbd995faa3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/web_platform/html/blockquote_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/blockquote_element_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/blockquote_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/blockquote_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/blockquote_element_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/blockquote_element_rendering_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower blockquote UA margins through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/blockquote_element_rendering_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower blockquote UA margins through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
