# Definition List Rendering

> This bounded system specification traces `dl`, `dt`, and `dd` through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Definition List Rendering

This bounded system specification traces `dl`, `dt`, and `dd` through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/definition_list_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This bounded system specification traces `dl`, `dt`, and `dd` through the
canonical HTML tree, selected user-agent defaults, Web layout, Draw IR, and
Engine2D. It covers cross-kind omitted end tags, the medium-profile `dl`
block margins, the `dd` indentation, authored overrides, exact geometry, and
discriminating component/control pixels.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

Runtime and generated-manual status remain HELD until a current-source
pure-Simple runner receipt is admitted. No execution PASS is claimed here.

## Scenarios

### Production definition list rendering

#### should trace definition-list semantics and styles to exact pixels

- should trace definition-list semantics and styles to exact pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse omitted dt and dd end tags as definition-list siblings
   - GUI capture: after_step (HTML preferred when available)
- Apply definition-list user-agent defaults before authored CSS
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: ua.hit_index.styles[ua_list].display equals `block`
   - Expected: ua.hit_index.styles[ua_term].display equals `block`
- Lower authored definition-list boxes to exact Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: _geometry(result, "list") equals `[4, 4, 64, 24]`
   - Expected: _geometry(result, "term") equals `[4, 4, 24, 8]`
- Rasterize exact definition-list pixels against a plain control
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 8 expected checks
   - Expected: frame.skipped_command_count equals `0`
   - Expected: frame.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: _pixel_at(frame.pixels, 5, 5) equals `0xFF2563EBu32`
   - Expected: _pixel_at(frame.pixels, 21, 13) equals `0xFF16A34Au32`
   - Expected: _pixel_at(frame.pixels, 60, 25) equals `0xFFFEE2E2u32`
   - Expected: _pixel_at(frame.pixels, 5, 37) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(frame.pixels, 21, 45) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(frame.pixels, 60, 57) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 106 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should trace definition-list semantics and styles to exact pixels")
step("Parse omitted dt and dd end tags as definition-list siblings")
val semantic = html_tree_builder_build(
    "<dl id='semantic'><dt id='s-term'>" +
    "<dd id='s-description'><dt id='s-next'></dl>"
)
val semantic_index = system_dom_identity_index(semantic)
_expect_parent(semantic, semantic_index, "s-term", "dt", "semantic")
_expect_parent(semantic, semantic_index, "s-description", "dd", "semantic")
_expect_parent(semantic, semantic_index, "s-next", "dt", "semantic")

step("Apply definition-list user-agent defaults before authored CSS")
val ua = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{{margin:0}}</style><body>" +
    "<dl id='ua-list'><dt id='ua-term'></dt>" +
    "<dd id='ua-description'></dd></dl></body>",
    WIDTH, HEIGHT
)
val ua_list = _node_index(ua.hit_index.nodes, "ua-list")
val ua_term = _node_index(ua.hit_index.nodes, "ua-term")
val ua_description = _node_index(
    ua.hit_index.nodes, "ua-description"
)
expect(ua.hit_index.styles[ua_list].display).to_equal("block")
expect([
    ua.hit_index.styles[ua_list].margin_t,
    ua.hit_index.styles[ua_list].margin_b
]).to_equal([16, 16])
expect(ua.hit_index.styles[ua_term].display).to_equal("block")
expect(ua.hit_index.styles[
    ua_description
].margin_l).to_equal(40)

val html = (
    "<style>html,body{margin:0;background:#ffffff}" +
    "dl{position:absolute;width:64px;height:24px;margin:0}" +
    "dt,dd{display:block;height:8px;margin:0}" +
    "#list{left:4px;top:4px;background:#fee2e2}" +
    "#term{width:24px;background:#2563eb}" +
    "#description{width:32px;margin-left:16px;background:#16a34a}" +
    "#control{left:4px;top:36px}" +
    "#control-term{width:24px}" +
    "#control-description{width:32px;margin-left:16px}</style>" +
    "<body><dl id='list'><dt id='term'></dt>" +
    "<dd id='description'></dd></dl>" +
    "<dl id='control'><dt id='control-term'></dt>" +
    "<dd id='control-description'></dd></dl></body>"
)
val result = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, HEIGHT
)
val list = _node_index(result.hit_index.nodes, "list")
val description = _node_index(
    result.hit_index.nodes, "description"
)
expect([
    result.hit_index.styles[list].margin_t,
    result.hit_index.styles[list].margin_b,
    result.hit_index.styles[description].margin_l
]).to_equal([0, 0, 16])

step("Lower authored definition-list boxes to exact Draw IR geometry")
expect(_geometry(result, "list")).to_equal([4, 4, 64, 24])
expect(_geometry(result, "term")).to_equal([4, 4, 24, 8])
expect(_geometry(
    result, "description"
)).to_equal([20, 12, 32, 8])
expect(_command_geometry(
    result.composition, "list"
)).to_equal([4, 4, 64, 24])
expect(_command_geometry(
    result.composition, "term"
)).to_equal([4, 4, 24, 8])
expect(_command_geometry(
    result.composition, "description"
)).to_equal([20, 12, 32, 8])
expect(_style(
    _command(result.composition, "list"), "tag"
)).to_equal("dl")
expect(_style(
    _command(result.composition, "term"), "tag"
)).to_equal("dt")
expect(_style(
    _command(result.composition, "description"), "tag"
)).to_equal("dd")
expect(_style(
    _command(result.composition, "description"), "margin-left"
)).to_equal("16")

step("Rasterize exact definition-list pixels against a plain control")
val raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val frame = raster.render_draw_ir_composition(
    result.composition, []
)
raster.shutdown()
expect(frame.skipped_command_count).to_equal(0)
expect(frame.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(_pixel_at(frame.pixels, 5, 5)).to_equal(0xFF2563EBu32)
expect(_pixel_at(frame.pixels, 21, 13)).to_equal(0xFF16A34Au32)
expect(_pixel_at(frame.pixels, 60, 25)).to_equal(0xFFFEE2E2u32)
expect(_pixel_at(frame.pixels, 5, 37)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(frame.pixels, 21, 45)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(frame.pixels, 60, 57)).to_equal(0xFFFFFFFFu32)
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

- Canonical SPipe generation for source `a7f9deca34d9916967e0c427a68c02c517dafe071a95ebe706e7884372fdebc8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7f9deca34d9916967e0c427a68c02c517dafe071a95ebe706e7884372fdebc8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7f9deca34d9916967e0c427a68c02c517dafe071a95ebe706e7884372fdebc8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/web_platform/html/definition_list_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/definition_list_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/definition_list_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/definition_list_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/definition_list_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/definition_list_rendering_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should trace definition-list semantics and styles to exact pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/definition_list_rendering_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should trace definition-list semantics and styles to exact pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
