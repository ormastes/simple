# Fieldset and Legend Rendering

> This system specification covers the selected deterministic `fieldset` and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fieldset and Legend Rendering

This system specification covers the selected deterministic `fieldset` and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This system specification covers the selected deterministic `fieldset` and
`legend` profile through the canonical HTML/Web layout, Draw IR, and Engine2D
path. It proves semantic parentage, selected user-agent defaults, authored CSS
override, exact component geometry, and discriminating pixels.

The selected profile uses a solid two-pixel `#767676` fieldset border because
the renderer does not model platform-themed groove colors. Generic
`inline-block` legend layout is a bounded shrink-to-content fallback. This
spec does not claim the HTML fieldset legend border cutout, special formatting
context, or form-disabled propagation.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

Requirements:
`doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`

This handwritten executable/manual pair remains evidence-blocked until an
admitted pure-Simple runner and docgen execute it.

## Scenarios

### Production fieldset and legend rendering

#### should trace selected fieldset and legend semantics to exact pixels

- should trace selected fieldset and legend semantics to exact pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse fieldset and legend as a semantic parent-child pair
   - GUI capture: after_step (HTML preferred when available)
- Apply selected user-agent defaults before authored CSS
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: fieldset_style.display equals `block`
   - Expected: legend_style.display equals `inline-block`
   - Expected: [legend_style.pad_l, legend_style.pad_r] equals `[2, 2]`
   - Expected: _geometry(ua, "ua-legend") equals `[16, 8, 9, 16]`
- Lower authored fieldset and legend boxes to exact Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 7 expected checks
   - Expected: _geometry(result, "styled") equals `[4, 4, 40, 24]`
   - Expected: _style(styled_command, "tag") equals `fieldset`
   - Expected: _style(styled_command, "border-top-width") equals `2`
   - Expected: _style(styled_command, "padding-left") equals `4`
   - Expected: _style(legend_command, "tag") equals `legend`
   - Expected: _style(legend_command, "display") equals `block`
   - Expected: _style(legend_command, "padding-left") equals `0`
- Rasterize exact component pixels against an unstyled control
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 12 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: control.skipped_command_count equals `0`
   - Expected: control.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: cleared_frame.skipped_command_count equals `0`
   - Expected: cleared_frame.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: _pixel_at(rendered.pixels, 4, 4) equals `0xFF334155u32`
   - Expected: _pixel_at(rendered.pixels, 6, 6) equals `0xFFF8FAFCu32`
   - Expected: _pixel_at(rendered.pixels, 24, 17) equals `0xFFFDE68Au32`
   - Expected: _pixel_at(rendered.pixels, 44, 4) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(control.pixels, 2, 0) equals `0xFF767676u32`
   - Expected: _pixel_at(control.pixels, 4, 2) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 194 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should trace selected fieldset and legend semantics to exact pixels")
val html = (
    "<style>html,body{margin:0;background:#ffffff}" +
    "#styled{position:absolute;left:4px;top:4px;width:40px;" +
    "height:24px;box-sizing:border-box;padding:4px;" +
    "border:2px solid #334155;background:#f8fafc}" +
    "#styled-legend{display:block;width:16px;height:8px;" +
    "padding:0;margin:0;background:#fde68a;color:#111827}</style>" +
    "<body id='body'><fieldset id='styled'>" +
    "<legend id='styled-legend'>S</legend></fieldset></body>"
)

step("Parse fieldset and legend as a semantic parent-child pair")
val semantic_root = html_tree_builder_build(html)
val semantic_index = system_dom_identity_index(semantic_root)
_expect_semantic_identity(semantic_root, semantic_index, "styled", "fieldset", "body")
_expect_semantic_identity(
    semantic_root, semantic_index, "styled-legend", "legend", "styled"
)

step("Apply selected user-agent defaults before authored CSS")
val ua_html = (
    "<style>html,body{margin:0;background:#ffffff}</style>" +
    "<body id='ua-body'>" +
    "<fieldset id='ua-fieldset'>" +
    "<legend id='ua-legend'>U</legend></fieldset></body>"
)
val ua = simple_web_layout_render_html_draw_ir_result(
    ua_html, WIDTH, HEIGHT
)
val ua_fieldset = _node_index(
    ua.hit_index.nodes, "ua-fieldset"
)
val ua_legend = _node_index(ua.hit_index.nodes, "ua-legend")
val fieldset_style = ua.hit_index.styles[ua_fieldset]
val legend_style = ua.hit_index.styles[ua_legend]
expect(fieldset_style.display).to_equal("block")
expect([
    fieldset_style.margin_l, fieldset_style.margin_r,
    fieldset_style.pad_t, fieldset_style.pad_r,
    fieldset_style.pad_b, fieldset_style.pad_l
]).to_equal([2, 2, 6, 12, 10, 12])
expect([
    fieldset_style.border_l, fieldset_style.border_t,
    fieldset_style.border_r, fieldset_style.border_b
]).to_equal([2, 2, 2, 2])
expect([
    fieldset_style.border_color_l, fieldset_style.border_color_t,
    fieldset_style.border_color_r, fieldset_style.border_color_b
]).to_equal([
    0xFF767676u32, 0xFF767676u32,
    0xFF767676u32, 0xFF767676u32
])
expect([
    fieldset_style.border_style_l,
    fieldset_style.border_style_r
]).to_equal(["solid", "solid"])
expect(legend_style.display).to_equal("inline-block")
expect([legend_style.pad_l, legend_style.pad_r]).to_equal([2, 2])
expect(_geometry(
    ua, "ua-fieldset"
)).to_equal([2, 0, 92, 36])
expect(_geometry(ua, "ua-legend")).to_equal([16, 8, 9, 16])
val clear_html = (
    "<style>html,body{margin:0;background:#ffffff}" +
    "fieldset{position:absolute;box-sizing:border-box;width:40px;" +
    "height:20px;padding:0;background:#f8fafc}" +
    "#none{left:2px;top:2px;border:none}" +
    "#zero{left:48px;top:2px;border:0}</style><body>" +
    "<fieldset id='none'></fieldset>" +
    "<fieldset id='zero'></fieldset></body>"
)
val cleared = simple_web_layout_render_html_draw_ir_result(
    clear_html, WIDTH, HEIGHT
)
val none_index = _node_index(cleared.hit_index.nodes, "none")
val zero_index = _node_index(cleared.hit_index.nodes, "zero")
expect([
    cleared.hit_index.styles[none_index].border_l,
    cleared.hit_index.styles[none_index].border_t,
    cleared.hit_index.styles[none_index].border_r,
    cleared.hit_index.styles[none_index].border_b
]).to_equal([0, 0, 0, 0])
expect([
    cleared.hit_index.styles[zero_index].border_l,
    cleared.hit_index.styles[zero_index].border_t,
    cleared.hit_index.styles[zero_index].border_r,
    cleared.hit_index.styles[zero_index].border_b
]).to_equal([0, 0, 0, 0])
expect([
    _style(_command(cleared.composition, "none"), "border-left-width"),
    _style(_command(cleared.composition, "none"), "border-top-width"),
    _style(_command(cleared.composition, "none"), "border-right-width"),
    _style(_command(cleared.composition, "none"), "border-bottom-width")
]).to_equal(["0", "0", "0", "0"])
expect([
    _style(_command(cleared.composition, "zero"), "border-left-width"),
    _style(_command(cleared.composition, "zero"), "border-top-width"),
    _style(_command(cleared.composition, "zero"), "border-right-width"),
    _style(_command(cleared.composition, "zero"), "border-bottom-width")
]).to_equal(["0", "0", "0", "0"])

step("Lower authored fieldset and legend boxes to exact Draw IR geometry")
val result = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, HEIGHT
)
val styled = _node_index(result.hit_index.nodes, "styled")
val styled_legend = _node_index(
    result.hit_index.nodes, "styled-legend"
)
expect([
    result.hit_index.styles[styled].pad_l,
    result.hit_index.styles[styled].pad_t,
    result.hit_index.styles[styled].pad_r,
    result.hit_index.styles[styled].pad_b
]).to_equal([4, 4, 4, 4])
expect([
    result.hit_index.styles[styled].border_l,
    result.hit_index.styles[styled].border_t,
    result.hit_index.styles[styled].border_r,
    result.hit_index.styles[styled].border_b
]).to_equal([2, 2, 2, 2])
expect(result.hit_index.styles[
    styled
].border_color_t).to_equal(0xFF334155u32)
expect(result.hit_index.styles[
    styled_legend
].display).to_equal("block")
expect([
    result.hit_index.styles[styled_legend].pad_l,
    result.hit_index.styles[styled_legend].pad_r
]).to_equal([0, 0])
expect(_geometry(result, "styled")).to_equal([4, 4, 40, 24])
expect(_command_geometry(
    result, "styled"
)).to_equal([4, 4, 40, 24])
expect(_geometry(
    result, "styled-legend"
)).to_equal([10, 10, 16, 8])
expect(_command_geometry(
    result, "styled-legend"
)).to_equal([10, 10, 16, 8])
val styled_command = _command(result.composition, "styled")
val legend_command = _command(
    result.composition, "styled-legend"
)
expect(_style(styled_command, "tag")).to_equal("fieldset")
expect(_style(styled_command, "border-top-width")).to_equal("2")
expect(_style(styled_command, "padding-left")).to_equal("4")
expect(_style(legend_command, "tag")).to_equal("legend")
expect(_style(legend_command, "display")).to_equal("block")
expect(_style(legend_command, "padding-left")).to_equal("0")

step("Rasterize exact component pixels against an unstyled control")
val styled_raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val rendered = styled_raster.render_draw_ir_composition(
    result.composition, []
)
styled_raster.shutdown()
val control_raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val control = control_raster.render_draw_ir_composition(
    ua.composition, []
)
control_raster.shutdown()
val cleared_raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val cleared_frame = cleared_raster.render_draw_ir_composition(
    cleared.composition, []
)
cleared_raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(control.skipped_command_count).to_equal(0)
expect(control.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(cleared_frame.skipped_command_count).to_equal(0)
expect(cleared_frame.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(_pixel_at(rendered.pixels, 4, 4)).to_equal(0xFF334155u32)
expect(_pixel_at(rendered.pixels, 6, 6)).to_equal(0xFFF8FAFCu32)
expect(_pixel_at(rendered.pixels, 24, 17)).to_equal(0xFFFDE68Au32)
expect(_pixel_at(rendered.pixels, 44, 4)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(control.pixels, 2, 0)).to_equal(0xFF767676u32)
expect(_pixel_at(control.pixels, 4, 2)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(
    cleared_frame.pixels, 2, 2
)).to_equal(0xFFF8FAFCu32)
expect(_pixel_at(
    cleared_frame.pixels, 48, 2
)).to_equal(0xFFF8FAFCu32)
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

- Canonical SPipe generation for source `f41cc1af3a3350ca6164e07e3f24fb5f2d0c55348e5a25faf0f7ce87c70ba863`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f41cc1af3a3350ca6164e07e3f24fb5f2d0c55348e5a25faf0f7ce87c70ba863`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f41cc1af3a3350ca6164e07e3f24fb5f2d0c55348e5a25faf0f7ce87c70ba863`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should trace selected fieldset and legend semantics to exact pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/fieldset_legend_rendering_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should trace selected fieldset and legend semantics to exact pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
