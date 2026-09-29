# label_element_rendering_spec

> Selected `<label>` UA inline flow through Web semantics, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# label_element_rendering_spec

Selected `<label>` UA inline flow through Web semantics, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/label_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<label>` UA inline flow through Web semantics, Draw IR, and Engine2D.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

## Scenarios

### Production label element rendering

#### should lower the label UA inline flow through Draw IR to pixels

- should lower the label UA inline flow through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse label with the row as its immediate parent
   - GUI capture: after_step (HTML preferred when available)
- Apply the inline label default before author CSS
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: label.hit_index.styles[label_index].display equals `inline`
   - Expected: label.hit_index.styles[label_index].bg equals `RED`
- Lower label and following text to exact inline Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 6 expected checks
   - Expected: _label_geometry(label_term) equals `[32, 8, 24, 16]`
   - Expected: _label_geometry(label_mid) equals `[32, 8, 24, 16]`
   - Expected: _label_geometry(label_right) equals `[56, 8, 40, 16]`
   - Expected: label_mid.advance_widths equals `inline_mid.advance_widths`
   - Expected: _label_style(label_term, "tag") equals `label`
   - Expected: _label_style(label_term, "display") equals `inline`
- Rasterize exact label pixels and discriminating controls
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: label_pixels.len() equals `WIDTH * HEIGHT`
   - Expected: label_pixels equals `inline_pixels`
   - Expected: label_pixels[23 * WIDTH + 55] equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 110 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower the label UA inline flow through Draw IR to pixels")
val common = (
    "<style>html,body{margin:0;padding:0;background:#fff}" +
    "body{padding-top:8px}#row{font-size:16px;color:#111827}" +
    "</style><body id='body'><div id='row'>"
)
val suffix = "</div></body>"
val label_html = (
    common + "LEFT<label id='term' style='background:#dc2626'>" +
    "MID</label>RIGHT" + suffix
)
val inline_html = (
    common + "LEFT<span id='term' style='" +
    "display:inline;background:#dc2626'>MID</span>RIGHT" + suffix
)
val block_html = (
    common + "LEFT<span id='term' style='" +
    "display:block;background:#dc2626'>MID</span>RIGHT" + suffix
)
val override_html = (
    common + "LEFT<label id='term' style='" +
    "display:block;background:#dc2626'>MID</label>RIGHT" + suffix
)

step("Parse label with the row as its immediate parent")
val root = html_tree_builder_build(label_html)
val identity_index = system_dom_identity_index(root)
val row_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "row")
)
val label_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "term")
)
expect(label_path.len()).to_be_greater_than(1)
expect(row_path.len()).to_be_greater_than(0)
expect(be_dom_get_tag(label_path[label_path.len() - 1])).to_equal(
    "label"
)
expect(label_path[label_path.len() - 2].node_id).to_equal(
    row_path[row_path.len() - 1].node_id
)

step("Apply the inline label default before author CSS")
val label = simple_web_layout_render_html_draw_ir_result(
    label_html, WIDTH, HEIGHT
)
val inline = simple_web_layout_render_html_draw_ir_result(
    inline_html, WIDTH, HEIGHT
)
val block = simple_web_layout_render_html_draw_ir_result(
    block_html, WIDTH, HEIGHT
)
val override = simple_web_layout_render_html_draw_ir_result(
    override_html, WIDTH, HEIGHT
)
val label_index = _label_node_index(label.hit_index.nodes, "term")
val override_index = _label_node_index(
    override.hit_index.nodes, "term"
)
expect(label.hit_index.styles[label_index].display).to_equal("inline")
expect(label.hit_index.styles[label_index].bg).to_equal(RED)
expect(override.hit_index.styles[override_index].display).to_equal(
    "block"
)

step("Lower label and following text to exact inline Draw IR geometry")
val label_term = _label_command(label.composition, "term")
val inline_term = _label_command(inline.composition, "term")
val block_term = _label_command(block.composition, "term")
val label_mid = _label_text_command(label.composition, "MID")
val inline_mid = _label_text_command(inline.composition, "MID")
val label_right = _label_text_command(label.composition, "RIGHT")
val inline_right = _label_text_command(inline.composition, "RIGHT")
val block_right = _label_text_command(block.composition, "RIGHT")
expect(_label_geometry(label_term)).to_equal([32, 8, 24, 16])
expect(_label_geometry(label_mid)).to_equal([32, 8, 24, 16])
expect(_label_geometry(label_right)).to_equal([56, 8, 40, 16])
expect(_label_geometry(label_term)).to_equal(
    _label_geometry(inline_term)
)
expect(_label_geometry(label_mid)).to_equal(
    _label_geometry(inline_mid)
)
expect(_label_geometry(label_right)).to_equal(
    _label_geometry(inline_right)
)
expect(_label_geometry(label_term)).not.to_equal(
    _label_geometry(block_term)
)
expect(_label_geometry(label_right)).not.to_equal(
    _label_geometry(block_right)
)
expect(label_mid.advance_widths).to_equal(inline_mid.advance_widths)
expect(label_right.advance_widths).to_equal(
    inline_right.advance_widths
)
expect(_label_style(label_term, "tag")).to_equal("label")
expect(_label_style(label_term, "display")).to_equal("inline")

step("Rasterize exact label pixels and discriminating controls")
val label_pixels = _label_pixels(label.composition)
val inline_pixels = _label_pixels(inline.composition)
val block_pixels = _label_pixels(block.composition)
val override_pixels = _label_pixels(override.composition)
expect(label_pixels.len()).to_equal(WIDTH * HEIGHT)
expect(label_pixels).to_equal(inline_pixels)
expect(label_pixels).not.to_equal(block_pixels)
expect(label_pixels).not.to_equal(override_pixels)
expect(label_pixels[23 * WIDTH + 55]).to_equal(RED)
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

- Canonical SPipe generation for source `6ce6b9eb78adfc80c02324af2dac5b380635ce3f4a091ee98b43cea7705592b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ce6b9eb78adfc80c02324af2dac5b380635ce3f4a091ee98b43cea7705592b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ce6b9eb78adfc80c02324af2dac5b380635ce3f4a091ee98b43cea7705592b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/feature/web_platform/html/label_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/label_element_rendering_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/label_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/label_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/label_element_rendering_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower the label UA inline flow through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/label_element_rendering_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower the label UA inline flow through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
