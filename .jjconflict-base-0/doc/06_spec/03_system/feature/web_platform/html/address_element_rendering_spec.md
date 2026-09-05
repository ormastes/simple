# HTML address element rendering

> This bounded scenario proves the selected HTML user-agent profile for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML address element rendering

This bounded scenario proves the selected HTML user-agent profile for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/address_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This bounded scenario proves the selected HTML user-agent profile for
`address`: block layout and italic typography. Standalone
`font-style:normal` exercises the direct declaration path; adding
`visibility:visible` forces full Style reconstruction.

All variants lower through canonical Web semantics/style/layout and WebIR into
DrawIrComposition and Engine2D. Explicit italic and normal `div` controls make
the raster oracle independent of private font paths. Static review is not
runtime PASS evidence.

## Scenarios

### Production address element rendering

#### should lower address UA typography and both overrides to pixels

- should lower address UA typography and both overrides to pixels
   - Artifact capture: after_step
- Parse address as a semantic body child
   - Artifact capture: after_step
- Resolve address UA typography through both style paths
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: _address_geometry(selected) equals `[0, 0, 80, 16]`
   - Expected: _address_geometry(dispatch) equals `[0, 0, 80, 16]`
   - Expected: _address_geometry(full) equals `[0, 0, 80, 16]`
- Emit absolute address Draw IR geometry
   - Artifact capture: after_step
   - Evidence: artifact verified by 11 expected checks
   - Expected: selected_box.kind equals `rect`
   - Expected: selected_box.color equals `0xFFFEF3C7u32`
   - Expected: _address_style(selected_box, "tag") equals `address`
   - Expected: _address_style(selected_box, "display") equals `block`
   - Expected: _address_style(selected_box, "font-style") equals `italic`
   - Expected: _address_style(dispatch_box, "font-style") equals `normal`
   - Expected: _address_style(full_box, "font-style") equals `normal`
   - Expected: [selected_text.x, selected_text.y] equals `[0, 0]`
   - Expected: _address_style(selected_text, "font-style") equals `italic`
   - Expected: _address_style(dispatch_text, "font-style") equals `normal`
   - Expected: _address_style(full_text, "font-style") equals `normal`
- Rasterize address typography with exact pixel controls
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 106 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower address UA typography and both overrides to pixels")
step("Parse address as a semantic body child")
val semantic = html_tree_builder_build(
    "<body id='body'><address id='target'>A</address></body>"
)
val body_path = be_dom_find_path_to_id(semantic, "body")
val address_path = be_dom_find_path_to_id(semantic, "target")
expect(address_path.len()).to_be_greater_than(1)
expect(be_dom_get_tag(address_path[address_path.len() - 1])).to_equal(
    "address"
)
expect(address_path[address_path.len() - 2].node_id).to_equal(
    body_path[body_path.len() - 1].node_id
)

step("Resolve address UA typography through both style paths")
val selected = simple_web_layout_render_html_draw_ir_result(
    _address_fixture("address", ""), ADDRESS_WIDTH, ADDRESS_HEIGHT
)
val italic = simple_web_layout_render_html_draw_ir_result(
    _address_fixture("div", "font-style:italic"),
    ADDRESS_WIDTH, ADDRESS_HEIGHT
)
val dispatch = simple_web_layout_render_html_draw_ir_result(
    _address_fixture("address", "font-style:normal"),
    ADDRESS_WIDTH, ADDRESS_HEIGHT
)
val full = simple_web_layout_render_html_draw_ir_result(
    _address_fixture(
        "address", "font-style:normal;visibility:visible"
    ),
    ADDRESS_WIDTH, ADDRESS_HEIGHT
)
val normal = simple_web_layout_render_html_draw_ir_result(
    _address_fixture("div", "font-style:normal"),
    ADDRESS_WIDTH, ADDRESS_HEIGHT
)
val selected_index = _address_node_index(
    selected.hit_index.nodes, "target"
)
val dispatch_index = _address_node_index(
    dispatch.hit_index.nodes, "target"
)
val full_index = _address_node_index(full.hit_index.nodes, "target")
expect(selected.hit_index.styles[selected_index].display).to_equal(
    "block"
)
expect(
    selected.hit_index.styles[selected_index].font_style_italic
).to_be(true)
expect(
    dispatch.hit_index.styles[dispatch_index].font_style_italic
).to_be(false)
expect(full.hit_index.styles[full_index].font_style_italic).to_be(false)
expect(_address_geometry(selected)).to_equal([0, 0, 80, 16])
expect(_address_geometry(dispatch)).to_equal([0, 0, 80, 16])
expect(_address_geometry(full)).to_equal([0, 0, 80, 16])

step("Emit absolute address Draw IR geometry")
val selected_box = _address_command(selected.composition, "target")
val dispatch_box = _address_command(dispatch.composition, "target")
val full_box = _address_command(full.composition, "target")
expect([
    selected_box.x, selected_box.y,
    selected_box.width, selected_box.height
]).to_equal([0, 0, 80, 16])
expect(selected_box.kind).to_equal("rect")
expect(selected_box.color).to_equal(0xFFFEF3C7u32)
expect(_address_style(selected_box, "tag")).to_equal("address")
expect(_address_style(selected_box, "display")).to_equal("block")
expect(_address_style(selected_box, "font-style")).to_equal("italic")
expect(_address_style(dispatch_box, "font-style")).to_equal("normal")
expect(_address_style(full_box, "font-style")).to_equal("normal")
val selected_text = _address_text_command(selected.composition)
val dispatch_text = _address_text_command(dispatch.composition)
val full_text = _address_text_command(full.composition)
expect([selected_text.x, selected_text.y]).to_equal([0, 0])
expect(_address_style(selected_text, "font-style")).to_equal("italic")
expect(_address_style(dispatch_text, "font-style")).to_equal("normal")
expect(_address_style(full_text, "font-style")).to_equal("normal")

step("Rasterize address typography with exact pixel controls")
val selected_pixels = _address_pixels(selected)
val italic_pixels = _address_pixels(italic)
val dispatch_pixels = _address_pixels(dispatch)
val full_pixels = _address_pixels(full)
val normal_pixels = _address_pixels(normal)
expect(selected_pixels[15 * ADDRESS_WIDTH + 79]).to_equal(
    0xFFFEF3C7u32
)
expect(selected_pixels[18 * ADDRESS_WIDTH + 1]).to_equal(
    0xFFFFFFFFu32
)
expect(_address_pixel_difference_count(
    selected_pixels, italic_pixels
)).to_equal(0)
expect(_address_pixel_difference_count(
    dispatch_pixels, normal_pixels
)).to_equal(0)
expect(_address_pixel_difference_count(
    full_pixels, normal_pixels
)).to_equal(0)
expect(_address_pixel_difference_count(
    selected_pixels, dispatch_pixels
)).to_be_greater_than(0)
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
- `REQ-WEB-BROWSER-002`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ba43eca0868d93b22f4b612048fd701872a7679ada287ffadad3819a5771da5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ba43eca0868d93b22f4b612048fd701872a7679ada287ffadad3819a5771da5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ba43eca0868d93b22f4b612048fd701872a7679ada287ffadad3819a5771da5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/html/address_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/address_element_rendering_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/html/address_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/address_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/address_element_rendering_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/web_platform/html/address_element_rendering_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower address UA typography and both overrides to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/address_element_rendering_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower address UA typography and both overrides to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
