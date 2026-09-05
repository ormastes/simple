# kbd_samp_var_rendering_spec

> Selected `<kbd>`, `<samp>`, and `<var>` UA typography through WebIR,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kbd_samp_var_rendering_spec

Selected `<kbd>`, `<samp>`, and `<var>` UA typography through WebIR,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<kbd>`, `<samp>`, and `<var>` UA typography through WebIR,
DrawIrComposition, and Engine2D.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

## Scenarios

### Production kbd samp and var rendering

#### should lower grouped UA typography through Draw IR to pixels

- should lower grouped UA typography through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse kbd samp and var as inline body children
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: be_dom_get_tag(path[path.len() - 1]) equals `component_id`
- Resolve grouped user-agent typography and author overrides
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 8 expected checks
   - Expected: kbd_style.display equals `inline`
   - Expected: samp_style.display equals `inline`
   - Expected: var_style.display equals `inline`
   - Expected: kbd_style.font_family equals `monospace`
   - Expected: samp_style.font_family equals `monospace`
   - Expected: kbd_override_style.font_family equals `sans-serif`
   - Expected: _typography_geometry(kbd) equals `_typography_geometry(mono)`
   - Expected: _typography_geometry(samp) equals `_typography_geometry(mono)`
- Emit canonical grouped typography Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 16 expected checks
   - Expected: _typography_style(kbd_box, "tag") equals `kbd`
   - Expected: _typography_style(samp_box, "tag") equals `samp`
   - Expected: _typography_style(var_box, "tag") equals `var`
   - Expected: _typography_style(kbd_box, "display") equals `inline`
   - Expected: _typography_style(kbd_box, "font-family") equals `monospace`
   - Expected: _typography_style(samp_box, "display") equals `inline`
   - Expected: _typography_style(samp_box, "font-family") equals `monospace`
   - Expected: _typography_style(var_box, "display") equals `inline`
   - Expected: _typography_style(var_box, "font-style") equals `italic`
   - Expected: _typography_style(var_text, "font-style") equals `italic`
   - Expected: kbd_text.parent_id equals `target`
   - Expected: samp_text.parent_id equals `target`
   - Expected: var_text.parent_id equals `target`
   - Expected: [kbd_text.x, kbd_text.y] equals `[0, 0]`
   - Expected: [samp_text.x, samp_text.y] equals `[0, 0]`
   - Expected: [var_text.x, var_text.y] equals `[0, 0]`
- Render grouped typography through Engine2D
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 139 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower grouped UA typography through Draw IR to pixels")
step("Parse kbd samp and var as inline body children")
val semantic_html = (
    "<body id='body'><kbd id='kbd'>K</kbd>" +
    "<samp id='samp'>S</samp><var id='var'>V</var></body>"
)
val root = html_tree_builder_build(semantic_html)
val identity_index = system_dom_identity_index(root)
val body_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "body"))
for component_id in ["kbd", "samp", "var"]:
    val path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, component_id))
    expect(path.len()).to_be_greater_than(1)
    expect(be_dom_get_tag(path[path.len() - 1])).to_equal(component_id)
    expect(path[path.len() - 2].node_id).to_equal(
        body_path[body_path.len() - 1].node_id
    )

step("Resolve grouped user-agent typography and author overrides")
val kbd = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("kbd", ""), WIDTH, HEIGHT
)
val samp = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("samp", ""), WIDTH, HEIGHT
)
val mono = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("span", "font-family:monospace"), WIDTH, HEIGHT
)
val kbd_override = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("kbd", "font-family:sans-serif"), WIDTH, HEIGHT
)
val variable = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("var", ""), WIDTH, HEIGHT
)
val italic = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("span", "font-style:italic"), WIDTH, HEIGHT
)
val var_override = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("var", "font-style:normal"), WIDTH, HEIGHT
)
val normal = simple_web_layout_render_html_draw_ir_result(
    _typography_fixture("span", "font-style:normal"), WIDTH, HEIGHT
)
val kbd_style = kbd.hit_index.styles[
    _typography_node_index(kbd.hit_index.nodes, "target")
]
val samp_style = samp.hit_index.styles[
    _typography_node_index(samp.hit_index.nodes, "target")
]
val var_style = variable.hit_index.styles[
    _typography_node_index(variable.hit_index.nodes, "target")
]
val kbd_override_style = kbd_override.hit_index.styles[
    _typography_node_index(kbd_override.hit_index.nodes, "target")
]
val var_override_style = var_override.hit_index.styles[
    _typography_node_index(var_override.hit_index.nodes, "target")
]
expect(kbd_style.display).to_equal("inline")
expect(samp_style.display).to_equal("inline")
expect(var_style.display).to_equal("inline")
expect(kbd_style.font_family).to_equal("monospace")
expect(samp_style.font_family).to_equal("monospace")
expect(var_style.font_style_italic).to_be(true)
expect(kbd_override_style.font_family).to_equal("sans-serif")
expect(var_override_style.font_style_italic).to_be(false)
expect(_typography_geometry(kbd)).to_equal(_typography_geometry(mono))
expect(_typography_geometry(samp)).to_equal(_typography_geometry(mono))
expect(_typography_geometry(variable)).to_equal(
    _typography_geometry(italic)
)

step("Emit canonical grouped typography Draw IR")
val kbd_box = _typography_command(kbd.composition, "target")
val samp_box = _typography_command(samp.composition, "target")
val var_box = _typography_command(variable.composition, "target")
val kbd_text = _typography_text_command(kbd.composition)
val samp_text = _typography_text_command(samp.composition)
val var_text = _typography_text_command(variable.composition)
val mono_text = _typography_text_command(mono.composition)
expect(_typography_style(kbd_box, "tag")).to_equal("kbd")
expect(_typography_style(samp_box, "tag")).to_equal("samp")
expect(_typography_style(var_box, "tag")).to_equal("var")
expect(_typography_style(kbd_box, "display")).to_equal("inline")
expect(_typography_style(kbd_box, "font-family")).to_equal("monospace")
expect(_typography_style(samp_box, "display")).to_equal("inline")
expect(_typography_style(samp_box, "font-family")).to_equal("monospace")
expect(_typography_style(var_box, "display")).to_equal("inline")
expect(_typography_style(var_box, "font-style")).to_equal("italic")
expect(_typography_style(kbd_text, "font-family")).to_equal(
    _typography_style(mono_text, "font-family")
)
expect(_typography_style(
    kbd_text, "font-identity"
) == "").to_be(false)
expect(_typography_style(kbd_text, "font-identity")).to_equal(
    _typography_style(mono_text, "font-identity")
)
expect(_typography_style(samp_text, "font-identity")).to_equal(
    _typography_style(mono_text, "font-identity")
)
expect(_typography_style(var_text, "font-style")).to_equal("italic")
expect(kbd_text.parent_id).to_equal("target")
expect(samp_text.parent_id).to_equal("target")
expect(var_text.parent_id).to_equal("target")
expect([kbd_text.x, kbd_text.y]).to_equal([0, 0])
expect([samp_text.x, samp_text.y]).to_equal([0, 0])
expect([var_text.x, var_text.y]).to_equal([0, 0])

step("Render grouped typography through Engine2D")
val kbd_pixels = _typography_pixels(kbd)
val samp_pixels = _typography_pixels(samp)
val mono_pixels = _typography_pixels(mono)
val kbd_override_pixels = _typography_pixels(kbd_override)
val var_pixels = _typography_pixels(variable)
val italic_pixels = _typography_pixels(italic)
val var_override_pixels = _typography_pixels(var_override)
val normal_pixels = _typography_pixels(normal)
expect(_typography_pixel_difference_count(
    kbd_pixels, mono_pixels
)).to_equal(0)
expect(_typography_pixel_difference_count(
    samp_pixels, mono_pixels
)).to_equal(0)
expect(_typography_pixel_difference_count(
    kbd_pixels, kbd_override_pixels
)).to_be_greater_than(0)
expect(_typography_pixel_difference_count(
    kbd_override_pixels, normal_pixels
)).to_equal(0)
expect(_typography_pixel_difference_count(
    var_pixels, italic_pixels
)).to_equal(0)
expect(_typography_pixel_difference_count(
    var_pixels, var_override_pixels
)).to_be_greater_than(0)
expect(_typography_pixel_difference_count(
    var_override_pixels, normal_pixels
)).to_equal(0)
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

- Canonical SPipe generation for source `bb65d916876b33288d9b2dd644a9967f7c2a3f08b9819c7ef1153bdf72885d26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb65d916876b33288d9b2dd644a9967f7c2a3f08b9819c7ef1153bdf72885d26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb65d916876b33288d9b2dd644a9967f7c2a3f08b9819c7ef1153bdf72885d26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower grouped UA typography through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower grouped UA typography through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
