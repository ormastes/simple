# code_element_rendering_spec

> Selected `<code>` UA monospace rendering through WebIR, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# code_element_rendering_spec

Selected `<code>` UA monospace rendering through WebIR, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/code_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<code>` UA monospace rendering through WebIR, Draw IR, and Engine2D.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

## Scenarios

### Production code element rendering

#### should lower the code UA monospace face through Draw IR to pixels

- should lower the code UA monospace face through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse code as an inline body child
   - GUI capture: after_step (HTML preferred when available)
- Resolve the code user-agent monospace family
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 5 expected checks
   - Expected: selected_style.display equals `inline`
   - Expected: selected_style.font_family equals `monospace`
   - Expected: explicit_style.font_family equals `monospace`
   - Expected: override_style.font_family equals `sans-serif`
   - Expected: _code_geometry(selected) equals `_code_geometry(explicit)`
- Emit canonical code text Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 5 expected checks
   - Expected: _code_style(selected_box, "tag") equals `code`
   - Expected: _code_style(selected_box, "display") equals `inline`
   - Expected: _code_style(selected_box, "font-family") equals `monospace`
   - Expected: selected_text.parent_id equals `target`
   - Expected: [selected_text.x, selected_text.y] equals `[0, 0]`
- Render monospace code through Engine2D
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 91 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower the code UA monospace face through Draw IR to pixels")
val default_html = _code_fixture("code", "")
val explicit_html = _code_fixture("span", "monospace")
val override_html = _code_fixture("code", "sans-serif")
val normal_html = _code_fixture("span", "sans-serif")

step("Parse code as an inline body child")
val root = html_tree_builder_build(default_html)
val identity_index = system_dom_identity_index(root)
val body_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "body")
)
val code_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "target")
)
expect(be_dom_get_tag(
    code_path[code_path.len() - 1]
)).to_equal("code")
expect(code_path[
    code_path.len() - 2
].node_id).to_equal(body_path[body_path.len() - 1].node_id)

step("Resolve the code user-agent monospace family")
val selected = simple_web_layout_render_html_draw_ir_result(
    default_html, WIDTH, HEIGHT
)
val explicit = simple_web_layout_render_html_draw_ir_result(
    explicit_html, WIDTH, HEIGHT
)
val overridden = simple_web_layout_render_html_draw_ir_result(
    override_html, WIDTH, HEIGHT
)
val normal = simple_web_layout_render_html_draw_ir_result(
    normal_html, WIDTH, HEIGHT
)
val selected_style = selected.hit_index.styles[
    _code_node_index(selected.hit_index.nodes, "target")
]
val explicit_style = explicit.hit_index.styles[
    _code_node_index(explicit.hit_index.nodes, "target")
]
val override_style = overridden.hit_index.styles[
    _code_node_index(overridden.hit_index.nodes, "target")
]
expect(selected_style.display).to_equal("inline")
expect(selected_style.font_family).to_equal("monospace")
expect(explicit_style.font_family).to_equal("monospace")
expect(override_style.font_family).to_equal("sans-serif")
expect(_code_geometry(selected)).to_equal(_code_geometry(explicit))
expect(
    _code_geometry(selected)[2] == _code_geometry(overridden)[2]
).to_be(false)

step("Emit canonical code text Draw IR")
val selected_box = _code_command(selected.composition, "target")
val selected_text = _code_text_command(selected.composition)
val explicit_text = _code_text_command(explicit.composition)
val override_text = _code_text_command(overridden.composition)
expect(_code_style(selected_box, "tag")).to_equal("code")
expect(_code_style(selected_box, "display")).to_equal("inline")
expect(_code_style(selected_box, "font-family")).to_equal("monospace")
expect(selected_text.parent_id).to_equal("target")
expect([selected_text.x, selected_text.y]).to_equal([0, 0])
expect(_code_style(
    selected_text, "font-family"
)).to_equal(_code_style(explicit_text, "font-family"))
expect(_code_style(
    selected_text, "font-identity"
) == "").to_be(false)
expect(_code_style(
    selected_text, "font-identity"
)).to_equal(_code_style(explicit_text, "font-identity"))
expect(_code_style(
    selected_text, "font-identity"
) == _code_style(override_text, "font-identity")).to_be(false)

step("Render monospace code through Engine2D")
val selected_pixels = _code_pixels(selected)
val explicit_pixels = _code_pixels(explicit)
val override_pixels = _code_pixels(overridden)
val normal_pixels = _code_pixels(normal)
expect(_code_pixel_difference_count(
    selected_pixels, explicit_pixels
)).to_equal(0)
expect(_code_pixel_difference_count(
    selected_pixels, override_pixels
)).to_be_greater_than(0)
expect(_code_pixel_difference_count(
    override_pixels, normal_pixels
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

- Canonical SPipe generation for source `54584a58335aa8d33e902db15b23dca858f189a211b21f04f623cf262b389d68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54584a58335aa8d33e902db15b23dca858f189a211b21f04f623cf262b389d68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54584a58335aa8d33e902db15b23dca858f189a211b21f04f623cf262b389d68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/feature/web_platform/html/code_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/code_element_rendering_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/code_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/code_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/code_element_rendering_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower the code UA monospace face through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/code_element_rendering_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower the code UA monospace face through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
