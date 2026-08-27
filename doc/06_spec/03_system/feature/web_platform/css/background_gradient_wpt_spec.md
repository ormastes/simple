# CSS Linear Gradient Rendering

> Proves the admitted two-stop vertical and horizontal linear-gradient slice

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Linear Gradient Rendering

Proves the admitted two-stop vertical and horizontal linear-gradient slice

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the admitted two-stop vertical and horizontal linear-gradient slice
through canonical web semantic/layout state, Draw IR, and Engine2D pixels.
Radial, conic, and multi-gradient stacks remain explicit fail-closed RED rows.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS gradient lowering

#### should lower a vertical two-stop linear gradient

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004
```

</details>

#### should lower a horizontal two-stop linear gradient

- should lower a horizontal two-stop linear gradient
   - Artifact capture: after_step
- Resolve horizontal stops in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: _style_value(panel, "background-layers-raw") equals ``
- Read exact horizontal endpoint pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: pixels[WIDTH] equals `0xFFDC2626u32`
   - Expected: pixels[7 + WIDTH] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower a horizontal two-stop linear gradient")
val html = _gradient_html(
    "linear-gradient(90deg,#dc2626,#2563eb)"
)

step("Resolve horizontal stops in canonical web semantic and layout state")
_expect_web_layout(html)
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_gradient_from"
)).to_equal("4292617766")
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_gradient_to"
)).to_equal("4280640491")

step("Render HTML and CSS through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(
    html, WIDTH, HEIGHT
)
val panel = _draw_ir_panel(composition)
expect(_style_value(
    panel, "background-image"
)).to_equal("linear-gradient(4292617766,4280640491)")
expect(_style_value(panel, "background-layers-raw")).to_equal("")

step("Read exact horizontal endpoint pixels through Engine2D")
val pixels = _gradient_pixels(html, composition)
expect(pixels[WIDTH]).to_equal(0xFFDC2626u32)
expect(pixels[7 + WIDTH]).to_equal(0xFF2563EBu32)
```

</details>

#### should keep radial conic and stacked gradients fail closed

- should keep radial conic and stacked gradients fail closed
   - Artifact capture: after_step
- Preserve unsupported gradient syntax in canonical web semantic state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact solid fallback pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: radial_pixels[1 + WIDTH] equals `0xFFFFFFFFu32`
   - Expected: conic_pixels[1 + WIDTH] equals `0xFFFFFFFFu32`
   - Expected: stacked_pixels[1 + WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep radial conic and stacked gradients fail closed")
val radial = _gradient_html(
    "radial-gradient(#dc2626,#2563eb)"
)
val conic = _gradient_html(
    "conic-gradient(#dc2626,#2563eb)"
)
val stacked = _gradient_html(
    "linear-gradient(#dc2626,#2563eb)," +
    "linear-gradient(#16a34a,#9333ea)"
)

step("Preserve unsupported gradient syntax in canonical web semantic state")
_expect_web_layout(radial)
_expect_web_layout(conic)
_expect_web_layout(stacked)
expect(simple_web_layout_debug_style_by_id(
    radial, "panel", "background_layers_raw"
)).to_equal("radial-gradient(#dc2626,#2563eb)")
expect(simple_web_layout_debug_style_by_id(
    conic, "panel", "background_layers_raw"
)).to_equal("conic-gradient(#dc2626,#2563eb)")
expect(simple_web_layout_debug_style_by_id(
    stacked, "panel", "background_layers_raw"
)).to_equal(
    "linear-gradient(#dc2626,#2563eb)," +
    "linear-gradient(#16a34a,#9333ea)"
)

step("Render HTML and CSS through canonical Draw IR")
val radial_composition = simple_web_layout_render_html_draw_ir(
    radial, WIDTH, HEIGHT
)
val conic_composition = simple_web_layout_render_html_draw_ir(
    conic, WIDTH, HEIGHT
)
val stacked_composition = simple_web_layout_render_html_draw_ir(
    stacked, WIDTH, HEIGHT
)
val radial_panel = _draw_ir_panel(radial_composition)
val conic_panel = _draw_ir_panel(conic_composition)
val stacked_panel = _draw_ir_panel(stacked_composition)
expect(_style_value(
    radial_panel, "background-image"
)).to_equal("none")
expect(_style_value(
    conic_panel, "background-image"
)).to_equal("none")
expect(_style_value(
    stacked_panel, "background-image"
)).to_equal("none")
expect(_style_value(
    radial_panel, "background-layers-raw"
)).to_equal("radial-gradient(#dc2626,#2563eb)")
expect(_style_value(
    conic_panel, "background-layers-raw"
)).to_equal("conic-gradient(#dc2626,#2563eb)")
expect(_style_value(
    stacked_panel, "background-layers-raw"
)).to_equal(
    "linear-gradient(#dc2626,#2563eb)," +
    "linear-gradient(#16a34a,#9333ea)"
)

step("Read exact solid fallback pixels through Engine2D")
val radial_pixels = _gradient_pixels(radial, radial_composition)
val conic_pixels = _gradient_pixels(conic, conic_composition)
val stacked_pixels = _gradient_pixels(stacked, stacked_composition)
expect(radial_pixels[1 + WIDTH]).to_equal(0xFFFFFFFFu32)
expect(conic_pixels[1 + WIDTH]).to_equal(0xFFFFFFFFu32)
expect(stacked_pixels[1 + WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b00607b3c0531b7d0a6cbe2cd895baaa4625f420c8d4ebf5c8ed89e439788094`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b00607b3c0531b7d0a6cbe2cd895baaa4625f420c8d4ebf5c8ed89e439788094`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b00607b3c0531b7d0a6cbe2cd895baaa4625f420c8d4ebf5c8ed89e439788094`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/background_gradient_wpt_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/background_gradient_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/background_gradient_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl:106:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should lower a vertical two-stop linear gradient' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower a vertical two-stop linear gradient' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower a horizontal two-stop linear gradient' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower a horizontal two-stop linear gradient' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl:176:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep radial conic and stacked gradients fail closed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl:176:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep radial conic and stacked gradients fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
