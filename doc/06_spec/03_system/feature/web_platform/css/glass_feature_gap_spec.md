# CSS Feature Admission And Fallback

> Proves that admitted comparison-page CSS crosses the existing web

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Feature Admission And Fallback

Proves that admitted comparison-page CSS crosses the existing web

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that admitted comparison-page CSS crosses the existing web
semantic/layout owner and canonical Draw IR before Engine2D pixels are read.
Unsupported backdrop sampling and transform forms remain explicit fallback
rows; this specification does not claim full CSS effects or transforms.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS effects admission and fallback

#### should lower generated pseudo content through web layout and Draw IR

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004
```

</details>

#### should preserve the explicit backdrop sampling fallback

- should preserve the explicit backdrop sampling fallback
   - Artifact capture: after_step
- Resolve the solid fallback in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read the exact solid fallback pixel through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: pixels[2 + 2 * WIDTH] equals `0xFF1F1F21u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the explicit backdrop sampling fallback")
val html = (
    "<style>html,body{{margin:0}}:root{--glass-blur:12px;" +
    "--glass-saturation:145%}#panel{width:16px;height:8px;" +
    "background:rgba(31,31,33,0.80);backdrop-filter:" +
    "blur(var(--glass-blur)) saturate(var(--glass-saturation));" +
    "box-shadow:0 8px 24px #000, 0 2px 6px #333}</style>" +
    "<div id='panel'></div>"
)

step("Resolve the solid fallback in canonical web semantic and layout state")
_expect_web_layout(html, "panel", 0, 0, 16, 8)
expect(simple_web_layout_debug_style_by_id(
    html, "panel", "background_color"
)).to_equal("4280229665")

step("Render HTML and CSS through canonical Draw IR")
val composition = _glass_composition(html)
val panel = _expect_draw_ir_rect(
    composition, "panel", 0, 0, 16, 8
)
expect(_draw_ir_style_value(panel, "backdrop-filter")).to_equal(
    "blur(12px) saturate(145%)"
)
expect(_draw_ir_style_value(
    panel, "backdrop-filter-capability"
)).to_equal("unavailable")
expect(_draw_ir_style_value(
    panel, "backdrop-filter-fallback"
)).to_equal("solid-material")
expect(_draw_ir_style_value(
    panel, "backdrop-filter-fallback-reason"
)).to_equal("cpu-raster-backdrop-sampling-unavailable")
expect(_draw_ir_style_value(
    panel, "background-color"
)).to_equal("4280229665")
expect(_draw_ir_style_value(
    panel, "background-image"
)).to_equal("none")
expect(_draw_ir_style_value(
    panel, "backdrop-filter-fallback-material-hash"
)).to_equal("")
expect(_draw_ir_style_value(
    panel, "box-shadow"
)).to_equal("0px 6px 4279834905")
expect(_draw_ir_style_value(
    panel, "box-shadow-raw"
)).to_equal("0 8px 24px #000, 0 2px 6px #333")
expect(_draw_ir_style_value(
    panel, "box-shadow-layer-count"
)).to_equal("2")
expect(_draw_ir_style_value(
    panel, "box-shadow-blur-radius"
)).to_equal("15")
expect(_contains(
    identify_missing_features(html), "backdrop-filter: blur()"
)).to_be(true)

step("Read the exact solid fallback pixel through Engine2D")
val pixels = _glass_pixels(html, composition)
expect(pixels[2 + 2 * WIDTH]).to_equal(0xFF1F1F21u32)
```

</details>

#### should lower admitted multi-layer shadows through canonical owners

- should lower admitted multi-layer shadows through canonical owners
   - Artifact capture: after_step
- Resolve the shadow box in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read one exact pixel from each shadow layer through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: pixels[10 + WIDTH] equals `0xFFDC2626u32`
   - Expected: pixels[1 + 8 * WIDTH] equals `0xFF2563EBu32`
   - Expected: pixels[2 + 2 * WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower admitted multi-layer shadows through canonical owners")
val html = (
    "<style>html,body{{margin:0}}#panel{width:8px;height:6px;" +
    "background:#fff;box-shadow:4px 0 0 #dc2626," +
    "0 4px 0 #2563eb}</style><div id='panel'></div>"
)

step("Resolve the shadow box in canonical web semantic and layout state")
_expect_web_layout(html, "panel", 0, 0, 8, 6)
expect(_contains(
    identify_missing_features(html), "box-shadow (multi-layer)"
)).to_be(false)

step("Render HTML and CSS through canonical Draw IR")
val composition = _glass_composition(html)
val panel = _expect_draw_ir_rect(
    composition, "panel", 0, 0, 8, 6
)
expect(_draw_ir_style_value(
    panel, "box-shadow-layer-count"
)).to_equal("2")
expect(_draw_ir_has_style(
    panel, "backdrop-filter-fallback-material-hash"
)).to_be(false)

step("Read one exact pixel from each shadow layer through Engine2D")
val pixels = _glass_pixels(html, composition)
expect(pixels[10 + WIDTH]).to_equal(0xFFDC2626u32)
expect(pixels[1 + 8 * WIDTH]).to_equal(0xFF2563EBu32)
expect(pixels[2 + 2 * WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

#### should lower an admitted linear gradient through canonical owners

- should lower an admitted linear gradient through canonical owners
   - Artifact capture: after_step
- Resolve gradient stops in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact gradient endpoint pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: pixels[1] equals `0xFFDC2626u32`
   - Expected: pixels[1 + 5 * WIDTH] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower an admitted linear gradient through canonical owners")
val html = (
    "<style>html,body{{margin:0}}#panel{width:8px;height:6px;" +
    "background:linear-gradient(180deg,#dc2626,#2563eb)}" +
    "</style><div id='panel'></div>"
)

step("Resolve gradient stops in canonical web semantic and layout state")
_expect_web_layout(html, "panel", 0, 0, 8, 6)
expect(_contains(
    identify_missing_features(html), "linear-gradient()"
)).to_be(false)

step("Render HTML and CSS through canonical Draw IR")
val composition = _glass_composition(html)
val panel = _expect_draw_ir_rect(
    composition, "panel", 0, 0, 8, 6
)
expect(_draw_ir_style_value(
    panel, "background-image"
)).to_equal("linear-gradient(4292617766,4280640491)")

step("Read exact gradient endpoint pixels through Engine2D")
val pixels = _glass_pixels(html, composition)
expect(pixels[1]).to_equal(0xFFDC2626u32)
expect(pixels[1 + 5 * WIDTH]).to_equal(0xFF2563EBu32)
```

</details>

#### should lower admitted pixel and percentage translations

- should lower admitted pixel and percentage translations
   - Artifact capture: after_step
- Resolve translated boxes in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact translated pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: pixel_pixels[0] equals `0xFFFFFFFFu32`
   - Expected: pixel_pixels[4 + 4 * WIDTH] equals `0xFF16A34Au32`
   - Expected: percent_pixels[0] equals `0xFFFFFFFFu32`
   - Expected: percent_pixels[5] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower admitted pixel and percentage translations")
val pixel_html = (
    "<style>html,body{{margin:0}}#panel{width:4px;height:4px;" +
    "background:#16a34a;transform:translate(4px,4px)}" +
    "</style><div id='panel'></div>"
)
val percent_html = (
    "<style>html,body{{margin:0}}#panel{width:10px;height:8px;" +
    "background:#2563eb;transform:translate(50%,0)}" +
    "</style><div id='panel'></div>"
)

step("Resolve translated boxes in canonical web semantic and layout state")
_expect_web_layout(pixel_html, "panel", 4, 4, 4, 4)
_expect_web_layout(percent_html, "panel", 5, 0, 10, 8)
expect(_contains(
    identify_missing_features(pixel_html), "transform"
)).to_be(false)
expect(_contains(
    identify_missing_features(percent_html), "transform"
)).to_be(false)

step("Render HTML and CSS through canonical Draw IR")
val pixel_composition = _glass_composition(pixel_html)
val percent_composition = _glass_composition(percent_html)
_expect_draw_ir_rect(
    pixel_composition, "panel", 4, 4, 4, 4
)
_expect_draw_ir_rect(
    percent_composition, "panel", 5, 0, 10, 8
)

step("Read exact translated pixels through Engine2D")
val pixel_pixels = _glass_pixels(pixel_html, pixel_composition)
val percent_pixels = _glass_pixels(
    percent_html, percent_composition
)
expect(pixel_pixels[0]).to_equal(0xFFFFFFFFu32)
expect(pixel_pixels[4 + 4 * WIDTH]).to_equal(0xFF16A34Au32)
expect(percent_pixels[0]).to_equal(0xFFFFFFFFu32)
expect(percent_pixels[5]).to_equal(0xFF2563EBu32)
```

</details>

#### should keep unsupported transform forms explicit and fail closed

- should keep unsupported transform forms explicit and fail closed
   - Artifact capture: after_step
- Retain unsupported transform rows in the feature ledger
   - Artifact capture: after_step
- Resolve the fallback box in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read an exact fail-closed fallback pixel through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: pixels[3 + 3 * WIDTH] equals `0xFF0F766Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep unsupported transform forms explicit and fail closed")
val rotate_html = (
    "<style>html,body{{margin:0}}#panel{width:8px;height:8px;" +
    "background:#0f766e;transform:rotate(5deg)}" +
    "</style><div id='panel'></div>"
)
val multiple_html = (
    "<style>#panel{transform:translate(4px,4px) " +
    "translateX(2px)}</style><div id='panel'></div>"
)
val unit_html = (
    "<style>#panel{transform:translate(2em,0)}</style>" +
    "<div id='panel'></div>"
)

step("Retain unsupported transform rows in the feature ledger")
expect(_contains(
    identify_missing_features(rotate_html), "transform"
)).to_be(true)
expect(_contains(
    identify_missing_features(multiple_html), "transform"
)).to_be(true)
expect(_contains(
    identify_missing_features(unit_html), "transform"
)).to_be(true)

step("Resolve the fallback box in canonical web semantic and layout state")
_expect_web_layout(rotate_html, "panel", 0, 0, 8, 8)

step("Render HTML and CSS through canonical Draw IR")
val composition = _glass_composition(rotate_html)
_expect_draw_ir_rect(composition, "panel", 0, 0, 8, 8)

step("Read an exact fail-closed fallback pixel through Engine2D")
val pixels = _glass_pixels(rotate_html, composition)
expect(pixels[3 + 3 * WIDTH]).to_equal(0xFF0F766Eu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b79a92c5b2a302d62bd0f0341a9b99d5a93ac46c39c87c5c9e16a6828af274f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b79a92c5b2a302d62bd0f0341a9b99d5a93ac46c39c87c5c9e16a6828af274f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b79a92c5b2a302d62bd0f0341a9b99d5a93ac46c39c87c5c9e16a6828af274f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/glass_feature_gap_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/glass_feature_gap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/glass_feature_gap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:135:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should lower generated pseudo content through web layout and Draw IR' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:135:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower generated pseudo content through web layout and Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:168:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the explicit backdrop sampling fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the explicit backdrop sampling fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:235:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower admitted multi-layer shadows through canonical owners' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:235:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower admitted multi-layer shadows through canonical owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:271:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower an admitted linear gradient through canonical owners' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:271:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower an admitted linear gradient through canonical owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:303:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower admitted pixel and percentage translations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl:350:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep unsupported transform forms explicit and fail closed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
