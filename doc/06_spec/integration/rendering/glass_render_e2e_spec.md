# Glass Render E2e Specification

> Tests covering Glass Theme End-to-End Rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Render E2e Specification

## Scenarios

### Glass Theme End-to-End Rendering

#### glass_dark theme

#### generates non-empty HTML

- generates non-empty HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates non-empty HTML")
val html = generate_glass_test_html("glass_dark")
expect(html.len()).to_be_greater_than(100)
# Should contain key structural elements
expect(html).to_contain("glass-window")
expect(html).to_contain("glass-titlebar")
expect(html).to_contain("widget-button")
```

</details>

#### renders to non-empty pixel buffer

- renders to non-empty pixel buffer
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result.format equals `pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders to non-empty pixel buffer")
val html = generate_glass_test_html("glass_dark")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result.format).to_equal("pixels")
```

</details>

#### pixels contain dark background colors

- pixels contain dark background colors
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pixels contain dark background colors")
val html = generate_glass_test_html("glass_dark")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
# Dark background is #0A0A0F -> 0xFF0A0A0F in ARGB
# Check first row for dark pixels (within tolerance of 30)
val dark_bg: u32 = 0xFF0A0A0F
val dark_count = count_pixels_near(result.pixel_data, 0, W, dark_bg, 30)
# At least some pixels in the first row should be near the bg color
expect(dark_count).to_be_greater_than(0)
```

</details>

#### pixels contain glass accent blue

- pixels contain glass accent blue
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pixels contain glass accent blue")
val html = generate_glass_test_html("glass_dark")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
# iOS blue accent #007AFF -> 0xFF007AFF or #0A84FF -> 0xFF0A84FF
# Search full buffer for blue accent pixels (tolerance 40)
val blue1: u32 = 0xFF007AFF
val blue2: u32 = 0xFF0A84FF
val blue_count_1 = count_pixels_near(result.pixel_data, 0, PIXEL_COUNT, blue1, 40)
val blue_count_2 = count_pixels_near(result.pixel_data, 0, PIXEL_COUNT, blue2, 40)
val total_blue = blue_count_1 + blue_count_2
# At least some accent-blue pixels should be present (buttons, dock, etc.)
expect(total_blue).to_be_greater_than(0)
```

</details>

#### glass_light theme

#### renders to non-empty pixel buffer

- renders to non-empty pixel buffer
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result.format equals `pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders to non-empty pixel buffer")
val html = generate_glass_test_html("glass_light")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result.format).to_equal("pixels")
```

</details>

#### light theme differs from dark theme

- light theme differs from dark theme
   - Expected: dark_result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: light_result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("light theme differs from dark theme")
val dark_html = generate_glass_test_html("glass_dark")
val light_html = generate_glass_test_html("glass_light")
var renderer_d = BrowserRenderer.create(W, H)
var renderer_l = BrowserRenderer.create(W, H)
val dark_result = renderer_d.render_html_to_pixels(dark_html)
val light_result = renderer_l.render_html_to_pixels(light_html)
expect(dark_result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(light_result.pixel_data.len()).to_equal(PIXEL_COUNT)
# They should NOT be identical — different backgrounds and colors
val cmp = compare_pixel_buffers(
    dark_result.pixel_data, light_result.pixel_data, W, H, 0)
# Match should be below 50% (very different themes)
expect(cmp.match_percentage).to_be_less_than(5000)
```

</details>

#### rendering stress test

<details>
<summary>Advanced: stress test renders without crash</summary>

#### stress test renders without crash

- stress test renders without crash
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result.format equals `pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stress test renders without crash")
val html = build_rendering_stress_html()
expect(html.len()).to_be_greater_than(100)
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result.format).to_equal("pixels")
```

</details>


</details>

<details>
<summary>Advanced: stress test produces varied pixels</summary>

#### stress test produces varied pixels

- stress test produces varied pixels
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stress test produces varied pixels")
val html = build_rendering_stress_html()
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
# Should have multiple distinct colors (gradients, overlapping alpha, etc.)
val unique = count_unique_colors(result.pixel_data, 50)
# Stress test has gradients/alpha/text — should have many colors
expect(unique).to_be_greater_than(3)
```

</details>


</details>

#### float vs int effect engine rendering

#### both engines produce non-empty output for glass_dark

- both engines produce non-empty output for glass_dark
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true
   - Expected: int_cap.pixels.len() equals `PIXEL_COUNT`
   - Expected: float_cap.pixels.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("both engines produce non-empty output for glass_dark")
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
expect(int_cap.pixels.len()).to_equal(PIXEL_COUNT)
expect(float_cap.pixels.len()).to_equal(PIXEL_COUNT)
```

</details>

#### float and int engines produce similar output

- float and int engines produce similar output
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("float and int engines produce similar output")
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
# Compare with per-channel threshold of 3
val result = compare_pixel_buffers(
    int_cap.pixels, float_cap.pixels, W, H, 3)
# match_percentage is 0-10000 (100.00% * 100)
# 99.50% = 9950
expect(result.match_percentage).to_be_greater_than(9949)
```

</details>

#### deterministic rendering

#### same HTML renders identically twice

- same HTML renders identically twice
   - Expected: result1.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result2.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: cmp.match_percentage equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("same HTML renders identically twice")
val html = generate_glass_test_html("glass_dark")
var renderer1 = BrowserRenderer.create(W, H)
var renderer2 = BrowserRenderer.create(W, H)
val result1 = renderer1.render_html_to_pixels(html)
val result2 = renderer2.render_html_to_pixels(html)
expect(result1.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result2.pixel_data.len()).to_equal(PIXEL_COUNT)
# Exact match — deterministic software rendering
val cmp = compare_exact(result1.pixel_data, result2.pixel_data, W, H)
expect(cmp.match_percentage).to_equal(10000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/glass_render_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Glass Theme End-to-End Rendering.
- Glass Theme End-to-End Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `66f3435a0a18428abdbc90171a6e291e73af78040fef5450a22c30093ce1728e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66f3435a0a18428abdbc90171a6e291e73af78040fef5450a22c30093ce1728e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66f3435a0a18428abdbc90171a6e291e73af78040fef5450a22c30093ce1728e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/rendering/glass_render_e2e_spec.spl
mirror: doc/06_spec/integration/rendering/glass_render_e2e_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/glass_render_e2e_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/integration/rendering/glass_render_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/glass_render_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/glass_render_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/glass_render_e2e_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates non-empty HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/glass_render_e2e_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders to non-empty pixel buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/glass_render_e2e_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pixels contain dark background colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
