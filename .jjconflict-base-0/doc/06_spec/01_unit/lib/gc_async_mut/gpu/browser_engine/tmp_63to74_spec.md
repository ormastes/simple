# Tmp 63to74 Specification

> Tests covering BrowserRenderer HTML rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp 63to74 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### paints inline background shorthand fallback colors after url tokens

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- paints inline background shorthand fallback colors after url tokens
   - Expected: _scene_has_fill_color(html, 0xFF00FF88u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints inline background shorthand fallback colors after url tokens")
val html = "<html><body><div style='width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### paints style block background shorthand fallback colors after url tokens

- paints style block background shorthand fallback colors after url tokens
   - Expected: _scene_has_fill_color(html, 0xFF00FF88u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints style block background shorthand fallback colors after url tokens")
val html = "<html><head><style>.card { width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### resolves background-color currentColor from the computed text color

- resolves background-color currentColor from the computed text color
   - Expected: _scene_has_fill_color(html, 0xFF123456u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves background-color currentColor from the computed text color")
val html = "<html><body><div style='width: 80px; height: 40px; color: #123456; background-color: currentColor'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF123456u32)).to_equal(true)
```

</details>

#### resolves background shorthand currentColor from the computed text color

- resolves background shorthand currentColor from the computed text color
   - Expected: _scene_has_fill_color(html, 0xFF345678u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves background shorthand currentColor from the computed text color")
val html = "<html><body><div style='width: 80px; height: 40px; color: #345678; background: currentColor no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF345678u32)).to_equal(true)
```

</details>

#### resolves inline currentColor backgrounds even when color is declared later

- resolves inline currentColor backgrounds even when color is declared later
   - Expected: _scene_has_fill_color(html, 0xFF456789u32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves inline currentColor backgrounds even when color is declared later")
val html = "<html><body><div style='width: 80px; height: 40px; background-color: currentColor; color: #456789'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF456789u32)).to_equal(true)
```

</details>

#### resolves style block currentColor backgrounds from rule color

- resolves style block currentColor backgrounds from rule color
   - Expected: _scene_has_fill_color(html, 0xFF56789Au32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves style block currentColor backgrounds from rule color")
val html = "<html><head><style>.card { width: 80px; height: 40px; background-color: currentColor; color: #56789a; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF56789Au32)).to_equal(true)
```

</details>

#### resolves style block currentColor backgrounds after later matched color rules

- resolves style block currentColor backgrounds after later matched color rules
   - Expected: _scene_has_fill_color(html, 0xFF6789ABu32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves style block currentColor backgrounds after later matched color rules")
val html = "<html><head><style>.card { width: 80px; height: 40px; background-color: currentColor; } .card { color: #6789ab; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF6789ABu32)).to_equal(true)
```

</details>

#### resolves CSS custom properties from style blocks

- resolves CSS custom properties from style blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves CSS custom properties from style blocks")
val blue_html = "<html><head><style>:root { --theme-panel: #0000ff; } body { margin: 0; background-color: #ffffff; } .card { width: 100px; height: 50px; background-color: var(--theme-panel); }</style></head><body><div class='card'></div></body></html>"
val green_html = "<html><head><style>:root { --theme-panel: #00ff00; } body { margin: 0; background-color: #ffffff; } .card { width: 100px; height: 50px; background-color: var(--theme-panel); }</style></head><body><div class='card'></div></body></html>"
val blue = render_html_to_pixels_with_viewport(blue_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
assert_not_equal(_pixel_signature(blue), _pixel_signature(green))
```

</details>

#### renders the glass style body fixture

- renders the glass style body fixture
   - Expected: pixels.len() equals `TEST_WIDTH * TEST_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders the glass style body fixture")
val html = "<html><head><style>body { margin: 0; background-color: #101820; color: #f3f4f6; } .panel { width: 120px; height: 70px; background-color: #1f2937; }</style></head><body><div class='panel'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### is deterministic for repeated renders of the same HTML

- is deterministic for repeated renders of the same HTML
   - Expected: _pixel_signature(first) equals `_pixel_signature(second)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is deterministic for repeated renders of the same HTML")
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #22aa44'></div></body></html>"
val first = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val second = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(_pixel_signature(first)).to_equal(_pixel_signature(second))
```

</details>

#### uses the same pixels as an explicit Engine2D software renderer

- uses the same pixels as an explicit Engine2D software renderer
   - Expected: default_renderer.engine == nil is true
   - Expected: software_renderer.engine == nil is false
   - Expected: default_renderer.backend_name() equals `software`
   - Expected: software_renderer.backend_name() equals `software`
   - Expected: _pixels_equal(default_pixels, software_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the same pixels as an explicit Engine2D software renderer")
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #2050a0'></div><span style='color:#ffffff'>Hi</span></body></html>"
val default_renderer = BrowserRenderer.create(TEST_WIDTH, TEST_HEIGHT)
val software_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val default_pixels = default_renderer.render_html_to_pixels(html).pixel_data
val software_pixels = software_renderer.render_html_to_pixels(html).pixel_data
expect(default_renderer.engine == nil).to_equal(true)
expect(software_renderer.engine == nil).to_equal(false)
expect(default_renderer.backend_name()).to_equal("software")
expect(software_renderer.backend_name()).to_equal("software")
expect(_pixels_equal(default_pixels, software_pixels)).to_equal(true)
```

</details>

#### reports deterministic software for unknown backend fallback

- reports deterministic software for unknown backend fallback
   - Expected: renderer.engine == nil is true
   - Expected: renderer.backend_name() equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports deterministic software for unknown backend fallback")
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "not-a-backend")
expect(renderer.engine == nil).to_equal(true)
expect(renderer.backend_name()).to_equal("software")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer HTML rendering.
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a368c0fc25ebb21732fa8a7c35d32dfb2cd1eb45aa57219aeb21bed6bb21803b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a368c0fc25ebb21732fa8a7c35d32dfb2cd1eb45aa57219aeb21bed6bb21803b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a368c0fc25ebb21732fa8a7c35d32dfb2cd1eb45aa57219aeb21bed6bb21803b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints inline background shorthand fallback colors after url tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints style block background shorthand fallback colors after url tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_63to74_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves background-color currentColor from the computed text color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
