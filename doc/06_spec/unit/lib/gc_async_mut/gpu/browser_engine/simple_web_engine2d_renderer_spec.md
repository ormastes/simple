# Simple Web Engine2d Renderer Specification

> Tests covering SimpleWebEngine2DRenderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2d Renderer Specification

## Scenarios

### SimpleWebEngine2DRenderer

#### returns solid background pixels without visual elements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns solid background pixels without visual elements
   - Expected: pixels.len() equals `12 * 10`
   - Expected: pixels[0] equals `0xFF123456u32`
   - Expected: pixels[119] equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns solid background pixels without visual elements")
val html = "<html><body style='background-color: #123456'></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[0]).to_equal(0xFF123456u32)
expect(pixels[119]).to_equal(0xFF123456u32)
```

</details>

#### keeps Simple Web marker off the solid-fill shortcut

- keeps Simple Web marker off the solid-fill shortcut
   - Expected: pixels.len() equals `12 * 10`
   - Expected: pixels[6 + 6 * 12] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple Web marker off the solid-fill shortcut")
val html = "<html><body style='background-color: #123456'>Simple Web</body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[6 + 6 * 12]).to_equal(0xFFFFFFFFu32)
```

</details>

#### reuses retained pixels for unchanged static html

- reuses retained pixels for unchanged static html
   - Expected: first.len() equals `12 * 10`
   - Expected: second[0] equals `0xFF123456u32`
   - Expected: cache.stores equals `1`
   - Expected: cache.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses retained pixels for unchanged static html")
val html = "<html><body style='background-color: #123456'></body></html>"
var cache = SimpleWebEngine2DStaticPixelCache.create(12, 10, "software")
val first = cache.pixels_for_html(html)
val second = cache.pixels_for_html(html)
expect(first.len()).to_equal(12 * 10)
expect(second[0]).to_equal(0xFF123456u32)
expect(cache.stores).to_equal(1)
expect(cache.hits).to_equal(1)
```

</details>

#### renders toolbar modal grid fixture with exact taskbar and image colors

- renders toolbar modal grid fixture with exact taskbar and image colors
   - Expected: pixels.len() equals `96 * 64`
   - Expected: pixels[0] equals `0xFF243447u32`
   - Expected: pixels[4 + 2 * 96] equals `0xFF22C55Eu32`
   - Expected: pixels[20 + 18 * 96] equals `0xFFEF4444u32`
   - Expected: pixels[54 + 26 * 96] equals `0xFFCBD5E1u32`
   - Expected: pixels[6 + 58 * 96] equals `0xFF8B5CF6u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders toolbar modal grid fixture with exact taskbar and image colors")
val html = "<html><body class='simple-web-engine2d-toolbar-modal-grid' style='margin:0; background-color: #0e1116'><main>toolbar modal grid</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF243447u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[20 + 18 * 96]).to_equal(0xFFEF4444u32)
expect(pixels[54 + 26 * 96]).to_equal(0xFFCBD5E1u32)
expect(pixels[6 + 58 * 96]).to_equal(0xFF8B5CF6u32)
```

</details>

#### renders dashboard command list fixture with exact chart and list colors

- renders dashboard command list fixture with exact chart and list colors
   - Expected: pixels.len() equals `96 * 64`
   - Expected: pixels[0] equals `0xFF111827u32`
   - Expected: pixels[4 + 2 * 96] equals `0xFF22C55Eu32`
   - Expected: pixels[24 + 18 * 96] equals `0xFF22C55Eu32`
   - Expected: pixels[58 + 18 * 96] equals `0xFFCBD5E1u32`
   - Expected: pixels[68 + 58 * 96] equals `0xFF10B981u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders dashboard command list fixture with exact chart and list colors")
val html = "<html><body class='simple-web-engine2d-dashboard-command-list' style='margin:0; background-color: #0b1220'><main>dashboard command list</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF111827u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[24 + 18 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[58 + 18 * 96]).to_equal(0xFFCBD5E1u32)
expect(pixels[68 + 58 * 96]).to_equal(0xFF10B981u32)
```

</details>

#### renders form sidebar validation fixture with exact navigation and validation colors

- renders form sidebar validation fixture with exact navigation and validation colors
   - Expected: pixels.len() equals `96 * 64`
   - Expected: pixels[0] equals `0xFF111827u32`
   - Expected: pixels[4 + 6 * 96] equals `0xFF2563EBu32`
   - Expected: pixels[26 + 30 * 96] equals `0xFFEF4444u32`
   - Expected: pixels[26 + 42 * 96] equals `0xFF22C55Eu32`
   - Expected: pixels[74 + 18 * 96] equals `0xFFF59E0Bu32`
   - Expected: pixels[54 + 58 * 96] equals `0xFF8B5CF6u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders form sidebar validation fixture with exact navigation and validation colors")
val html = "<html><body class='simple-web-engine2d-form-sidebar-validation' style='margin:0; background-color: #0a0f1a'><main>form sidebar validation</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF111827u32)
expect(pixels[4 + 6 * 96]).to_equal(0xFF2563EBu32)
expect(pixels[26 + 30 * 96]).to_equal(0xFFEF4444u32)
expect(pixels[26 + 42 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[74 + 18 * 96]).to_equal(0xFFF59E0Bu32)
expect(pixels[54 + 58 * 96]).to_equal(0xFF8B5CF6u32)
```

</details>

#### renders settings inspector tree fixture with exact tree and inspector colors

- renders settings inspector tree fixture with exact tree and inspector colors
   - Expected: pixels.len() equals `96 * 64`
   - Expected: pixels[0] equals `0xFF111827u32`
   - Expected: pixels[4 + 2 * 96] equals `0xFF38BDF8u32`
   - Expected: pixels[4 + 15 * 96] equals `0xFFE2E8F0u32`
   - Expected: pixels[30 + 28 * 96] equals `0xFFBFDBFEu32`
   - Expected: pixels[68 + 18 * 96] equals `0xFFF59E0Bu32`
   - Expected: pixels[76 + 58 * 96] equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders settings inspector tree fixture with exact tree and inspector colors")
val html = "<html><body class='simple-web-engine2d-settings-inspector-tree' style='margin:0; background-color: #0b1020'><main>settings inspector tree</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF111827u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF38BDF8u32)
expect(pixels[4 + 15 * 96]).to_equal(0xFFE2E8F0u32)
expect(pixels[30 + 28 * 96]).to_equal(0xFFBFDBFEu32)
expect(pixels[68 + 18 * 96]).to_equal(0xFFF59E0Bu32)
expect(pixels[76 + 58 * 96]).to_equal(0xFFEF4444u32)
```

</details>

#### renders media gallery command fixture with exact image grid and taskbar colors

- renders media gallery command fixture with exact image grid and taskbar colors
   - Expected: pixels.len() equals `96 * 64`
   - Expected: pixels[0] equals `0xFF1F2937u32`
   - Expected: pixels[4 + 2 * 96] equals `0xFF14B8A6u32`
   - Expected: pixels[7 + 17 * 96] equals `0xFF38BDF8u32`
   - Expected: pixels[37 + 17 * 96] equals `0xFFFACC15u32`
   - Expected: pixels[67 + 17 * 96] equals `0xFF22C55Eu32`
   - Expected: pixels[54 + 40 * 96] equals `0xFFA78BFAu32`
   - Expected: pixels[70 + 58 * 96] equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders media gallery command fixture with exact image grid and taskbar colors")
val html = "<html><body class='simple-web-engine2d-media-gallery-command' style='margin:0; background-color: #0f172a'><main>media gallery command</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF1F2937u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF14B8A6u32)
expect(pixels[7 + 17 * 96]).to_equal(0xFF38BDF8u32)
expect(pixels[37 + 17 * 96]).to_equal(0xFFFACC15u32)
expect(pixels[67 + 17 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[54 + 40 * 96]).to_equal(0xFFA78BFAu32)
expect(pixels[70 + 58 * 96]).to_equal(0xFFEF4444u32)
```

</details>

#### matches direct child :has selector for first block

- matches direct child :has selector for first block
   - Expected: _render_selector_color(style, "<div><span class='badge'></span></div>", 0xFF0E7490u32) is true
   - Expected: _render_selector_color(style, "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches direct child :has selector for first block")
val style = "div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }"
expect(_render_selector_color(style, "<div><span class='badge'></span></div>", 0xFF0E7490u32)).to_equal(true)
expect(_render_selector_color(style, "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleWebEngine2DRenderer.
- SimpleWebEngine2DRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `f8ff76ab8f25aca554195f52235877faafcd564ad721959fa26079c7014b589e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8ff76ab8f25aca554195f52235877faafcd564ad721959fa26079c7014b589e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8ff76ab8f25aca554195f52235877faafcd564ad721959fa26079c7014b589e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns solid background pixels without visual elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Simple Web marker off the solid-fill shortcut' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses retained pixels for unchanged static html' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
