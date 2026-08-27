# Production GUI/Web Renderer Parity Hardening Specification

> Verifies selected Feature C and NFR C renderer parity and GPU/browser evidence taxonomy contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/Web Renderer Parity Hardening Specification

Verifies selected Feature C and NFR C renderer parity and GPU/browser evidence taxonomy contracts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/simple_web_browser_production_hardening.md |
| Source | `test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C renderer parity and GPU/browser evidence
taxonomy contracts.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-013, REQ-WEB-HARD-014, NFR-WEB-HARD-009, NFR-WEB-HARD-012

## Scenarios

### production GUI web renderer parity hardening

#### generated common.ui widget HTML

#### uses real GUI widget HTML without legacy fixture markers

- uses real GUI widget HTML without legacy fixture markers
   - Expected: html does not contain `data-simple-actual-gui-button`
   - Expected: html does not contain `simple-web-engine2d-`
   - Expected: html does not contain `data-font-corpus="known-site-fonts"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-HARD-013
# @req REQ-WEB-HARD-014
# @req REQ-SSPEC-SYSTEM
step("uses real GUI widget HTML without legacy fixture markers")
val html = generated_gui_widget_html()
expect(html).to_contain("widget-button")
expect(html).to_contain("widget-image")
expect(html).to_contain("data-action=\"run_production_gui\"")
expect(html.contains("data-simple-actual-gui-button")).to_equal(false)
expect(html.contains("simple-web-engine2d-")).to_equal(false)
expect(html.contains("data-font-corpus=\"known-site-fonts\"")).to_equal(false)
```

</details>

#### Simple Web Renderer backends

#### renders marker-free widget HTML to a non-empty framebuffer

- renders marker-free widget HTML to a non-empty framebuffer
   - Expected: report.has_widget_html is true
   - Expected: report.has_legacy_fixture_marker is false
   - Expected: report.software_pixel_count equals `96 * 72`
   - Expected: report.timing_budget_status equals `pass`
   - Expected: report.timing_budget_reason equals `within-render-budget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders marker-free widget HTML to a non-empty framebuffer")
val report = run_generated_gui_widget_backend_parity(96, 72)
expect(report.has_widget_html).to_equal(true)
expect(report.has_legacy_fixture_marker).to_equal(false)
expect(report.software_pixel_count).to_equal(96 * 72)
expect(report.distinct_software_colors).to_be_greater_than(3)
expect(report.html_build_elapsed_us).to_be_greater_than(0)
expect(report.software_render_elapsed_us).to_be_greater_than(0)
expect(report.cpu_simd_render_elapsed_us).to_be_greater_than(0)
expect(report.metal_render_elapsed_us).to_be_greater_than(0)
expect(report.total_elapsed_us).to_be_greater_than(0)
expect(report.software_pixels_per_second).to_be_greater_than(0)
expect(report.cpu_simd_pixels_per_second).to_be_greater_than(0)
expect(report.metal_pixels_per_second).to_be_greater_than(0)
expect(report.total_pixels_per_second).to_be_greater_than(0)
expect(report.timing_budget_us).to_be_greater_than(0)
expect(report.timing_budget_status).to_equal("pass")
expect(report.timing_budget_reason).to_equal("within-render-budget")
```

</details>

#### matches CPU SIMD backend pixels exactly

- matches CPU SIMD backend pixels exactly
   - Expected: report.cpu_simd_resolved_backend equals `cpu_simd`
   - Expected: report.cpu_simd_pixel_count equals `96 * 72`
   - Expected: report.cpu_simd_different_pixels equals `0`
   - Expected: report.cpu_simd_match_percentage equals `10000`
   - Expected: report.cpu_simd_max_channel_diff equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches CPU SIMD backend pixels exactly")
val report = run_generated_gui_widget_backend_parity(96, 72)
expect(report.cpu_simd_resolved_backend).to_equal("cpu_simd")
expect(report.cpu_simd_pixel_count).to_equal(96 * 72)
expect(report.cpu_simd_different_pixels).to_equal(0)
expect(report.cpu_simd_match_percentage).to_equal(10000)
expect(report.cpu_simd_max_channel_diff).to_equal(0)
```

</details>

#### matches Metal backend pixels exactly with no tolerance

- matches Metal backend pixels exactly with no tolerance
   - Expected: report.metal_resolved_backend equals `metal`
   - Expected: report.metal_resolved_backend equals `software`
   - Expected: report.tolerance_used is false
   - Expected: report.metal_pixel_count equals `96 * 72`
   - Expected: report.metal_different_pixels equals `0`
   - Expected: report.metal_match_percentage equals `10000`
   - Expected: report.metal_max_channel_diff equals `0`
   - Expected: report.exact_backend_parity is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches Metal backend pixels exactly with no tolerance")
val report = run_generated_gui_widget_backend_parity(96, 72)
if is_macos():
    expect(report.metal_resolved_backend).to_equal("metal")
else:
    expect(report.metal_resolved_backend).to_equal("software")
expect(report.tolerance_used).to_equal(false)
expect(report.metal_pixel_count).to_equal(96 * 72)
expect(report.metal_different_pixels).to_equal(0)
expect(report.metal_match_percentage).to_equal(10000)
expect(report.metal_max_channel_diff).to_equal(0)
expect(report.exact_backend_parity).to_equal(true)
```

</details>

#### backend-executed reduced GUI widget scene

#### executes real CPU SIMD drawing operations with exact software parity

- executes real CPU SIMD drawing operations with exact software parity
   - Expected: report.software_resolved_backend equals `software`
   - Expected: report.cpu_simd_resolved_backend equals `cpu_simd`
   - Expected: report.software_pixel_count equals `16 * 16`
   - Expected: report.cpu_simd_pixel_count equals `16 * 16`
   - Expected: report.cpu_simd_different_pixels equals `0`
   - Expected: report.cpu_simd_max_channel_diff equals `0`
   - Expected: report.tolerance_used is false
   - Expected: report.timing_budget_status equals `pass`
   - Expected: report.timing_budget_reason equals `within-render-budget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes real CPU SIMD drawing operations with exact software parity")
val report = run_backend_executed_gui_widget_scene_parity(16, 16)
expect(report.software_resolved_backend).to_equal("software")
expect(report.cpu_simd_resolved_backend).to_equal("cpu_simd")
expect(report.software_pixel_count).to_equal(16 * 16)
expect(report.cpu_simd_pixel_count).to_equal(16 * 16)
expect(report.cpu_simd_different_pixels).to_equal(0)
expect(report.cpu_simd_max_channel_diff).to_equal(0)
expect(report.cpu_simd_total_hits).to_be_greater_than(0)
expect(report.cpu_simd_fill_hits).to_be_greater_than(0)
expect(report.tolerance_used).to_equal(false)
expect(report.software_render_elapsed_us).to_be_greater_than(0)
expect(report.cpu_simd_render_elapsed_us).to_be_greater_than(0)
expect(report.metal_render_elapsed_us).to_be_greater_than(0)
expect(report.total_elapsed_us).to_be_greater_than(0)
expect(report.software_pixels_per_second).to_be_greater_than(0)
expect(report.cpu_simd_pixels_per_second).to_be_greater_than(0)
expect(report.metal_pixels_per_second).to_be_greater_than(0)
expect(report.total_pixels_per_second).to_be_greater_than(0)
expect(report.timing_budget_us).to_be_greater_than(0)
expect(report.timing_budget_status).to_equal("pass")
expect(report.timing_budget_reason).to_equal("within-render-budget")
```

</details>

#### executes real Metal framebuffer readback when Metal is available

- executes real Metal framebuffer readback when Metal is available
   - Expected: report.metal_resolved_backend equals `metal`
   - Expected: report.metal_gpu_frame_complete is true
   - Expected: report.metal_gpu_readback_pixel_count equals `16 * 16`
   - Expected: report.metal_resolved_backend equals `software`
   - Expected: report.metal_gpu_frame_complete is false
   - Expected: report.metal_pixel_count equals `16 * 16`
   - Expected: report.metal_different_pixels equals `0`
   - Expected: report.metal_max_channel_diff equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes real Metal framebuffer readback when Metal is available")
val report = run_backend_executed_gui_widget_scene_parity(16, 16)
if is_macos():
    expect(report.metal_resolved_backend).to_equal("metal")
    expect(report.metal_gpu_frame_complete).to_equal(true)
    expect(report.metal_gpu_readback_pixel_count).to_equal(16 * 16)
    expect(report.metal_gpu_readback_checksum).to_be_greater_than(0)
else:
    expect(report.metal_resolved_backend).to_equal("software")
    expect(report.metal_gpu_frame_complete).to_equal(false)
expect(report.metal_pixel_count).to_equal(16 * 16)
expect(report.metal_different_pixels).to_equal(0)
expect(report.metal_max_channel_diff).to_equal(0)
```

</details>

#### medium resolution parity (480x270)

#### maintains exact CPU SIMD parity at 480x270 for reduced scene

- maintains exact CPU SIMD parity at 480x270 for reduced scene
   - Expected: report.software_pixel_count equals `480 * 270`
   - Expected: report.cpu_simd_pixel_count equals `480 * 270`
   - Expected: report.cpu_simd_different_pixels equals `0`
   - Expected: report.cpu_simd_max_channel_diff equals `0`
   - Expected: report.tolerance_used is false
   - Expected: report.exact_backend_parity is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains exact CPU SIMD parity at 480x270 for reduced scene")
val report = run_backend_executed_gui_widget_scene_parity(480, 270)
expect(report.software_pixel_count).to_equal(480 * 270)
expect(report.cpu_simd_pixel_count).to_equal(480 * 270)
expect(report.cpu_simd_different_pixels).to_equal(0)
expect(report.cpu_simd_max_channel_diff).to_equal(0)
expect(report.tolerance_used).to_equal(false)
expect(report.exact_backend_parity).to_equal(true)
```

</details>

#### maintains exact backend parity at 480x270 for widget HTML

- maintains exact backend parity at 480x270 for widget HTML
   - Expected: report.software_pixel_count equals `480 * 270`
   - Expected: report.cpu_simd_pixel_count equals `480 * 270`
   - Expected: report.cpu_simd_different_pixels equals `0`
   - Expected: report.cpu_simd_max_channel_diff equals `0`
   - Expected: report.tolerance_used is false
   - Expected: report.exact_backend_parity is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains exact backend parity at 480x270 for widget HTML")
val report = run_generated_gui_widget_backend_parity(480, 270)
expect(report.software_pixel_count).to_equal(480 * 270)
expect(report.cpu_simd_pixel_count).to_equal(480 * 270)
expect(report.cpu_simd_different_pixels).to_equal(0)
expect(report.cpu_simd_max_channel_diff).to_equal(0)
expect(report.tolerance_used).to_equal(false)
expect(report.exact_backend_parity).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-HARD-013`
- `REQ-WEB-HARD-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d09f64b3f548d0567105e3a82cdd728d5987a3d98ab5173d0e6833e4bcd082e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d09f64b3f548d0567105e3a82cdd728d5987a3d98ab5173d0e6833e4bcd082e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d09f64b3f548d0567105e3a82cdd728d5987a3d98ab5173d0e6833e4bcd082e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses real GUI widget HTML without legacy fixture markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders marker-free widget HTML to a non-empty framebuffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches CPU SIMD backend pixels exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
