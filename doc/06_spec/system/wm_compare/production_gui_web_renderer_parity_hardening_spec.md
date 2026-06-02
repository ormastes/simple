# Production Gui Web Renderer Parity Hardening Specification

## Scenarios

### production GUI web renderer parity hardening

#### generated common.ui widget HTML

#### uses real GUI widget HTML without legacy fixture markers

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = run_generated_gui_widget_backend_parity(96, 72)
expect(report.has_widget_html).to_equal(true)
expect(report.has_legacy_fixture_marker).to_equal(false)
expect(report.software_pixel_count).to_equal(96 * 72)
expect(report.distinct_software_colors).to_be_greater_than(3)
```

</details>

#### matches CPU SIMD backend pixels exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = run_generated_gui_widget_backend_parity(96, 72)
expect(report.cpu_simd_resolved_backend).to_equal("cpu_simd")
expect(report.cpu_simd_pixel_count).to_equal(96 * 72)
expect(report.cpu_simd_different_pixels).to_equal(0)
expect(report.cpu_simd_match_percentage).to_equal(10000)
expect(report.cpu_simd_max_channel_diff).to_equal(0)
```

</details>

#### matches Metal backend pixels exactly with no tolerance

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/system/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- production GUI web renderer parity hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

