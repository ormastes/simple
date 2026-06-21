# Production GUI/Web Renderer Parity Hardening Specification

> Verifies selected Feature C and NFR C renderer parity and GPU/browser evidence taxonomy contracts.

<!-- sdn-diagram:id=production_gui_web_renderer_parity_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_renderer_parity_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_renderer_parity_hardening_spec -> std
production_gui_web_renderer_parity_hardening_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_renderer_parity_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/Web Renderer Parity Hardening Specification

Verifies selected Feature C and NFR C renderer parity and GPU/browser evidence taxonomy contracts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md |
| Research | doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md |
| Source | `test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C renderer parity and GPU/browser evidence
taxonomy contracts.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md
**Research:** doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md
**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Design:** doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md
**Traceability:** REQ-WEB-HARD-013, REQ-WEB-HARD-014, NFR-WEB-HARD-009, NFR-WEB-HARD-012

## Syntax

Call the parity harness helpers from
`app.wm_compare.production_gui_web_renderer_parity` and assert concrete
framebuffer sizes, backend names, pixel counts, exact mismatch counters, and
timing-budget status.

## Examples

The 8K packed-surface planning scenarios assert `7680 * 4320 * 4 =
132710400`, accept `ARGB32`/`RGBA32`/`BGRA32`, reject `RGB565`, and confirm no
default wide-color or codec initialization is required.

## Scenarios

### production GUI web renderer parity hardening

#### 8K packed surface planning

#### reports the exact packed 8K framebuffer size without wide-color eager init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_8k_packed_framebuffer_bytes()).to_equal(132710400)
expect(gui_8k_default_lazy_init_count()).to_equal(0)
```

</details>

#### accepts only 32-bit packed formats for the 8K hot path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_8k_format_eligible_for_packed_hot_path("ARGB32")).to_equal(true)
expect(gui_8k_format_eligible_for_packed_hot_path("RGBA32")).to_equal(true)
expect(gui_8k_format_eligible_for_packed_hot_path("BGRA32")).to_equal(true)
expect(gui_8k_format_eligible_for_packed_hot_path("RGB565")).to_equal(false)
```

</details>

#### generated common.ui widget HTML

#### uses real GUI widget HTML without legacy fixture markers

<details>
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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

#### backend-executed reduced GUI widget scene

#### executes real CPU SIMD drawing operations with exact software parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md](doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md)
- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md](doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md)
- **Research:** [doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md](doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md)


</details>
