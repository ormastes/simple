# Production GUI 8K Surface Planning Specification

> Verifies the 8K packed-surface planning contract without running the full renderer parity scene suite. This keeps the 8K color/image evidence gate fast while the broader parity hardening spec continues to cover backend rendering.

<!-- sdn-diagram:id=production_gui_8k_surface_planning_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_8k_surface_planning_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_8k_surface_planning_spec -> std
production_gui_8k_surface_planning_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_8k_surface_planning_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI 8K Surface Planning Specification

Verifies the 8K packed-surface planning contract without running the full renderer parity scene suite. This keeps the 8K color/image evidence gate fast while the broader parity hardening spec continues to cover backend rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md |
| Research | doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md |
| Source | `test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the 8K packed-surface planning contract without running the full
renderer parity scene suite. This keeps the 8K color/image evidence gate fast
while the broader parity hardening spec continues to cover backend rendering.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md
**Research:** doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md
**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Design:** doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md

## Syntax

Call the 8K planning helpers from
`app.wm_compare.production_gui_web_renderer_parity` and assert exact pixel
count, row stride, framebuffer bytes, lazy init count, and format eligibility.

## Examples

`7680 * 4320 * 4` must stay `132710400` bytes for the default packed GUI
surface. `ARGB32`, `RGBA32`, and `BGRA32` are eligible for the 8K hot path;
`RGB565` is rejected.

## Scenarios

### production GUI 8K surface planning

#### reports the exact packed 8K framebuffer size without eager init

- Plan a 7680 by 4320 packed 32-bit GUI surface
   - Expected: gui_8k_pixel_count() equals `33177600`
   - Expected: gui_8k_packed_row_stride_bytes() equals `30720`
   - Expected: gui_8k_packed_framebuffer_bytes() equals `132710400`
- Confirm wide-color and codec setup stays lazy for the default path
   - Expected: gui_8k_default_lazy_init_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a 7680 by 4320 packed 32-bit GUI surface")
expect(gui_8k_pixel_count()).to_equal(33177600)
expect(gui_8k_packed_row_stride_bytes()).to_equal(30720)
expect(gui_8k_packed_framebuffer_bytes()).to_equal(132710400)

step("Confirm wide-color and codec setup stays lazy for the default path")
expect(gui_8k_default_lazy_init_count()).to_equal(0)
```

</details>

#### accepts only 32-bit packed formats for the 8K hot path

- Accept ARGB32, RGBA32, and BGRA32 as packed 8K hot-path formats
   - Expected: gui_8k_format_eligible_for_packed_hot_path("ARGB32") is true
   - Expected: gui_8k_format_eligible_for_packed_hot_path("RGBA32") is true
   - Expected: gui_8k_format_eligible_for_packed_hot_path("BGRA32") is true
- Reject RGB565 because it is not the 32-bit packed GUI path
   - Expected: gui_8k_format_eligible_for_packed_hot_path("RGB565") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept ARGB32, RGBA32, and BGRA32 as packed 8K hot-path formats")
expect(gui_8k_format_eligible_for_packed_hot_path("ARGB32")).to_equal(true)
expect(gui_8k_format_eligible_for_packed_hot_path("RGBA32")).to_equal(true)
expect(gui_8k_format_eligible_for_packed_hot_path("BGRA32")).to_equal(true)

step("Reject RGB565 because it is not the 32-bit packed GUI path")
expect(gui_8k_format_eligible_for_packed_hot_path("RGB565")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md](doc/02_requirements/ui/graphics/gui_color_image_pipeline_8k.md)
- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md](doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md)
- **Research:** [doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md](doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md)


</details>
