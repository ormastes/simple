# modern_wm_readiness_spec

Verifies one combined readiness report for the modern Web WM, SimpleOS

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/desktop/modern_wm_readiness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies one combined readiness report for the modern Web WM, SimpleOS
    dock/taskbar, lifecycle motion, and rendered motion metadata.

## Scenarios

### Modern WM readiness audit

#### passes when Web quality and OS shell motion contracts are all present

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = modern_wm_readiness_report("glass_dark")
expect(report.passed)
expect(report.web_quality_ready)
expect(report.os_dock_ready)
expect(report.os_taskbar_ready)
expect(report.lifecycle_motion_ready)
expect(report.rendered_motion_ready)
expect(report.color_checked)
expect(report.contrast_ratio_x100).to_be_greater_than(449)
expect(report.size_layout_configured)
expect(report.titlebar_height_px).to_equal(38)
expect(report.window_min_width_px).to_equal(200)
expect(report.window_min_height_px).to_equal(120)
expect(report.title_input_min_width_px).to_equal(140)
expect(report.taskbar_icon_size_px).to_equal(26)
expect(report.command_palette_ready)
expect(report.title_input_ready)
expect(report.visual_layering_ready)
expect(report.motion_verbosity_control)
expect(report.round_icon_converter)
expect(report.round_scrollbars)
expect(report.translucent_shell)
expect(report.accessible_controls_ready)
expect(report.snap_assist_ready)
expect(report.desktop_widgets_ready)
expect(report.notes[0]).to_equal("modern WM readiness passed")
```

</details>

#### summarizes the readiness gates for release evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = modern_wm_readiness_summary("glass_dark")
expect(summary).to_contain("modern_wm_readiness")
expect(summary).to_contain("status=pass")
expect(summary).to_contain("web=true")
expect(summary).to_contain("dock=true")
expect(summary).to_contain("taskbar=true")
expect(summary).to_contain("lifecycle=true")
expect(summary).to_contain("rendered_motion=true")
expect(summary).to_contain("color_checked=true")
expect(summary).to_contain("contrast_ratio_x100=")
expect(summary).to_contain("size_layout=true")
expect(summary).to_contain("titlebar=38px")
expect(summary).to_contain("window_min=200x120")
expect(summary).to_contain("title_input=140px")
expect(summary).to_contain("taskbar_icon=26px")
expect(summary).to_contain("command_palette=true")
expect(summary).to_contain("title_input_ready=true")
expect(summary).to_contain("visual_layering=true")
expect(summary).to_contain("motion_control=true")
expect(summary).to_contain("round_icons=true")
expect(summary).to_contain("round_scrollbars=true")
expect(summary).to_contain("translucent=true")
expect(summary).to_contain("accessible_controls=true")
expect(summary).to_contain("snap_assist=true")
expect(summary).to_contain("desktop_widgets=true")
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

