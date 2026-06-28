# macOS Metal render-log compare report surface

> Checks that the macOS Metal compare wrapper surfaces the typed report rows used by the aggregate mobile/desktop evidence lane.

<!-- sdn-diagram:id=macos_metal_render_log_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macos_metal_render_log_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macos_metal_render_log_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macos_metal_render_log_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS Metal render-log compare report surface

Checks that the macOS Metal compare wrapper surfaces the typed report rows used by the aggregate mobile/desktop evidence lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md |
| Plan | doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md |
| Design | doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md |
| Research | N/A |
| Source | `test/03_system/check/macos_metal_render_log_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks that the macOS Metal compare wrapper surfaces the typed report rows used
by the aggregate mobile/desktop evidence lane.

**Plan:** doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md
**Requirements:** doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md
**Research:** N/A
**Design:** doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/macos_metal_render_log_compare_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- The report includes gate summary and blocked-gate rows.
- The report includes Electron and Chrome Metal backing provenance rows.
- The report includes Simple, Chrome, and Electron ARGB artifact rows.
- The report includes Xcode GPU capture status and artifact rows.

## Scenarios

### macOS Metal render-log compare report surface

#### keeps detailed Metal, ARGB, and GPU capture report rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-macos-metal-render-log-compare.shs")
expect(script).to_contain("- gate summary: generated=$metal_generated_gate_status framebuffer=$metal_framebuffer_gate_status browser=$browser_backing_gate_status pairwise=$pixel_gate_status argb=$argb_source_gate_status gpu_capture=$gpu_capture_gate_status")
expect(script).to_contain("- blocked gates: $blocked_gate_count / $blocked_gates")
expect(script).to_contain("- Electron Metal backing: $electron_backing detail=$electron_backing_detail_reason source=$electron_backing_source_reason")
expect(script).to_contain("- Chrome Metal backing: $chrome_backing detail=$chrome_backing_detail_reason source=$chrome_backing_source_reason")
expect(script).to_contain("- pairwise ARGB: mode=$pixel_mode electron_chrome=$ec_diff electron_simple=$es_diff chrome_simple=$cs_diff")
expect(script).to_contain("- Simple ARGB artifact: $simple_argb_artifact_file_status/$simple_argb_artifact_status")
expect(script).to_contain("- Chrome ARGB artifact: $chrome_argb_artifact_file_status/$chrome_argb_artifact_status")
expect(script).to_contain("- Electron ARGB artifact: $electron_argb_artifact_file_status/$electron_argb_artifact_status")
expect(script).to_contain("- Xcode GPU capture: status=${capture_status:-unavailable} tool=$gpu_capture_tool")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md](doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md)
- **Plan:** [doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md](doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md)
- **Design:** [doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md](doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md)


</details>
