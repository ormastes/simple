# Linux Vulkan RenderDoc Reason Forwarding

> Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep the actionable Chrome/Electron RenderDoc failure reason visible at aggregate level. This spec intentionally avoids the broad GUI aggregate fixture so it can run quickly when the full aggregate SSpec is too expensive for a focused check.

<!-- sdn-diagram:id=linux_vulkan_renderdoc_reason_forwarding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linux_vulkan_renderdoc_reason_forwarding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linux_vulkan_renderdoc_reason_forwarding_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linux_vulkan_renderdoc_reason_forwarding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Vulkan RenderDoc Reason Forwarding

Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep the actionable Chrome/Electron RenderDoc failure reason visible at aggregate level. This spec intentionally avoids the broad GUI aggregate fixture so it can run quickly when the full aggregate SSpec is too expensive for a focused check.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Source | `test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep
the actionable Chrome/Electron RenderDoc failure reason visible at aggregate
level. This spec intentionally avoids the broad GUI aggregate fixture so it can
run quickly when the full aggregate SSpec is too expensive for a focused check.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl --mode=interpreter --clean
```

## Acceptance

- The Linux comparison wrapper prefers
  `rdoc_external_host_capture_reason_raw` before the generic gate reason.
- The aggregate status wrapper reads and emits Simple, Chrome, and Electron
  Linux RenderDoc reason keys.
- The current report records the actionable Chrome and Electron blockers.

## Scenarios

### Linux Vulkan RenderDoc reason forwarding

#### keeps actionable browser RenderDoc failure reasons in the Linux comparison and aggregate

- Read the Linux comparison wrapper
- Assert Chrome raw capture reason is preferred over the generic gate reason
- Read the GUI RenderDoc aggregate wrapper
- Assert aggregate reads and emits per-backend Linux RenderDoc reasons
- Assert the current report exposes actionable browser blocker reasons


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the Linux comparison wrapper")
val linux_compare = file_read("scripts/check/check-linux-vulkan-render-log-compare.shs")

step("Assert Chrome raw capture reason is preferred over the generic gate reason")
expect(linux_compare).to_contain("render_log_reason_from_rdoc_env \"$RDOC_HTML_EVIDENCE_ENV\" rdoc_external_host_capture_reason_raw rdoc_external_host_gate_reason")

step("Read the GUI RenderDoc aggregate wrapper")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Assert aggregate reads and emits per-backend Linux RenderDoc reasons")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_simple_reason = value_of(\"linux_vulkan_render_log_compare_renderdoc_simple_reason\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_reason = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_reason\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_reason = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_reason\"")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_simple_reason\", linux_vulkan_render_log_renderdoc_simple_reason)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_reason\", linux_vulkan_render_log_renderdoc_chrome_reason)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_reason\", linux_vulkan_render_log_renderdoc_electron_reason)")

step("Assert the current report exposes actionable browser blocker reasons")
val report = file_read("doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md")
expect(report).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_reason=chromium-gpu-process-crashed-under-renderdoc")
expect(report).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_reason=missing-rdc")
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

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md)


</details>
