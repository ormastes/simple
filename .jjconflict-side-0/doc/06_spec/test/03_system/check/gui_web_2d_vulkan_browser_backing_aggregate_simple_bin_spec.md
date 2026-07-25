# GUI Web 2D Vulkan Browser Backing Aggregate Simple Binary Contract

> The aggregate can be run with only `GUI_WEB_2D_VULKAN_BROWSER_BACKING_ENV`. In that mode it must not emit stale direct-run defaults such as `bin/simple` or an empty status. The browser-backing setup row already records the release Simple binary used for the evidence lane, and the aggregate must preserve it.

<!-- sdn-diagram:id=gui_web_2d_vulkan_browser_backing_aggregate_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_vulkan_browser_backing_aggregate_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_vulkan_browser_backing_aggregate_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_vulkan_browser_backing_aggregate_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Web 2D Vulkan Browser Backing Aggregate Simple Binary Contract

The aggregate can be run with only `GUI_WEB_2D_VULKAN_BROWSER_BACKING_ENV`. In that mode it must not emit stale direct-run defaults such as `bin/simple` or an empty status. The browser-backing setup row already records the release Simple binary used for the evidence lane, and the aggregate must preserve it.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md |
| Source | `test/03_system/check/gui_web_2d_vulkan_browser_backing_aggregate_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The aggregate can be run with only `GUI_WEB_2D_VULKAN_BROWSER_BACKING_ENV`.
In that mode it must not emit stale direct-run defaults such as `bin/simple`
or an empty status. The browser-backing setup row already records the release
Simple binary used for the evidence lane, and the aggregate must preserve it.

## Requirements

**Requirements:** N/A

- REQ-GUI-VK-BROWSER-BIN-001: Browser-backing-only aggregate output preserves
  `gui_web_2d_vulkan_simple_bin` from the browser-backing evidence row.
- REQ-GUI-VK-BROWSER-BIN-002: Browser-backing-only aggregate output preserves
  `gui_web_2d_vulkan_simple_bin_selection_reason`.
- REQ-GUI-VK-BROWSER-BIN-003: Browser-backing-only aggregate output preserves
  `gui_web_2d_vulkan_simple_bin_status`.

## Plan

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md

1. Create a minimal browser-backing env with passing browser status and release
   Simple provenance.
2. Run the GUI RenderDoc aggregate with only that browser-backing env.
3. Assert the aggregate emits the same Simple binary, reason, and status.

## Design

**Design:** doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_vulkan_browser_backing_aggregate_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### GUI Web 2D Vulkan browser-backing aggregate Simple binary contract

#### preserves browser backing Simple binary provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-web-2d-vulkan-browser-backing-aggregate-bin"
val env_path = root + "/browser/evidence.env"
val command = "rm -rf " + root + " && mkdir -p " + root + "/browser && " +
    "printf 'gui_web_2d_vulkan_mode=--browser-backing\\n" +
    "gui_web_2d_vulkan_simple_bin=release/x86_64-unknown-linux-gnu/simple\\n" +
    "gui_web_2d_vulkan_simple_bin_selection_reason=self-hosted-release\\n" +
    "gui_web_2d_vulkan_simple_bin_status=pass\\n" +
    "gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status\\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\\n" +
    "gui_web_2d_vulkan_browser_backing_reason=pass\\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\\n" +
    "gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-backed\\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed\\n' > " + env_path + " && " +
    "GUI_WEB_2D_VULKAN_BROWSER_BACKING_ENV=" + env_path + " BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs >/dev/null"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(_value_of(evidence, "gui_web_2d_vulkan_browser_backing_status")).to_equal("pass")
expect(_value_of(evidence, "gui_web_2d_vulkan_simple_bin")).to_equal("release/x86_64-unknown-linux-gnu/simple")
expect(_value_of(evidence, "gui_web_2d_vulkan_simple_bin_selection_reason")).to_equal("self-hosted-release")
expect(_value_of(evidence, "gui_web_2d_vulkan_simple_bin_status")).to_equal("pass")
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

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md](doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md)


</details>
