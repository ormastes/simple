# Linux Vulkan render-log compare gate

> Validates the Linux-first normalized render-log gate for Simple, Chrome, and Electron Vulkan evidence. The spec uses controlled key/value fixtures so it can run on non-GUI hosts without launching browsers or RenderDoc.

<!-- sdn-diagram:id=linux_vulkan_render_log_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linux_vulkan_render_log_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linux_vulkan_render_log_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linux_vulkan_render_log_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Vulkan render-log compare gate

Validates the Linux-first normalized render-log gate for Simple, Chrome, and Electron Vulkan evidence. The spec uses controlled key/value fixtures so it can run on non-GUI hosts without launching browsers or RenderDoc.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Source | `test/03_system/check/linux_vulkan_render_log_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the Linux-first normalized render-log gate for Simple, Chrome, and
Electron Vulkan evidence. The spec uses controlled key/value fixtures so it can
run on non-GUI hosts without launching browsers or RenderDoc.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_render_log_compare_spec.spl --mode=interpreter --clean --fail-fast
```

## Scenarios

### Linux Vulkan render-log compare gate

#### accepts matching Linux Vulkan Simple Chrome and Electron fixture evidence

- Create pass fixtures for aggregate and RenderDoc evidence
   - Expected: code equals `0`
- Read normalized pass evidence and source logs


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass fixtures for aggregate and RenderDoc evidence")
val command = "rm -rf build/test-linux-vulkan-render-log-pass && mkdir -p build/test-linux-vulkan-render-log-pass/rdoc/simple build/test-linux-vulkan-render-log-pass/rdoc/html build/test-linux-vulkan-render-log-pass/rdoc/electron && cat > build/test-linux-vulkan-render-log-pass/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_simple_argb_width=3840\n" +
    "gui_web_2d_vulkan_simple_argb_height=2160\n" +
    "gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_chrome_argb_width=3840\n" +
    "gui_web_2d_vulkan_chrome_argb_height=2160\n" +
    "gui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=42\n" +
    "gui_web_2d_vulkan_electron_argb_width=3840\n" +
    "gui_web_2d_vulkan_electron_argb_height=2160\n" +
    "gui_web_2d_vulkan_electron_argb_nonblank_pixel_count=42\n" +
    "EOF\n" +
    "printf 'rdoc_simple_gate_status=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\nrdoc_capture_file=simple.rdc\\n' > build/test-linux-vulkan-render-log-pass/rdoc/simple/evidence.env\n" +
    "printf 'rdoc_external_host_capture_gate_status=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\nrdoc_capture_file=chrome.rdc\\n' > build/test-linux-vulkan-render-log-pass/rdoc/html/evidence.env\n" +
    "printf 'rdoc_electron_html_gate_status=pass\\nrdoc_capture_status=pass\\nrdoc_capture_magic=RDOC\\nrdoc_capture_file=electron.rdc\\n' > build/test-linux-vulkan-render-log-pass/rdoc/electron/evidence.env\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-pass/out REPORT_PATH=build/test-linux-vulkan-render-log-pass/out/report.md GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-pass/gui.env RDOC_SIMPLE_EVIDENCE_ENV=build/test-linux-vulkan-render-log-pass/rdoc/simple/evidence.env RDOC_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-pass/rdoc/html/evidence.env RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-linux-vulkan-render-log-pass/rdoc/electron/evidence.env sh scripts/check/check-linux-vulkan-render-log-compare.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read normalized pass evidence and source logs")
val evidence = file_read("build/test-linux-vulkan-render-log-pass/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_required_api=vulkan")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_status=pass")
val electron_log = file_read("build/test-linux-vulkan-render-log-pass/out/electron.srl.env")
expect(electron_log).to_contain("simple_render_log_format=simple-render-log-v1")
expect(electron_log).to_contain("simple_render_log_platform=linux")
expect(electron_log).to_contain("simple_render_log_native_api=vulkan")
expect(electron_log).to_contain("simple_render_log_source=electron")
```

</details>

#### fails closed when Electron Vulkan backing is not proven

- Create fail fixtures with Electron browser backing disabled
   - Expected: code equals `0`
- Read fail-closed evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create fail fixtures with Electron browser backing disabled")
val command = "rm -rf build/test-linux-vulkan-render-log-fail && mkdir -p build/test-linux-vulkan-render-log-fail && cat > build/test-linux-vulkan-render-log-fail/gui.env <<'EOF'\n" +
    "gui_web_2d_vulkan_simple_status=pass\n" +
    "gui_web_2d_vulkan_simple_backend_name=vulkan\n" +
    "gui_web_2d_vulkan_simple_argb_backend=vulkan\n" +
    "gui_web_2d_vulkan_electron_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_chrome_browser_backing_status=pass\n" +
    "gui_web_2d_vulkan_browser_backing_status=fail\n" +
    "gui_web_2d_vulkan_pixel_comparison_status=pass\n" +
    "gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff\n" +
    "gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass\n" +
    "gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-fail/out GUI_WEB_2D_VULKAN_ENV=build/test-linux-vulkan-render-log-fail/gui.env sh scripts/check/check-linux-vulkan-render-log-compare.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read fail-closed evidence")
val evidence = file_read("build/test-linux-vulkan-render-log-fail/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("electron-browser-backing-fail")
expect(evidence).to_contain("browser-backing-fail")
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

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
