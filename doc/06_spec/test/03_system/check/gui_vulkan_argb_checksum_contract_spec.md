# GUI Vulkan ARGB Checksum Contract

> Validates that the aggregate GUI RenderDoc status gate fails closed when Electron, Chrome, and Simple ARGB evidence passes pairwise diff status but the reported checksums do not match. Zero mismatch rows are not enough unless the captured ARGB checksum metadata also agrees.

<!-- sdn-diagram:id=gui_vulkan_argb_checksum_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_vulkan_argb_checksum_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_vulkan_argb_checksum_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_vulkan_argb_checksum_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Vulkan ARGB Checksum Contract

Validates that the aggregate GUI RenderDoc status gate fails closed when Electron, Chrome, and Simple ARGB evidence passes pairwise diff status but the reported checksums do not match. Zero mismatch rows are not enough unless the captured ARGB checksum metadata also agrees.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_vulkan_argb_checksum_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the aggregate GUI RenderDoc status gate fails closed when
Electron, Chrome, and Simple ARGB evidence passes pairwise diff status but the
reported checksums do not match. Zero mismatch rows are not enough unless the
captured ARGB checksum metadata also agrees.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- All three pairwise diff rows may pass with `mismatch_count=0`.
- A mismatched ARGB checksum is normalized to a hard pixel comparison failure.
- The aggregate exposes checksum status fields for downstream review.

## Scenarios

### GUI Vulkan ARGB checksum contract

#### rejects pairwise-pass evidence with mismatched ARGB checksums

- Create direct-run Vulkan ARGB evidence with mismatched checksums
   - Expected: code equals `0`
- Assert checksum mismatch is a hard pixel comparison failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create direct-run Vulkan ARGB evidence with mismatched checksums")
val command = "rm -rf build/test-gui-vulkan-argb-checksum-mismatch && mkdir -p build/test-gui-vulkan-argb-checksum-mismatch/run build/test-gui-vulkan-argb-checksum-mismatch/simple && " +
    "printf '{\"width\":1280,\"height\":720,\"format\":\"argb-u32\",\"producer\":\"electron-vulkan-capture\",\"pixels\":[4294967295]}\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/electron_argb.json && " +
    "printf '{\"width\":1280,\"height\":720,\"format\":\"argb-u32\",\"producer\":\"chrome-vulkan-capture\",\"pixels\":[4294967295]}\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/chrome_argb.json && " +
    "printf '{\"width\":1280,\"height\":720,\"format\":\"argb-u32\",\"producer\":\"simple-vulkan-web2d\",\"pixels\":[4294967295]}\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/simple_argb.json && " +
    "printf 'mismatch_count=0\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/electron_chrome_diff.env && " +
    "printf 'mismatch_count=0\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/electron_simple_diff.env && " +
    "printf 'mismatch_count=0\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/chrome_simple_diff.env && " +
    "printf 'vulkan_engine2d_readback_status=pass\\nvulkan_engine2d_readback_reason=pass\\nvulkan_engine2d_readback_spec_status=pass\\nvulkan_engine2d_readback_clear_status=pass\\nvulkan_engine2d_readback_rect_status=pass\\nvulkan_engine2d_readback_clear_mismatches=0\\nvulkan_engine2d_readback_rect_mismatches=0\\nvulkan_engine2d_readback_blur_or_tolerance_used=false\\nvulkan_engine2d_readback_vulkan_strict_exit_code=0\\nvulkan_engine2d_readback_cpu_vulkan_parity_exit_code=0\\n' > build/test-gui-vulkan-argb-checksum-mismatch/simple/evidence.env && " +
    "printf 'gui_web_2d_vulkan_mode=--run\\ngui_web_2d_vulkan_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\ngui_web_2d_vulkan_width=1280\\ngui_web_2d_vulkan_height=720\\ngui_web_2d_vulkan_simple_status=pass\\ngui_web_2d_vulkan_simple_reason=pass\\ngui_web_2d_vulkan_simple_evidence_env=build/test-gui-vulkan-argb-checksum-mismatch/simple/evidence.env\\ngui_web_2d_vulkan_simple_probe_status=Initialized\\ngui_web_2d_vulkan_simple_backend_name=vulkan\\ngui_web_2d_vulkan_electron_argb_status=pass\\ngui_web_2d_vulkan_electron_argb_path=build/test-gui-vulkan-argb-checksum-mismatch/run/electron_argb.json\\ngui_web_2d_vulkan_electron_argb_width=1280\\ngui_web_2d_vulkan_electron_argb_height=720\\ngui_web_2d_vulkan_electron_argb_nonblank_pixel_count=1\\ngui_web_2d_vulkan_electron_argb_checksum=111\\ngui_web_2d_vulkan_electron_argb_weighted_checksum=333\\ngui_web_2d_vulkan_chrome_argb_status=pass\\ngui_web_2d_vulkan_chrome_argb_path=build/test-gui-vulkan-argb-checksum-mismatch/run/chrome_argb.json\\ngui_web_2d_vulkan_chrome_argb_width=1280\\ngui_web_2d_vulkan_chrome_argb_height=720\\ngui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=1\\ngui_web_2d_vulkan_chrome_argb_checksum=222\\ngui_web_2d_vulkan_chrome_argb_weighted_checksum=333\\ngui_web_2d_vulkan_simple_argb_status=pass\\ngui_web_2d_vulkan_simple_argb_path=build/test-gui-vulkan-argb-checksum-mismatch/run/simple_argb.json\\ngui_web_2d_vulkan_simple_argb_width=1280\\ngui_web_2d_vulkan_simple_argb_height=720\\ngui_web_2d_vulkan_simple_argb_nonblank_pixel_count=1\\ngui_web_2d_vulkan_simple_argb_checksum=111\\ngui_web_2d_vulkan_simple_argb_weighted_checksum=333\\ngui_web_2d_vulkan_electron_chrome_diff_status=pass\\ngui_web_2d_vulkan_electron_chrome_diff_reason=pass\\ngui_web_2d_vulkan_electron_chrome_mismatch_count=0\\ngui_web_2d_vulkan_electron_chrome_diff_path=build/test-gui-vulkan-argb-checksum-mismatch/run/electron_chrome_diff.env\\ngui_web_2d_vulkan_electron_simple_diff_status=pass\\ngui_web_2d_vulkan_electron_simple_diff_reason=pass\\ngui_web_2d_vulkan_electron_simple_mismatch_count=0\\ngui_web_2d_vulkan_electron_simple_diff_path=build/test-gui-vulkan-argb-checksum-mismatch/run/electron_simple_diff.env\\ngui_web_2d_vulkan_chrome_simple_diff_status=pass\\ngui_web_2d_vulkan_chrome_simple_diff_reason=pass\\ngui_web_2d_vulkan_chrome_simple_mismatch_count=0\\ngui_web_2d_vulkan_chrome_simple_diff_path=build/test-gui-vulkan-argb-checksum-mismatch/run/chrome_simple_diff.env\\n' > build/test-gui-vulkan-argb-checksum-mismatch/run/evidence.env && " +
    "GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV=build/test-gui-vulkan-argb-checksum-mismatch/run/evidence.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-vulkan-argb-checksum-mismatch/out REPORT_PATH=build/test-gui-vulkan-argb-checksum-mismatch/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert checksum mismatch is a hard pixel comparison failure")
val evidence = file_read("build/test-gui-vulkan-argb-checksum-mismatch/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_argb_checksum_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_chrome_argb_checksum_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_simple_argb_checksum_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_argb_checksum_match_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_argb_weighted_checksum_match_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_pixel_comparison_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff-mismatch")
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


</details>
