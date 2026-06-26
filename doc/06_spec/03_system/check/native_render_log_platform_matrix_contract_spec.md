# Native Render-Log Platform Matrix Contract

> Validates the aggregate GUI RenderDoc status gate's normalized native render-log platform matrix. The matrix must not accept a platform row only because `*_render_log_compare_status=pass`; it also requires the expected native API and pairwise comparison status for Linux Vulkan, macOS Metal, and Windows D3D12.

<!-- sdn-diagram:id=native_render_log_platform_matrix_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_render_log_platform_matrix_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_render_log_platform_matrix_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_render_log_platform_matrix_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Render-Log Platform Matrix Contract

Validates the aggregate GUI RenderDoc status gate's normalized native render-log platform matrix. The matrix must not accept a platform row only because `*_render_log_compare_status=pass`; it also requires the expected native API and pairwise comparison status for Linux Vulkan, macOS Metal, and Windows D3D12.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/native_render_log_platform_matrix_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the aggregate GUI RenderDoc status gate's normalized native
render-log platform matrix. The matrix must not accept a platform row only
because `*_render_log_compare_status=pass`; it also requires the expected
native API and pairwise comparison status for Linux Vulkan, macOS Metal, and
Windows D3D12.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=... \
MACOS_METAL_RENDER_LOG_COMPARE_ENV=... \
WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=... \
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Acceptance

- A `pass` Linux row with missing pairwise status is normalized to fail.
- A `pass` Windows row with `required_api=d3d11` is normalized to fail.
- The platform matrix reports invalid present rows as failed, not missing.
- A missing macOS row remains in the missing list without being counted as a
  failed row.

## Platform Rows

The aggregate reads three independent platform evidence files:

- `LINUX_VULKAN_RENDER_LOG_COMPARE_ENV`
- `MACOS_METAL_RENDER_LOG_COMPARE_ENV`
- `WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV`

Each row has its own native API contract. Linux must report
`linux_vulkan_render_log_compare_required_api=vulkan` and
`linux_vulkan_render_log_compare_pairwise_status=pass`. macOS must report
`macos_metal_render_log_compare_required_api=metal` and
`macos_metal_render_log_compare_pairwise_status=pass`. Windows must report
`windows_d3d12_render_log_compare_required_api=d3d12` and
`windows_d3d12_render_log_compare_pairwise_status=pass`.

## Matrix Semantics

The matrix emits three rollup keys:

- `native_render_log_platform_matrix_status`
- `native_render_log_platform_matrix_missing_platforms`
- `native_render_log_platform_matrix_failed_platforms`

`missing_platforms` is reserved for absent or unavailable platform rows. A row
that exists but claims the wrong API or lacks pairwise comparison proof is a
failed row, not a missing row. This distinction matters for parallel platform
work: a Linux failure needs Linux evidence repair, while missing macOS or
Windows rows need execution on those hosts.

## Failure Examples

The first scenario creates present but invalid Linux and Windows rows while
macOS passes. The expected result is `status=fail`, an empty missing list, and
`failed_platforms=linux-vulkan,windows-d3d12`.

The second scenario creates a valid Linux row while macOS and Windows evidence
files are absent. The expected result is `status=incomplete`,
`missing_platforms=macos-metal,windows-d3d12`, and an empty failed list.

## Completion Boundaries

This contract validates only the aggregate classification layer. It does not
produce real RenderDoc, Metal, D3D12, PIX, GPU debugger, Chrome, Electron, or
Simple renderer artifacts. Those artifacts must be produced by the platform
compare wrappers before the matrix can pass in production evidence.

## Operator Interpretation

Use the emitted lists to choose the next lane:

- If `missing_platforms` includes `macos-metal`, run or repair the macOS Metal
  compare wrapper on a macOS GUI host.
- If `missing_platforms` includes `windows-d3d12`, run or repair the Windows
  D3D12/PIX compare wrapper on a Windows GUI host.
- If `failed_platforms` includes `linux-vulkan`, inspect
  `linux_vulkan_render_log_compare_reason` first. On the current Linux host the
  expected actionable blocker is Electron browser hardware Vulkan backing, not
  missing pairwise pixels.
- If a platform appears in both lists, that is a regression in this aggregate
  classifier. A present invalid row must be failed only, while an absent row
  must be missing only.

The aggregate GUI RenderDoc report prints both missing and failed platform
lists in the summary line so a human can distinguish "needs another host" from
"host evidence exists but failed contract checks" without opening the raw env.
Do not collapse these fields back into a single incomplete list; that would
hide which parallel agent or host owns the next repair.

## Scenarios

### Native render-log platform matrix contract

#### rejects pass rows with missing pairwise status or the wrong native API

- Create controlled platform render-log rows with invalid pass claims
   - Expected: code equals `0`
- Assert the aggregate hardens the platform matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled platform render-log rows with invalid pass claims")
val command = "rm -rf build/test-native-render-log-platform-matrix-contract && mkdir -p build/test-native-render-log-platform-matrix-contract/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\n' > build/test-native-render-log-platform-matrix-contract/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\n' > build/test-native-render-log-platform-matrix-contract/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d11\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\n' > build/test-native-render-log-platform-matrix-contract/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-contract/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-contract/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-contract/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-contract/out REPORT_PATH=build/test-native-render-log-platform-matrix-contract/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate hardens the platform matrix")
val evidence = file_read("build/test-native-render-log-platform-matrix-contract/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_reason=missing-or-failing-native-render-log-platforms")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=linux-vulkan,windows-d3d12")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_reason=linux-vulkan-pairwise-not-pass:<missing>")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows_d3d12_render_log_compare_reason=invalid-windows-d3d12-required-api:d3d11")
expect(evidence).to_contain("macos_metal_render_log_compare_status=pass")
```

</details>

#### keeps absent platform rows in the missing list only

- Create Linux pass evidence and leave macOS/Windows rows absent
   - Expected: code equals `0`
- Assert unavailable rows are missing but not failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create Linux pass evidence and leave macOS/Windows rows absent")
val command = "rm -rf build/test-native-render-log-platform-matrix-missing && mkdir -p build/test-native-render-log-platform-matrix-missing/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\n' > build/test-native-render-log-platform-matrix-missing/renderlogs/linux.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-missing/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-missing/renderlogs/missing-macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-missing/renderlogs/missing-windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-missing/out REPORT_PATH=build/test-native-render-log-platform-matrix-missing/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert unavailable rows are missing but not failed")
val evidence = file_read("build/test-native-render-log-platform-matrix-missing/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=incomplete")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=macos-metal,windows-d3d12")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_status=unavailable")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=unavailable")
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
