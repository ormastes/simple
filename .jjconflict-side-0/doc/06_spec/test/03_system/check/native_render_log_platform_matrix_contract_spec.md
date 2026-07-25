# Native Render-Log Platform Matrix Contract

> Validates the aggregate GUI RenderDoc status gate's normalized native render-log platform matrix. The matrix must not accept a platform row only because `*_render_log_compare_status=pass`; it also requires the expected native API, pairwise comparison status, and platform-native capture/debugger proof for Linux Vulkan, macOS Metal, and Windows D3D12.

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
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Render-Log Platform Matrix Contract

Validates the aggregate GUI RenderDoc status gate's normalized native render-log platform matrix. The matrix must not accept a platform row only because `*_render_log_compare_status=pass`; it also requires the expected native API, pairwise comparison status, and platform-native capture/debugger proof for Linux Vulkan, macOS Metal, and Windows D3D12.

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
native API, pairwise comparison status, and platform-native capture/debugger
proof for Linux Vulkan, macOS Metal, and Windows D3D12.

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

- A `pass` Linux row with missing blocked-gate proof or pairwise status is
  normalized to fail before capture checks.
- A `pass` Windows row with `required_api=d3d11` is normalized to fail.
- A `pass` row that omits required RenderDoc/GPU capture/PIX/debugger proof is
  normalized to fail.
- A `pass` macOS row whose Xcode GPU capture metadata claims `XCODE-GPUTRACE`
  but omits artifact file-status proof is normalized to fail.
- A `pass` Windows row whose PIX metadata claims `PIX` but whose propagated
  file-byte magic is missing or invalid is normalized to fail.
- A `pass` Windows row that omits the structured blocked-gate fields from the
  D3D12 compare wrapper is normalized to fail.
- A `pass` Windows row that names a GPU debugger artifact but omits verified
  artifact file-status proof is normalized to fail.
- The platform matrix reports invalid present rows as failed, not missing.
- A missing macOS row remains in the missing list without being counted as a
  failed row.

## Platform Rows

The aggregate reads three independent platform evidence files:

- `LINUX_VULKAN_RENDER_LOG_COMPARE_ENV`
- `MACOS_METAL_RENDER_LOG_COMPARE_ENV`
- `WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV`

Each row has its own native API contract. Linux must report
`linux_vulkan_render_log_compare_required_api=vulkan`,
`linux_vulkan_render_log_compare_pairwise_status=pass`, and RenderDoc pass
statuses for Simple, Chrome, and Electron. Each Linux RenderDoc surface must
also report its evidence env file status, artifact file status, and
`artifact_magic=RDOC`; status-only rows are not capture proof. The aggregate
also forwards Linux host readiness rows for RenderDoc, Chrome, and Electron so
parallel agents can distinguish missing host tools from failed renderer
capture. macOS must report
`macos_metal_render_log_compare_required_api=metal`,
`macos_metal_render_log_compare_pairwise_status=pass`, and
`macos_metal_render_log_compare_gpu_capture_status=pass` with an
`XCODE-GPUTRACE` artifact marker and a passing capture artifact file-status
row. Windows must report
`windows_d3d12_render_log_compare_required_api=d3d12`,
`windows_d3d12_render_log_compare_pairwise_status=pass`,
`windows_d3d12_render_log_compare_blocked_gate_count=0`, passing native
readback, browser backing, pairwise, ARGB source, and PIX/GPU-debugger gate
statuses,
`windows_d3d12_render_log_compare_pix_status=pass` with a `PIX` artifact
marker plus `windows_d3d12_render_log_compare_pix_artifact_file_magic=PIX`, and
`windows_d3d12_render_log_compare_gpu_debugger_status=pass` with verified
debugger artifact file proof. Metadata strings alone are not PIX or GPU
debugger completion evidence.

## Matrix Semantics

The matrix emits the native render-log rollup keys:

- `native_render_log_platform_matrix_status`
- `native_render_log_platform_matrix_missing_platforms`
- `native_render_log_platform_matrix_failed_platforms`

It also emits the plainly named goal-completion alias keys:

- `native_gui_platform_verification_status`
- `native_gui_platform_verification_required_platforms`
- `native_gui_platform_verification_missing_platforms`
- `native_gui_platform_verification_failed_platforms`

The `native_gui_platform_verification_*` keys must stay in lockstep with the
native render-log matrix fields instead of becoming a second classifier.

`missing_platforms` is reserved for absent or unavailable platform rows. A row
that exists but claims the wrong API, lacks pairwise comparison proof, or omits
the native RenderDoc artifact/capture/debugger proof is a failed row, not a missing row. This
distinction matters for parallel platform work: a Linux failure needs Linux
evidence repair, while missing macOS or Windows rows need execution on those
hosts.

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

#### rejects pass rows with missing gate proof or the wrong native API

- Create controlled platform render-log rows with invalid pass claims
   - Expected: code equals `0`
- Assert the aggregate hardens the platform matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create controlled platform render-log rows with invalid pass claims")
val command = "rm -rf build/test-native-render-log-platform-matrix-contract && mkdir -p build/test-native-render-log-platform-matrix-contract/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\n' > build/test-native-render-log-platform-matrix-contract/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace\\nmacos_metal_render_log_compare_gpu_capture_artifact_file_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE\\nmacos_metal_render_log_compare_electron_browser_backing_status=pass\\nmacos_metal_render_log_compare_chrome_browser_backing_status=pass\\nmacos_metal_render_log_compare_browser_backing_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_simple_argb_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_reason=pass\\nmacos_metal_render_log_compare_electron_argb_reason=pass\\nmacos_metal_render_log_compare_simple_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_electron_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_argb_viewport_reason=pass\\n' > build/test-native-render-log-platform-matrix-contract/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d11\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_blocked_gate_count=0\\nwindows_d3d12_render_log_compare_blocked_gates=\\nwindows_d3d12_render_log_compare_native_readback_gate_status=pass\\nwindows_d3d12_render_log_compare_browser_backing_gate_status=pass\\nwindows_d3d12_render_log_compare_pairwise_gate_status=pass\\nwindows_d3d12_render_log_compare_argb_source_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log\\n' > build/test-native-render-log-platform-matrix-contract/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-contract/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-contract/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-contract/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-contract/out REPORT_PATH=build/test-native-render-log-platform-matrix-contract/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate hardens the platform matrix")
val evidence = file_read("build/test-native-render-log-platform-matrix-contract/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_reason=missing-or-failing-native-render-log-platforms")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=linux-vulkan,macos-metal,windows-d3d12")
expect(evidence).to_contain("native_gui_platform_verification_status=fail")
expect(evidence).to_contain("native_gui_platform_verification_reason=missing-or-failing-native-render-log-platforms")
expect(evidence).to_contain("native_gui_platform_verification_required_platforms=linux-vulkan,macos-metal,windows-d3d12")
expect(evidence).to_contain("native_gui_platform_verification_missing_platforms=")
expect(evidence).to_contain("native_gui_platform_verification_failed_platforms=linux-vulkan,macos-metal,windows-d3d12")
expect(evidence).to_contain("native_render_log_platform_matrix_linux_vulkan_command=BUILD_DIR=build/linux-vulkan-render-log-compare sh scripts/check/check-linux-vulkan-render-log-compare.shs")
expect(evidence).to_contain("native_render_log_platform_matrix_macos_metal_command=MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 BUILD_DIR=build/macos-metal-render-log-compare sh scripts/check/check-macos-metal-render-log-compare.shs")
expect(evidence).to_contain("native_render_log_platform_matrix_windows_d3d12_command=WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 BUILD_DIR=build/windows-d3d12-render-log-compare sh scripts/check/check-windows-d3d12-render-log-compare.shs")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_reason=linux-vulkan-blocked-gates-present:<missing>")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows_d3d12_render_log_compare_reason=invalid-windows-d3d12-required-api:d3d11")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_reason=macos-metal-blocked-gates-present:<missing>")
```

</details>

#### keeps absent platform rows in the missing list only

- Create Linux pass evidence and leave macOS/Windows rows absent
   - Expected: code equals `0`
- Assert unavailable rows are missing but not failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create Linux pass evidence and leave macOS/Windows rows absent")
val command = "rm -rf build/test-native-render-log-platform-matrix-missing && mkdir -p build/test-native-render-log-platform-matrix-missing/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_argb_source_gate_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_electron_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_host_renderdoc_status=pass\\nlinux_vulkan_render_log_compare_host_renderdoc_tool=renderdoccmd\\nlinux_vulkan_render_log_compare_host_chrome_status=pass\\nlinux_vulkan_render_log_compare_host_chrome_tool=google-chrome\\nlinux_vulkan_render_log_compare_host_electron_status=pass\\nlinux_vulkan_render_log_compare_host_electron_tool=electron\\n' > build/test-native-render-log-platform-matrix-missing/renderlogs/linux.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-missing/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-missing/renderlogs/missing-macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-missing/renderlogs/missing-windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-missing/out REPORT_PATH=build/test-native-render-log-platform-matrix-missing/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert unavailable rows are missing but not failed")
val evidence = file_read("build/test-native-render-log-platform-matrix-missing/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=incomplete")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=macos-metal,windows-d3d12")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=")
expect(evidence).to_contain("native_gui_platform_verification_status=incomplete")
expect(evidence).to_contain("native_gui_platform_verification_required_platforms=linux-vulkan,macos-metal,windows-d3d12")
expect(evidence).to_contain("native_gui_platform_verification_missing_platforms=macos-metal,windows-d3d12")
expect(evidence).to_contain("native_gui_platform_verification_failed_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_macos_metal_command=MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 BUILD_DIR=build/macos-metal-render-log-compare sh scripts/check/check-macos-metal-render-log-compare.shs")
expect(evidence).to_contain("native_render_log_platform_matrix_windows_d3d12_command=WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 BUILD_DIR=build/windows-d3d12-render-log-compare sh scripts/check/check-windows-d3d12-render-log-compare.shs")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_host_renderdoc_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_host_renderdoc_tool=renderdoccmd")
expect(evidence).to_contain("linux_vulkan_render_log_compare_host_chrome_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_host_chrome_tool=google-chrome")
expect(evidence).to_contain("linux_vulkan_render_log_compare_host_electron_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_host_electron_tool=electron")
expect(evidence).to_contain("macos_metal_render_log_compare_status=unavailable")
expect(evidence).to_contain("macos_metal_render_log_compare_pairwise_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_status=unavailable")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=missing")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=unavailable")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pairwise_status=missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_status=unavailable")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_artifact=missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_artifact_magic=missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_artifact_file_magic=missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_gpu_debugger_status=unavailable")
expect(evidence).to_contain("windows_d3d12_render_log_compare_gpu_debugger_artifact=missing")
```

</details>

#### rejects pass rows that omit native RenderDoc artifact capture and debugger proof

- Create pass-looking rows without the required native proof fields
   - Expected: code equals `0`
- Assert missing native proof fields are failed platform rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass-looking rows without the required native proof fields")
val command = "rm -rf build/test-native-render-log-platform-matrix-debugger-proof && mkdir -p build/test-native-render-log-platform-matrix-debugger-proof/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_argb_source_gate_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\n' > build/test-native-render-log-platform-matrix-debugger-proof/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_blocked_gate_count=0\\nmacos_metal_render_log_compare_blocked_gates=\\nmacos_metal_render_log_compare_generated_readback_gate_status=pass\\nmacos_metal_render_log_compare_framebuffer_readback_gate_status=pass\\nmacos_metal_render_log_compare_browser_backing_gate_status=pass\\nmacos_metal_render_log_compare_pairwise_gate_status=pass\\nmacos_metal_render_log_compare_argb_source_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\n' > build/test-native-render-log-platform-matrix-debugger-proof/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d12\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_blocked_gate_count=0\\nwindows_d3d12_render_log_compare_blocked_gates=\\nwindows_d3d12_render_log_compare_native_readback_gate_status=pass\\nwindows_d3d12_render_log_compare_browser_backing_gate_status=pass\\nwindows_d3d12_render_log_compare_pairwise_gate_status=pass\\nwindows_d3d12_render_log_compare_argb_source_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_pix_artifact_file_magic=PIX\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\n' > build/test-native-render-log-platform-matrix-debugger-proof/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-debugger-proof/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-debugger-proof/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-debugger-proof/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-debugger-proof/out REPORT_PATH=build/test-native-render-log-platform-matrix-debugger-proof/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert missing native proof fields are failed platform rows")
val evidence = file_read("build/test-native-render-log-platform-matrix-debugger-proof/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=linux-vulkan,macos-metal,windows-d3d12")
expect(evidence).to_contain("linux_vulkan_render_log_compare_reason=linux-vulkan-renderdoc-simple-env-not-pass:<missing>")
expect(evidence).to_contain("macos_metal_render_log_compare_reason=macos-metal-gpu-capture-artifact-missing")
expect(evidence).to_contain("windows_d3d12_render_log_compare_reason=windows-d3d12-pix-artifact-file-not-pass:<missing>")
```

</details>

#### rejects Windows D3D12 rows whose PIX file-byte proof is missing

- Create pass-looking platform rows with PIX metadata but no propagated file magic
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass-looking platform rows with PIX metadata but no propagated file magic")
val command = "rm -rf build/test-native-render-log-platform-matrix-pix-file-magic && mkdir -p build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_argb_source_gate_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_electron_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\\n' > build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_blocked_gate_count=0\\nmacos_metal_render_log_compare_blocked_gates=\\nmacos_metal_render_log_compare_generated_readback_gate_status=pass\\nmacos_metal_render_log_compare_framebuffer_readback_gate_status=pass\\nmacos_metal_render_log_compare_browser_backing_gate_status=pass\\nmacos_metal_render_log_compare_pairwise_gate_status=pass\\nmacos_metal_render_log_compare_argb_source_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace\\nmacos_metal_render_log_compare_gpu_capture_artifact_file_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE\\nmacos_metal_render_log_compare_electron_browser_backing_status=pass\\nmacos_metal_render_log_compare_chrome_browser_backing_status=pass\\nmacos_metal_render_log_compare_browser_backing_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_simple_argb_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_reason=pass\\nmacos_metal_render_log_compare_electron_argb_reason=pass\\nmacos_metal_render_log_compare_simple_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_electron_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_argb_viewport_reason=pass\\n' > build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d12\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_blocked_gate_count=0\\nwindows_d3d12_render_log_compare_blocked_gates=\\nwindows_d3d12_render_log_compare_native_readback_gate_status=pass\\nwindows_d3d12_render_log_compare_browser_backing_gate_status=pass\\nwindows_d3d12_render_log_compare_pairwise_gate_status=pass\\nwindows_d3d12_render_log_compare_argb_source_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_pix_artifact_file_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log\\n' > build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-pix-file-magic/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-pix-file-magic/out REPORT_PATH=build/test-native-render-log-platform-matrix-pix-file-magic/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-native-render-log-platform-matrix-pix-file-magic/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=windows-d3d12")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows_d3d12_render_log_compare_reason=windows-d3d12-pix-artifact-file-magic-not-pix:<missing>")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_artifact_magic=PIX")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_artifact_file_magic=")
```

</details>

#### rejects Windows D3D12 rows that omit structured blocked-gate proof

- Create pass-looking Windows row with legacy fields but no blocked-gate contract
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass-looking Windows row with legacy fields but no blocked-gate contract")
val command = "rm -rf build/test-native-render-log-platform-matrix-windows-gates && mkdir -p build/test-native-render-log-platform-matrix-windows-gates/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_argb_source_gate_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_electron_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\\n' > build/test-native-render-log-platform-matrix-windows-gates/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_blocked_gate_count=0\\nmacos_metal_render_log_compare_blocked_gates=\\nmacos_metal_render_log_compare_generated_readback_gate_status=pass\\nmacos_metal_render_log_compare_framebuffer_readback_gate_status=pass\\nmacos_metal_render_log_compare_browser_backing_gate_status=pass\\nmacos_metal_render_log_compare_pairwise_gate_status=pass\\nmacos_metal_render_log_compare_argb_source_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace\\nmacos_metal_render_log_compare_gpu_capture_artifact_file_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE\\nmacos_metal_render_log_compare_electron_browser_backing_status=pass\\nmacos_metal_render_log_compare_chrome_browser_backing_status=pass\\nmacos_metal_render_log_compare_browser_backing_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_simple_argb_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_reason=pass\\nmacos_metal_render_log_compare_electron_argb_reason=pass\\nmacos_metal_render_log_compare_simple_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_electron_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_argb_viewport_reason=pass\\n' > build/test-native-render-log-platform-matrix-windows-gates/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d12\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_pix_artifact_file_magic=PIX\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log\\n' > build/test-native-render-log-platform-matrix-windows-gates/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-windows-gates/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-windows-gates/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-windows-gates/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-windows-gates/out REPORT_PATH=build/test-native-render-log-platform-matrix-windows-gates/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-native-render-log-platform-matrix-windows-gates/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=windows-d3d12")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows_d3d12_render_log_compare_reason=windows-d3d12-blocked-gates-present:<missing>")
expect(evidence).to_contain("windows_d3d12_render_log_compare_blocked_gate_count=")
expect(evidence).to_contain("windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=")
```

</details>

#### rejects Windows D3D12 rows whose GPU debugger artifact file-status proof is missing

- Create pass-looking Windows D3D12 rows with a debugger artifact path but no file-status proof
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass-looking Windows D3D12 rows with a debugger artifact path but no file-status proof")
val command = "rm -rf build/test-native-render-log-platform-matrix-windows-debugger-file-status && mkdir -p build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_argb_source_gate_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_electron_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\\n' > build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_blocked_gate_count=0\\nmacos_metal_render_log_compare_blocked_gates=\\nmacos_metal_render_log_compare_generated_readback_gate_status=pass\\nmacos_metal_render_log_compare_framebuffer_readback_gate_status=pass\\nmacos_metal_render_log_compare_browser_backing_gate_status=pass\\nmacos_metal_render_log_compare_pairwise_gate_status=pass\\nmacos_metal_render_log_compare_argb_source_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace\\nmacos_metal_render_log_compare_gpu_capture_artifact_file_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE\\nmacos_metal_render_log_compare_electron_browser_backing_status=pass\\nmacos_metal_render_log_compare_chrome_browser_backing_status=pass\\nmacos_metal_render_log_compare_browser_backing_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_simple_argb_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_reason=pass\\nmacos_metal_render_log_compare_electron_argb_reason=pass\\nmacos_metal_render_log_compare_simple_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_electron_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_argb_viewport_reason=pass\\n' > build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d12\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_blocked_gate_count=0\\nwindows_d3d12_render_log_compare_blocked_gates=\\nwindows_d3d12_render_log_compare_native_readback_gate_status=pass\\nwindows_d3d12_render_log_compare_browser_backing_gate_status=pass\\nwindows_d3d12_render_log_compare_pairwise_gate_status=pass\\nwindows_d3d12_render_log_compare_argb_source_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_file_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_pix_artifact_file_magic=PIX\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log\\n' > build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-windows-debugger-file-status/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-windows-debugger-file-status/out REPORT_PATH=build/test-native-render-log-platform-matrix-windows-debugger-file-status/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-native-render-log-platform-matrix-windows-debugger-file-status/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=windows-d3d12")
expect(evidence).to_contain("windows_d3d12_render_log_compare_status=fail")
expect(evidence).to_contain("windows_d3d12_render_log_compare_reason=windows-d3d12-gpu-debugger-artifact-file-not-pass:<missing>")
expect(evidence).to_contain("windows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log")
expect(evidence).to_contain("windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status=")
```

</details>

#### rejects macOS Metal rows whose GPU capture artifact file-status proof is missing

- Create pass-looking macOS Metal rows with claimed Xcode capture magic but no file-status row
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create pass-looking macOS Metal rows with claimed Xcode capture magic but no file-status row")
val command = "rm -rf build/test-native-render-log-platform-matrix-macos-file-status && mkdir -p build/test-native-render-log-platform-matrix-macos-file-status/renderlogs && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_argb_source_gate_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_electron_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\\n' > build/test-native-render-log-platform-matrix-macos-file-status/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_blocked_gate_count=0\\nmacos_metal_render_log_compare_blocked_gates=\\nmacos_metal_render_log_compare_generated_readback_gate_status=pass\\nmacos_metal_render_log_compare_framebuffer_readback_gate_status=pass\\nmacos_metal_render_log_compare_browser_backing_gate_status=pass\\nmacos_metal_render_log_compare_pairwise_gate_status=pass\\nmacos_metal_render_log_compare_argb_source_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace\\nmacos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE\\nmacos_metal_render_log_compare_electron_browser_backing_status=pass\\nmacos_metal_render_log_compare_chrome_browser_backing_status=pass\\nmacos_metal_render_log_compare_browser_backing_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_simple_argb_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_reason=pass\\nmacos_metal_render_log_compare_electron_argb_reason=pass\\nmacos_metal_render_log_compare_simple_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_electron_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_argb_viewport_reason=pass\\n' > build/test-native-render-log-platform-matrix-macos-file-status/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d12\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_blocked_gate_count=0\\nwindows_d3d12_render_log_compare_blocked_gates=\\nwindows_d3d12_render_log_compare_native_readback_gate_status=pass\\nwindows_d3d12_render_log_compare_browser_backing_gate_status=pass\\nwindows_d3d12_render_log_compare_pairwise_gate_status=pass\\nwindows_d3d12_render_log_compare_argb_source_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_pix_artifact_file_magic=PIX\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log\\n' > build/test-native-render-log-platform-matrix-macos-file-status/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-macos-file-status/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-macos-file-status/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/test-native-render-log-platform-matrix-macos-file-status/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=build/test-native-render-log-platform-matrix-macos-file-status/out REPORT_PATH=build/test-native-render-log-platform-matrix-macos-file-status/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-native-render-log-platform-matrix-macos-file-status/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=fail")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=macos-metal")
expect(evidence).to_contain("macos_metal_render_log_compare_status=fail")
expect(evidence).to_contain("macos_metal_render_log_compare_reason=macos-metal-gpu-capture-artifact-file-not-pass:<missing>")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact=frame.gputrace")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
```

</details>

<details>
<summary>Advanced: accepts properly shaped macOS Metal Xcode capture rows in the platform matrix</summary>

#### accepts properly shaped macOS Metal Xcode capture rows in the platform matrix

- Create synthetic all-platform pass evidence with Xcode GPU capture file proof
   - Expected: code equals `0`
- Assert synthetic Xcode capture-shaped evidence satisfies only the headless contract shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create synthetic all-platform pass evidence with Xcode GPU capture file proof")
val root = "build/test-native-render-log-platform-matrix-macos-xcode-capture-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + "/renderlogs " + root + "/captures && printf 'XCODE-GPUTRACE synthetic fixture\\n' > " + root + "/captures/frame.gputrace && printf 'linux_vulkan_render_log_compare_status=pass\\nlinux_vulkan_render_log_compare_reason=pass\\nlinux_vulkan_render_log_compare_required_api=vulkan\\nlinux_vulkan_render_log_compare_blocked_gate_count=0\\nlinux_vulkan_render_log_compare_blocked_gates=\\nlinux_vulkan_render_log_compare_pairwise_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_chrome_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\\nlinux_vulkan_render_log_compare_renderdoc_electron_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\\nlinux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\\n' > " + root + "/renderlogs/linux.env && printf 'macos_metal_render_log_compare_status=pass\\nmacos_metal_render_log_compare_reason=pass\\nmacos_metal_render_log_compare_required_api=metal\\nmacos_metal_render_log_compare_pairwise_status=pass\\nmacos_metal_render_log_compare_blocked_gate_count=0\\nmacos_metal_render_log_compare_blocked_gates=\\nmacos_metal_render_log_compare_generated_readback_gate_status=pass\\nmacos_metal_render_log_compare_framebuffer_readback_gate_status=pass\\nmacos_metal_render_log_compare_browser_backing_gate_status=pass\\nmacos_metal_render_log_compare_pairwise_gate_status=pass\\nmacos_metal_render_log_compare_argb_source_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_gate_status=pass\\nmacos_metal_render_log_compare_gpu_capture_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact=" + root + "/captures/frame.gputrace\\nmacos_metal_render_log_compare_gpu_capture_artifact_file_status=pass\\nmacos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE\\nmacos_metal_render_log_compare_electron_browser_backing_status=pass\\nmacos_metal_render_log_compare_chrome_browser_backing_status=pass\\nmacos_metal_render_log_compare_browser_backing_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_status=pass\\nmacos_metal_render_log_compare_pixel_comparison_mode=pairwise-argb-diff\\nmacos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass\\nmacos_metal_render_log_compare_simple_argb_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_reason=pass\\nmacos_metal_render_log_compare_electron_argb_reason=pass\\nmacos_metal_render_log_compare_simple_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_chrome_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_electron_argb_artifact_reason=pass\\nmacos_metal_render_log_compare_argb_viewport_reason=pass\\n' > " + root + "/renderlogs/macos.env && printf 'windows_d3d12_render_log_compare_status=pass\\nwindows_d3d12_render_log_compare_reason=pass\\nwindows_d3d12_render_log_compare_required_api=d3d12\\nwindows_d3d12_render_log_compare_pairwise_status=pass\\nwindows_d3d12_render_log_compare_blocked_gate_count=0\\nwindows_d3d12_render_log_compare_blocked_gates=\\nwindows_d3d12_render_log_compare_native_readback_gate_status=pass\\nwindows_d3d12_render_log_compare_browser_backing_gate_status=pass\\nwindows_d3d12_render_log_compare_pairwise_gate_status=pass\\nwindows_d3d12_render_log_compare_argb_source_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass\\nwindows_d3d12_render_log_compare_pix_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact=frame.wpix\\nwindows_d3d12_render_log_compare_pix_artifact_file_status=pass\\nwindows_d3d12_render_log_compare_pix_artifact_magic=PIX\\nwindows_d3d12_render_log_compare_pix_artifact_file_magic=PIX\\nwindows_d3d12_render_log_compare_gpu_debugger_status=pass\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact=gpu-debugger.log\\nwindows_d3d12_render_log_compare_gpu_debugger_artifact_file_status=pass\\n' > " + root + "/renderlogs/windows.env && LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=" + root + "/renderlogs/linux.env MACOS_METAL_RENDER_LOG_COMPARE_ENV=" + root + "/renderlogs/macos.env WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=" + root + "/renderlogs/windows.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-native-render-log-platform-matrix-static-cache BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert synthetic Xcode capture-shaped evidence satisfies only the headless contract shape")
val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("native_render_log_platform_matrix_status=pass")
expect(evidence).to_contain("native_render_log_platform_matrix_missing_platforms=")
expect(evidence).to_contain("native_render_log_platform_matrix_failed_platforms=")
expect(evidence).to_contain("native_gui_platform_verification_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_reason=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_gate_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_file_status=pass")
expect(evidence).to_contain("macos_metal_render_log_compare_gpu_capture_artifact_magic=XCODE-GPUTRACE")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
