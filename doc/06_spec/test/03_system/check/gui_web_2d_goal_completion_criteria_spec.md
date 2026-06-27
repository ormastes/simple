# GUI/Web/2D Goal Completion Criteria

> This SSpec is the executable checklist for the active GUI/Web/2D hardening goal. Remaining platform lanes use explicit failing expectations until a platform agent replaces each placeholder with a real evidence-backed assertion; the retained 4K/8K perf lane now runs strict aggregate assertions.

<!-- sdn-diagram:id=gui_web_2d_goal_completion_criteria_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_goal_completion_criteria_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_goal_completion_criteria_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_goal_completion_criteria_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Goal Completion Criteria

This SSpec is the executable checklist for the active GUI/Web/2D hardening goal. Remaining platform lanes use explicit failing expectations until a platform agent replaces each placeholder with a real evidence-backed assertion; the retained 4K/8K perf lane now runs strict aggregate assertions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec is the executable checklist for the active GUI/Web/2D hardening
goal. Remaining platform lanes use explicit failing expectations until a
platform agent replaces each placeholder with a real evidence-backed assertion.
The retained 4K/8K perf lane now runs strict aggregate assertions against
current-source evidence.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Completion Rule

The overall goal is not complete until every scenario in this spec has
evidence-backed assertions over current evidence and passes. Passing the
retained perf lane, narrow renderer slices, or non-RenderDoc browser Vulkan rows
does not complete the goal by itself.

## Acceptance

- Linux Vulkan completion proves Chrome, Electron, and Simple Vulkan backing,
  pairwise nonblank ARGB equivalence, and valid RenderDoc `.rdc` artifacts with
  `RDOC` magic for all required lanes.
- macOS Metal completion proves native Metal readback, browser/gui backing,
  pairwise equivalence, and Xcode GPU Capture evidence when capture is required.
- Windows D3D12 completion proves native D3D12/DXGI readback, browser/gui
  backing, pairwise equivalence, verified PIX artifact files, and verified GPU
  debugger artifact files.
- 4K and 8K showcase completion proves current-source retained rows at 200 FPS
  with timing, RSS, checksum/readback, viewport, native binary provenance,
  retained mode, redraw count, and `fallback_state=none`.
- Full HTML/CSS completion proves all inventory CSS properties are rendered,
  not only the implemented Simple Web subset.
- Production GUI/Web parity completion proves same-frame backend readback,
  positive backend handles, matching checksums, and no CPU-mirror-only pass.
- Parallel-agent completion records Spark or fallback sidecar outputs plus
  normal/high-capability review before accepting broad findings or done marks.

## Scenarios

### GUI/Web/2D goal completion criteria

#### requires Linux Vulkan RenderDoc completion with current Chrome Electron and Simple evidence

- Verify Linux Vulkan browser backing, Simple backend proof, pairwise ARGB equivalence, and RDOC artifacts
- verify linux vulkan renderdoc completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify Linux Vulkan browser backing, Simple backend proof, pairwise ARGB equivalence, and RDOC artifacts")
verify_linux_vulkan_renderdoc_completion()
```

</details>

#### requires macOS Metal completion with native readback and GPU capture evidence

- Verify macOS Metal readback, browser/gui backing, pairwise equivalence, and capture artifact proof
- verify macos metal completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify macOS Metal readback, browser/gui backing, pairwise equivalence, and capture artifact proof")
verify_macos_metal_completion()
```

</details>

#### requires Windows D3D12 completion with verified PIX and GPU debugger evidence

- Verify Windows D3D12 readback, browser/gui backing, pairwise equivalence, verified PIX files, and verified debugger files
- verify windows d3d12 completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify Windows D3D12 readback, browser/gui backing, pairwise equivalence, verified PIX files, and verified debugger files")
verify_windows_d3d12_completion()
```

</details>

#### requires retained 4K and 8K GUI showcase performance at current source revision

- Verify current-source 4K and 8K retained rows include FPS, timing, RSS, checksum/readback, native provenance, retained mode, redraw count, and no fallback
- verify retained 4k 8k perf completion
- Run `check-gui-renderdoc-feature-coverage-status.shs` with `GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1`
- Assert both retained rows are `pass`, current-source, self-hosted release native builds, retained static frames, one redraw, nonfallback, nonblank, checksummed, within RSS budget, and at least 200 FPS across at least 200 frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 key checks folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify current-source 4K and 8K retained rows include FPS, timing, RSS, checksum/readback, native provenance, retained mode, redraw count, and no fallback")
verify_retained_4k_8k_perf_completion()
assert_retained_perf_row(evidence, "gui_showcase_4k_200fps", "4k", "3840", "2160", "8294400", "262144")
assert_retained_perf_row(evidence, "gui_showcase_8k_perf", "8k", "7680", "4320", "33177600", "750000")
```

</details>

#### requires full HTML and CSS rendering inventory completion

- Verify all HTML tags and every CSS inventory property are rendered, with strict mode passing
- verify full html css completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify all HTML tags and every CSS inventory property are rendered, with strict mode passing")
verify_full_html_css_completion()
```

</details>

#### requires production GUI/Web renderer parity with backend readback

- Verify production GUI/Web parity uses same-frame backend readback, positive handles, and matching checksums
- verify production gui web parity completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify production GUI/Web parity uses same-frame backend readback, positive handles, and matching checksums")
verify_production_gui_web_parity_completion()
```

</details>

#### requires parallel-agent work to have Spark or fallback output and higher-capability review

- Verify sidecar outputs are reviewed before any broad completion claim is accepted
- verify parallel agent review completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify sidecar outputs are reviewed before any broad completion claim is accepted")
verify_parallel_agent_review_completion()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
