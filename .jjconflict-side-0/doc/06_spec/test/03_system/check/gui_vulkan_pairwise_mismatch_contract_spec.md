# GUI Vulkan Pairwise Mismatch Contract

> Validates that the aggregate GUI RenderDoc status gate fails closed when a pairwise ARGB diff row claims `status=pass` but reports a malformed mismatch count. A pass claim must include `mismatch_count=0`; missing or nonnumeric counts are not release-grade pixel-equivalence proof.

<!-- sdn-diagram:id=gui_vulkan_pairwise_mismatch_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_vulkan_pairwise_mismatch_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_vulkan_pairwise_mismatch_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_vulkan_pairwise_mismatch_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Vulkan Pairwise Mismatch Contract

Validates that the aggregate GUI RenderDoc status gate fails closed when a pairwise ARGB diff row claims `status=pass` but reports a malformed mismatch count. A pass claim must include `mismatch_count=0`; missing or nonnumeric counts are not release-grade pixel-equivalence proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_vulkan_pairwise_mismatch_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the aggregate GUI RenderDoc status gate fails closed when a
pairwise ARGB diff row claims `status=pass` but reports a malformed mismatch
count. A pass claim must include `mismatch_count=0`; missing or nonnumeric
counts are not release-grade pixel-equivalence proof.

The spec also protects the shared GUI/Vulkan/RenderDoc HTML fixture used by the
Linux pairwise comparison. That fixture is shared by Electron Chromium, Chrome,
and the Simple HTML renderer. Browser-only animation or WebGL mutation inside
the compared viewport makes pairwise ARGB evidence nondeterministic and can
hide real renderer differences behind capture timing drift. The fixture may
still keep marker IDs for capture tooling, but pairwise-visible probe pixels
must remain deterministic.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A malformed pairwise mismatch count is normalized to `fail`.
- The aggregate pixel comparison status is `fail`.
- The aggregate pixel comparison mode is `pairwise-argb-diff-mismatch`.
- The shared GUI/Vulkan fixture keeps bottom-right capture probes deterministic
  so pairwise ARGB comparison does not fail on animation timing drift.

## Syntax

```sh
simple test test/03_system/check/gui_vulkan_pairwise_mismatch_contract_spec.spl --mode=interpreter
```

## Operator Flow

1. Keep live GUI/web/2D Vulkan evidence under
   `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`.
2. Inspect `gui_web_2d_vulkan_*_pairwise_diff_status` and mismatch counts in
   the generated evidence before claiming browser/Simple equivalence.
3. If a pixel mismatch is localized to fixture-only diagnostics, make the
   fixture deterministic instead of relaxing the pairwise gate.
4. If mismatches remain in real widget/content regions, fix the renderer path
   and keep the aggregate failed until mismatch counts are zero.

## Failure Semantics

The aggregate must fail closed when pairwise rows are malformed, nonnumeric, or
inconsistent with checksum evidence. A diagnostic row with `status=pass` is not
trusted unless the mismatch count is numeric zero. The fixture determinism check
prevents a known false blocker: browser JavaScript updating probe pixels after
Simple has already rendered a static equivalent.

## Evidence Fields

The aggregate reads these direct-run fields for the pairwise gate:

- `gui_web_2d_vulkan_electron_argb_status`
- `gui_web_2d_vulkan_chrome_argb_status`
- `gui_web_2d_vulkan_simple_argb_status`
- `gui_web_2d_vulkan_electron_chrome_pairwise_diff_status`
- `gui_web_2d_vulkan_electron_simple_pairwise_diff_status`
- `gui_web_2d_vulkan_chrome_simple_pairwise_diff_status`
- `gui_web_2d_vulkan_electron_chrome_mismatch_count`
- `gui_web_2d_vulkan_electron_simple_mismatch_count`
- `gui_web_2d_vulkan_chrome_simple_mismatch_count`
- `gui_web_2d_vulkan_pixel_comparison_status`
- `gui_web_2d_vulkan_pixel_comparison_mode`

For a release-grade Linux Vulkan pixel-equivalence row, all three pairwise
statuses must be `pass`, all three mismatch counts must be `0`, all three ARGB
captures must have matching viewport dimensions, all three captures must be
nonblank, and checksum metadata must not contradict the pairwise result.

## Fixture Determinism

The shared fixture is intentionally dense with widget and HTML/CSS coverage, but
the compared viewport cannot contain browser-only time-varying pixels. Electron
and Chrome execute JavaScript and GPU canvas paths; Simple's HTML renderer
renders the static document model. If the fixture mutates visible pixels with
`requestAnimationFrame`, CSS animations, or WebGL clears, the same source file
can produce different ARGB buffers without a renderer bug. Keep those probe
elements hidden from the pairwise-visible viewport unless all three renderers
can produce identical pixels.

## Troubleshooting

When the aggregate reports `pairwise-argb-diff-mismatch`, inspect each diff
bounding box before editing renderer code:

- A small box pinned to the fixture diagnostics area usually means fixture
  nondeterminism or browser-only probe pixels.
- A box inside a real widget/content area should be treated as a Simple renderer
  mismatch until proven otherwise.
- A browser-browser mismatch means Electron and Chrome are not a stable
  reference pair; fix capture timing or fixture determinism first.
- A Simple-only excess over the browser-browser floor means the Simple renderer
  differs beyond normal browser drift and the renderer path needs work.

## Completion Boundaries

This spec does not prove RenderDoc `.rdc` capture, macOS Metal, Windows D3D12,
production GUI/web parity, full CSS rendering, or 4K/8K performance. It protects
one prerequisite: the Linux GUI/web/2D Vulkan ARGB pixel-equivalence gate must
be strict and deterministic enough that a `pass` row means actual pixel parity.

## Scenarios

### GUI Vulkan pairwise mismatch contract

#### keeps the shared Vulkan capture fixture deterministic for pairwise ARGB

- Read the shared RenderDoc/Vulkan HTML fixture
- Assert capture probe pixels do not mutate per animation frame
   - Expected: fixture does not contain `window.requestAnimationFrame(frame)`
   - Expected: fixture does not contain `animation: rdoc-capture-pulse`
   - Expected: fixture does not contain `tick = (tick +`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the shared RenderDoc/Vulkan HTML fixture")
val fixture = file_read("test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")

step("Assert capture probe pixels do not mutate per animation frame")
expect(fixture).to_contain("#rdoc-frame-pulse")
expect(fixture).to_contain("#rdoc-webgl-pulse")
expect(fixture).to_contain("display: none;")
expect(fixture).to_contain("background-color: #2363eb;")
expect(fixture).to_contain("gl.clearColor(35 / 255, 99 / 255, 235 / 255, 1);")
expect(fixture.contains("window.requestAnimationFrame(frame)")).to_equal(false)
expect(fixture.contains("animation: rdoc-capture-pulse")).to_equal(false)
expect(fixture.contains("tick = (tick +")).to_equal(false)
```

</details>

#### rejects pass pairwise rows with malformed mismatch counts

- Create direct-run Vulkan ARGB evidence with one malformed mismatch count
   - Expected: code equals `0`
- Assert malformed mismatch evidence is a hard pairwise failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create direct-run Vulkan ARGB evidence with one malformed mismatch count")
val command = "rm -rf build/test-gui-vulkan-pairwise-malformed-mismatch && mkdir -p build/test-gui-vulkan-pairwise-malformed-mismatch/run build/test-gui-vulkan-pairwise-malformed-mismatch/simple && printf '{\"width\":1280,\"height\":720,\"format\":\"argb-u32\",\"producer\":\"electron-vulkan-capture\",\"pixels\":[4294967295]}\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/electron_argb.json && printf '{\"width\":1280,\"height\":720,\"format\":\"argb-u32\",\"producer\":\"chrome-vulkan-capture\",\"pixels\":[4294967295]}\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/chrome_argb.json && printf '{\"width\":1280,\"height\":720,\"format\":\"argb-u32\",\"producer\":\"simple-vulkan-web2d\",\"pixels\":[4294967295]}\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/simple_argb.json && printf 'mismatch_count=not-a-number\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/electron_chrome_diff.env && printf 'mismatch_count=0\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/electron_simple_diff.env && printf 'mismatch_count=0\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/chrome_simple_diff.env && printf 'vulkan_engine2d_readback_status=pass\\nvulkan_engine2d_readback_reason=pass\\nvulkan_engine2d_readback_spec_status=pass\\nvulkan_engine2d_readback_clear_status=pass\\nvulkan_engine2d_readback_rect_status=pass\\nvulkan_engine2d_readback_clear_mismatches=0\\nvulkan_engine2d_readback_rect_mismatches=0\\nvulkan_engine2d_readback_blur_or_tolerance_used=false\\nvulkan_engine2d_readback_vulkan_strict_exit_code=0\\nvulkan_engine2d_readback_cpu_vulkan_parity_exit_code=0\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/simple/evidence.env && printf 'gui_web_2d_vulkan_mode=--run\\ngui_web_2d_vulkan_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\ngui_web_2d_vulkan_width=1280\\ngui_web_2d_vulkan_height=720\\ngui_web_2d_vulkan_simple_status=pass\\ngui_web_2d_vulkan_simple_reason=pass\\ngui_web_2d_vulkan_simple_evidence_env=build/test-gui-vulkan-pairwise-malformed-mismatch/simple/evidence.env\\ngui_web_2d_vulkan_simple_probe_status=Initialized\\ngui_web_2d_vulkan_simple_backend_name=vulkan\\ngui_web_2d_vulkan_electron_argb_status=pass\\ngui_web_2d_vulkan_electron_argb_path=build/test-gui-vulkan-pairwise-malformed-mismatch/run/electron_argb.json\\ngui_web_2d_vulkan_electron_argb_width=1280\\ngui_web_2d_vulkan_electron_argb_height=720\\ngui_web_2d_vulkan_electron_argb_nonblank_pixel_count=1\\ngui_web_2d_vulkan_chrome_argb_status=pass\\ngui_web_2d_vulkan_chrome_argb_path=build/test-gui-vulkan-pairwise-malformed-mismatch/run/chrome_argb.json\\ngui_web_2d_vulkan_chrome_argb_width=1280\\ngui_web_2d_vulkan_chrome_argb_height=720\\ngui_web_2d_vulkan_chrome_argb_nonblank_pixel_count=1\\ngui_web_2d_vulkan_simple_argb_status=pass\\ngui_web_2d_vulkan_simple_argb_path=build/test-gui-vulkan-pairwise-malformed-mismatch/run/simple_argb.json\\ngui_web_2d_vulkan_simple_argb_width=1280\\ngui_web_2d_vulkan_simple_argb_height=720\\ngui_web_2d_vulkan_simple_argb_nonblank_pixel_count=1\\ngui_web_2d_vulkan_electron_chrome_diff_status=pass\\ngui_web_2d_vulkan_electron_chrome_diff_reason=pass\\ngui_web_2d_vulkan_electron_chrome_mismatch_count=not-a-number\\ngui_web_2d_vulkan_electron_chrome_diff_path=build/test-gui-vulkan-pairwise-malformed-mismatch/run/electron_chrome_diff.env\\ngui_web_2d_vulkan_electron_simple_diff_status=pass\\ngui_web_2d_vulkan_electron_simple_diff_reason=pass\\ngui_web_2d_vulkan_electron_simple_mismatch_count=0\\ngui_web_2d_vulkan_electron_simple_diff_path=build/test-gui-vulkan-pairwise-malformed-mismatch/run/electron_simple_diff.env\\ngui_web_2d_vulkan_chrome_simple_diff_status=pass\\ngui_web_2d_vulkan_chrome_simple_diff_reason=pass\\ngui_web_2d_vulkan_chrome_simple_mismatch_count=0\\ngui_web_2d_vulkan_chrome_simple_diff_path=build/test-gui-vulkan-pairwise-malformed-mismatch/run/chrome_simple_diff.env\\n' > build/test-gui-vulkan-pairwise-malformed-mismatch/run/evidence.env && GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV=build/test-gui-vulkan-pairwise-malformed-mismatch/run/evidence.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-vulkan-pairwise-malformed-mismatch/out REPORT_PATH=build/test-gui-vulkan-pairwise-malformed-mismatch/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert malformed mismatch evidence is a hard pairwise failure")
val evidence = file_read("build/test-gui-vulkan-pairwise-malformed-mismatch/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_chrome_mismatch_count=not-a-number")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass")
expect(evidence).to_contain("gui_web_2d_vulkan_pixel_comparison_status=fail")
expect(evidence).to_contain("gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff-mismatch")
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
