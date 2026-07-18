# GUI Showcase Perf Retained Mode Contract

> Validates that the GUI RenderDoc aggregate derives retained static-frame proof from raw 4K/8K showcase evidence instead of trusting producer-side pass rows for render mode or redraw count.

<!-- sdn-diagram:id=gui_showcase_perf_retained_mode_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_retained_mode_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_retained_mode_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_retained_mode_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Retained Mode Contract

Validates that the GUI RenderDoc aggregate derives retained static-frame proof from raw 4K/8K showcase evidence instead of trusting producer-side pass rows for render mode or redraw count.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_retained_mode_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the GUI RenderDoc aggregate derives retained static-frame proof
from raw 4K/8K showcase evidence instead of trusting producer-side pass rows for
render mode or redraw count.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_retained_mode_contract_spec.spl --mode=interpreter
```

## Operator Flow

1. Run this focused spec after changing retained-showcase mode or redraw checks
   in `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.
2. Inspect `build/test-gui-showcase-perf-retained-mode-4k/out/evidence.env` for
   the retained 4K aggregate result.
3. Inspect `build/test-gui-showcase-perf-retained-mode-8k/out/evidence.env` for
   the retained 8K aggregate result.
4. Treat any malformed `render_mode` or `redraw_frames` row that still reports
   aggregate `pass` as a completion-gate regression.

## Acceptance

- A retained 4K row with non-retained render mode and a forged retained-mode
  pass is downgraded to `fail`.
- A retained 4K row with redraw count other than one and a forged redraw pass is
  downgraded to `fail`.
- A retained 8K row with the same forged statuses is downgraded to `fail`.
- Raw evidence values win over producer-side `*_retained_*_status=pass`.

## Test Matrix

The 4K case creates a complete synthetic retained-showcase row, including FPS,
timing, RSS, checksum, source revision, native binary, alias source, build log,
showcase log, and time log artifacts. The invalid fields are:

- `gui_showcase_4k_200fps_render_mode=immediate-redraw`
- `gui_showcase_4k_200fps_retained_render_mode_status=pass`
- `gui_showcase_4k_200fps_redraw_frames=2`
- `gui_showcase_4k_200fps_retained_redraw_status=pass`

The aggregate must emit:

- `gui_showcase_4k_200fps_status=fail`
- `gui_showcase_4k_200fps_retained_render_mode_status=fail`
- `gui_showcase_4k_200fps_retained_redraw_status=fail`
- `gui_showcase_4k_200fps_reason=not-retained-4k-render-mode:immediate-redraw;redraw_frames=2`

The 8K case mirrors the same proof with the `gui_showcase_8k_perf_*` evidence
keys and must emit the matching `fail` statuses and
`not-retained-8k-render-mode:immediate-redraw;redraw_frames=2` reason.

## Evidence Keys

The spec validates these 4K aggregate keys:

- `gui_showcase_4k_200fps_status`
- `gui_showcase_4k_200fps_reason`
- `gui_showcase_4k_200fps_render_mode`
- `gui_showcase_4k_200fps_retained_render_mode_status`
- `gui_showcase_4k_200fps_redraw_frames`
- `gui_showcase_4k_200fps_retained_redraw_status`

The spec validates these 8K aggregate keys:

- `gui_showcase_8k_perf_status`
- `gui_showcase_8k_perf_reason`
- `gui_showcase_8k_perf_render_mode`
- `gui_showcase_8k_perf_retained_render_mode_status`
- `gui_showcase_8k_perf_redraw_frames`
- `gui_showcase_8k_perf_retained_redraw_status`

## Failure Semantics

This spec is fail-closed. A producer-provided retained-mode or redraw status is
accepted only after the aggregate derives that the raw mode equals
`retained-static-frame` and the raw redraw count equals `1`. Any other value is
not valid 4K/8K retained static-frame completion evidence.

## Troubleshooting

If this spec fails with missing native artifacts, check the synthetic ELF file,
alias source, and build log paths in the generated `status.env`. If it fails
with missing log artifacts, inspect the generated `source/showcase.log` and
`source/time.log` files. If it fails by returning aggregate `pass`, the
aggregate is trusting producer-provided retained-mode status before validating
the raw mode and redraw values.

## Relation To Performance Gates

The real 4K and 8K performance wrappers may still report richer diagnostic
status text from the producer. This contract only prevents producer `pass` from
overriding raw evidence that proves the showcase was not retained static-frame
rendering or redrew more than once.

## Completion Boundary

This test covers aggregate validation of retained-showcase mode and redraw
evidence only. It does not prove real 4K/8K throughput, browser GPU backing,
platform render-log comparison, or RenderDoc capture validity.

## Scenarios

### GUI showcase perf retained mode contract

#### rejects retained 4K rows with forged render-mode and redraw pass statuses

- Create a 4K performance row with forged retained-mode evidence
   - Expected: code equals `0`
- Assert the aggregate rejects the forged retained-mode proof
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_retained_render_mode_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_retained_redraw_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `not-retained-4k-render-mode:immediate-redraw;redraw_frames=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a 4K performance row with forged retained-mode evidence")
val command = "rm -rf build/test-gui-showcase-perf-retained-mode-4k && mkdir -p build/test-gui-showcase-perf-retained-mode-4k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-retained-mode-4k/source/native4k.bin && chmod +x build/test-gui-showcase-perf-retained-mode-4k/source/native4k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-retained-mode-4k/source/build4k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-retained-mode-4k/source/showcase4k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-retained-mode-4k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-retained-mode-4k/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\ngui_showcase_4k_200fps_reason=met-target-fps\ngui_showcase_4k_200fps_resolution=4k\ngui_showcase_4k_200fps_width=3840\ngui_showcase_4k_200fps_height=2160\ngui_showcase_4k_200fps_frames=200\ngui_showcase_4k_200fps_fps_x1000=201000\ngui_showcase_4k_200fps_frame_avg_ns=4975124\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\ngui_showcase_4k_200fps_frame_p50_ns=4975124\ngui_showcase_4k_200fps_frame_p95_ns=4975124\ngui_showcase_4k_200fps_target_fps=200\ngui_showcase_4k_200fps_max_rss_kb=131072\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\ngui_showcase_4k_200fps_rss_status=pass\ngui_showcase_4k_200fps_pixels=8294400\ngui_showcase_4k_200fps_nonzero_pixels=1000\ngui_showcase_4k_200fps_checksum=123456\ngui_showcase_4k_200fps_render_mode=immediate-redraw\ngui_showcase_4k_200fps_retained_render_mode_status=pass\ngui_showcase_4k_200fps_redraw_frames=2\ngui_showcase_4k_200fps_retained_redraw_status=pass\ngui_showcase_4k_200fps_source_revision=testrev123\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-retained-mode-4k/source/native4k.bin\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-retained-mode-4k/source/showcase4k.spl\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-retained-mode-4k/source/build4k.log\ngui_showcase_4k_200fps_use_native=1\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\ngui_showcase_4k_200fps_fallback_state=none\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-retained-mode-4k/source/showcase.log\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-retained-mode-4k/source/time.log\n' > build/test-gui-showcase-perf-retained-mode-4k/source/status.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-retained-mode-4k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-retained-mode-4k/out REPORT_PATH=build/test-gui-showcase-perf-retained-mode-4k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate rejects the forged retained-mode proof")
val evidence = file_read("build/test-gui-showcase-perf-retained-mode-4k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_retained_render_mode_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_retained_redraw_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("not-retained-4k-render-mode:immediate-redraw;redraw_frames=2")
```

</details>

#### rejects retained 8K rows with forged render-mode and redraw pass statuses

- Create an 8K performance row with forged retained-mode evidence
   - Expected: code equals `0`
- Assert the aggregate rejects the forged retained-mode proof
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_retained_render_mode_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_retained_redraw_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_reason") equals `not-retained-8k-render-mode:immediate-redraw;redraw_frames=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an 8K performance row with forged retained-mode evidence")
val command = "rm -rf build/test-gui-showcase-perf-retained-mode-8k && mkdir -p build/test-gui-showcase-perf-retained-mode-8k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-retained-mode-8k/source/native8k.bin && chmod +x build/test-gui-showcase-perf-retained-mode-8k/source/native8k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-retained-mode-8k/source/build8k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-retained-mode-8k/source/showcase8k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-retained-mode-8k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-retained-mode-8k/source/time.log && printf 'gui_showcase_8k_perf_status=pass\ngui_showcase_8k_perf_reason=met-target-fps\ngui_showcase_8k_perf_resolution=8k\ngui_showcase_8k_perf_width=7680\ngui_showcase_8k_perf_height=4320\ngui_showcase_8k_perf_frames=200\ngui_showcase_8k_perf_fps_x1000=201000\ngui_showcase_8k_perf_frame_avg_ns=4975124\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\ngui_showcase_8k_perf_frame_p50_ns=4975124\ngui_showcase_8k_perf_frame_p95_ns=4975124\ngui_showcase_8k_perf_target_fps=200\ngui_showcase_8k_perf_max_rss_kb=524288\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\ngui_showcase_8k_perf_rss_status=pass\ngui_showcase_8k_perf_pixels=33177600\ngui_showcase_8k_perf_nonzero_pixels=1000\ngui_showcase_8k_perf_checksum=123456\ngui_showcase_8k_perf_render_mode=immediate-redraw\ngui_showcase_8k_perf_retained_render_mode_status=pass\ngui_showcase_8k_perf_redraw_frames=2\ngui_showcase_8k_perf_retained_redraw_status=pass\ngui_showcase_8k_perf_source_revision=testrev123\ngui_showcase_8k_perf_source_revision_kind=content-sha256\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\ngui_showcase_8k_perf_native_bin=build/test-gui-showcase-perf-retained-mode-8k/source/native8k.bin\ngui_showcase_8k_perf_alias_src=build/test-gui-showcase-perf-retained-mode-8k/source/showcase8k.spl\ngui_showcase_8k_perf_native_build_log=build/test-gui-showcase-perf-retained-mode-8k/source/build8k.log\ngui_showcase_8k_perf_use_native=1\ngui_showcase_8k_perf_native_build_mode=aggressive-native\ngui_showcase_8k_perf_fallback_state=none\ngui_showcase_8k_perf_log=build/test-gui-showcase-perf-retained-mode-8k/source/showcase.log\ngui_showcase_8k_perf_time_log=build/test-gui-showcase-perf-retained-mode-8k/source/time.log\n' > build/test-gui-showcase-perf-retained-mode-8k/source/status.env && GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-showcase-perf-retained-mode-8k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-retained-mode-8k/out REPORT_PATH=build/test-gui-showcase-perf-retained-mode-8k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate rejects the forged retained-mode proof")
val evidence = file_read("build/test-gui-showcase-perf-retained-mode-8k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_retained_render_mode_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_retained_redraw_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_reason")).to_equal("not-retained-8k-render-mode:immediate-redraw;redraw_frames=2")
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
