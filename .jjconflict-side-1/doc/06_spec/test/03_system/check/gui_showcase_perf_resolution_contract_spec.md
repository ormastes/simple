# GUI Showcase Perf Resolution Contract

> Validates that retained 4K and 8K GUI showcase performance evidence must name the matching resolution label. Width, height, and pixel count are necessary but not sufficient; the aggregate should reject a row whose `resolution` field contradicts the measured viewport class.

<!-- sdn-diagram:id=gui_showcase_perf_resolution_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_resolution_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_resolution_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_resolution_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Resolution Contract

Validates that retained 4K and 8K GUI showcase performance evidence must name the matching resolution label. Width, height, and pixel count are necessary but not sufficient; the aggregate should reject a row whose `resolution` field contradicts the measured viewport class.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/ui/web_render_backend.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_resolution_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K and 8K GUI showcase performance evidence must name
the matching resolution label. Width, height, and pixel count are necessary but
not sufficient; the aggregate should reject a row whose `resolution` field
contradicts the measured viewport class.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/ui/web_render_backend.md

## Acceptance

- A retained 4K row with `resolution=8k` is normalized to `fail`.
- A retained 8K row with `resolution=4k` is normalized to `fail`.
- The failure reason names the invalid resolution field.

## Syntax

The aggregate receives showcase status rows from `GUI_SHOWCASE_4K_PERF_ENV` and
`GUI_SHOWCASE_8K_PERF_ENV`. The row prefix selects the expected evidence
contract: 4K rows must report the 4K resolution label with 3840x2160 geometry,
and 8K rows must report the 8K resolution label with 7680x4320 geometry.

This fixture keeps timing, RSS, checksum, nonzero-pixel, native-binary, and
retained-mode proof valid. It also emits `*_frame_elapsed_ns_status=pass` so the
timing trust gate does not mask the resolution failure under test. The only
intentional contradiction is the swapped `resolution` label.

## Examples

Given a `gui_showcase_4k_200fps_*` row that reports `resolution=8k`, the
aggregate emits a failed 4K status and an `invalid-4k-resolution` reason.

Given a `gui_showcase_8k_perf_*` row that reports `resolution=4k`, the
aggregate emits a failed 8K status and an `invalid-8k-resolution` reason.

This prevents a producer from satisfying the 8K performance evidence contract
with a mislabeled lower-resolution row.

## Fixture Shape

The synthetic rows create native binary placeholders, source placeholders, build
logs, showcase logs, and time logs before invoking the aggregate script. These
artifact references mirror the production retained showcase wrapper closely
enough for the aggregate to exercise its normal trust checks without requiring a
GPU host during this system test.

The 4K row keeps 3840x2160 dimensions and 8,294,400 pixels while intentionally
reporting the `8k` label. The 8K row keeps 7680x4320 dimensions and 33,177,600
pixels while intentionally reporting the `4k` label. Both rows otherwise use
valid timing, RSS, checksum, nonzero-pixel, retained-mode, source, native, and
fallback fields.

## Failure Ordering

Resolution validation should run after basic row trust checks have enough proof
to treat the row as a real retained showcase candidate. The fixture therefore
includes `*_frame_elapsed_ns_status=pass`, valid native binary markers, valid
artifact paths, and retained static frame evidence. If any of those surrounding
fields are missing, the aggregate may fail for the wrong reason and the
resolution assertions will no longer prove the intended behavior.

The assertion checks the final status and the exact invalid-resolution reason
for both 4K and 8K rows. That prevents a broad fail result from hiding a
regression in the resolution classifier itself.

## Debugging

When this scenario fails, inspect
`build/test-gui-showcase-perf-resolution-contract/out/evidence.env`. The
important keys are `gui_showcase_4k_200fps_resolution`,
`gui_showcase_4k_200fps_reason`, `gui_showcase_8k_perf_resolution`, and
`gui_showcase_8k_perf_reason`.

If the reason mentions timing, checksum, source revision, RSS, native binary
format, nonzero pixels, or retained redraw status, refresh the fixture so the
resolution classifier is the first failing gate again.

## Evidence Checklist

- `*_status=fail` proves the mislabeled row cannot pass the release gate.
- `*_reason=invalid-*-resolution:*` proves the resolution classifier selected
  the failure reason.
- `*_width`, `*_height`, and `*_pixels` stay valid so the test isolates the
  label mismatch instead of geometry parsing.
- `*_frame_elapsed_ns_status=pass` proves timing trust did not mask resolution
  validation.
- `*_checksum_status=pass` and parseable checksum text prove readback proof did
  not mask resolution validation.
- `*_retained_render_mode_status=pass` and `*_retained_redraw_status=pass`
  prove retained rendering did not mask resolution validation.
- The 4K and 8K rows are both checked because either prefix can regress
  independently in the aggregate script.

The expected output must remain deterministic across Linux, macOS, and Windows
because this contract validates aggregate text processing, not platform GPU
capture behavior.

## Scenarios

### GUI showcase perf resolution contract

#### rejects retained 4K and 8K rows with contradictory resolution labels

- Create retained perf rows with valid geometry but wrong resolution labels
- "printf 'fn main
   - Expected: code equals `0`
- Assert resolution labels must match the retained perf row


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create retained perf rows with valid geometry but wrong resolution labels")
val command = "rm -rf build/test-gui-showcase-perf-resolution-contract && mkdir -p build/test-gui-showcase-perf-resolution-contract/4k build/test-gui-showcase-perf-resolution-contract/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > build/test-gui-showcase-perf-resolution-contract/4k/native.bin && chmod +x build/test-gui-showcase-perf-resolution-contract/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > build/test-gui-showcase-perf-resolution-contract/8k/native.bin && chmod +x build/test-gui-showcase-perf-resolution-contract/8k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > build/test-gui-showcase-perf-resolution-contract/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > build/test-gui-showcase-perf-resolution-contract/8k/showcase.spl && " +
    "printf 'native build log\\n' > build/test-gui-showcase-perf-resolution-contract/4k/build.log && printf 'native build log\\n' > build/test-gui-showcase-perf-resolution-contract/8k/build.log && " +
    "printf 'showcase retained log\\n' > build/test-gui-showcase-perf-resolution-contract/4k/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-showcase-perf-resolution-contract/4k/time.log && " +
    "printf 'showcase retained log\\n' > build/test-gui-showcase-perf-resolution-contract/8k/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-showcase-perf-resolution-contract/8k/time.log && " +
    "printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-200fps\\ngui_showcase_4k_200fps_resolution=8k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_nonzero_pixels_status=pass\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_checksum_status=pass\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=testrev123\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-resolution-contract/4k/native.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-resolution-contract/4k/showcase.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-resolution-contract/4k/build.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-resolution-contract/4k/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-resolution-contract/4k/time.log\\n' > build/test-gui-showcase-perf-resolution-contract/4k/status.env && " +
    "printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_resolution=4k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_nonzero_pixels_status=pass\\ngui_showcase_8k_perf_checksum=123456\\ngui_showcase_8k_perf_checksum_status=pass\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=testrev123\\ngui_showcase_8k_perf_source_revision_kind=content-sha256\\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-showcase-perf-resolution-contract/8k/native.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-showcase-perf-resolution-contract/8k/showcase.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-showcase-perf-resolution-contract/8k/build.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-showcase-perf-resolution-contract/8k/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-showcase-perf-resolution-contract/8k/time.log\\n' > build/test-gui-showcase-perf-resolution-contract/8k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-resolution-contract/4k/status.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-showcase-perf-resolution-contract/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-resolution-contract/out REPORT_PATH=build/test-gui-showcase-perf-resolution-contract/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert resolution labels must match the retained perf row")
val evidence = file_read("build/test-gui-showcase-perf-resolution-contract/out/evidence.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_resolution=8k")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-resolution-field:8k")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_resolution=4k")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=invalid-8k-resolution-field:4k")
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
- **Design:** [doc/07_guide/ui/web_render_backend.md](doc/07_guide/ui/web_render_backend.md)


</details>
