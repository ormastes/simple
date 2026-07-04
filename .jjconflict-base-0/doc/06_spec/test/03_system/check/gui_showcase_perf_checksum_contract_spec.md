# GUI Showcase Perf Checksum Contract

> Validates that retained 4K and 8K GUI showcase performance evidence cannot claim pass with a malformed checksum, even when the row also reports `checksum_status=pass`. The aggregate must verify the checksum text itself so a status-only row cannot masquerade as readback proof.

<!-- sdn-diagram:id=gui_showcase_perf_checksum_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_checksum_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_checksum_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_checksum_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Checksum Contract

Validates that retained 4K and 8K GUI showcase performance evidence cannot claim pass with a malformed checksum, even when the row also reports `checksum_status=pass`. The aggregate must verify the checksum text itself so a status-only row cannot masquerade as readback proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/ui/web_render_backend.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_checksum_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K and 8K GUI showcase performance evidence cannot
claim pass with a malformed checksum, even when the row also reports
`checksum_status=pass`. The aggregate must verify the checksum text itself so a
status-only row cannot masquerade as readback proof.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/ui/web_render_backend.md

## Acceptance

- A retained 4K row with a nonnumeric checksum is normalized to `fail`.
- A retained 8K row with a nonnumeric checksum is normalized to `fail`.
- The failure reason names the invalid readback checksum.

## Syntax

The aggregate accepts one status environment file per showcase row through
`GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`. Each row must include
retained timing keys, readback keys, native build proof, source revision
metadata, and `*_frame_elapsed_ns_status=pass` when it claims trusted timing.
This scenario keeps those surrounding gates valid so the malformed checksum is
the first failure reported by the aggregate.

The checksum contract is intentionally defensive. A producer may emit
`*_checksum_status=pass`, but the aggregate still parses the checksum value
itself. Text such as `not-a-number` or `also-bad` is not valid readback proof
and must be normalized to a failed checksum status.

## Examples

Given a retained 4K row with `checksum=not-a-number`, the aggregate emits
`gui_showcase_4k_200fps_status=fail` and an
`invalid-4k-readback-checksum` reason.

Given a retained 8K row with `checksum=also-bad`, the aggregate emits
`gui_showcase_8k_perf_status=fail` and an
`invalid-8k-readback-checksum` reason.

This prevents cached, status-only, or hand-written fixture evidence from
masquerading as real GUI showcase readback proof.

## Fixture Shape

The synthetic rows create executable native placeholders, source placeholders,
build logs, showcase logs, and time logs before invoking the aggregate script.
Those files are present because the production aggregate verifies artifact
presence along with status text. The test does not depend on a GPU host, but it
does preserve the same file references that a real retained 4K or 8K showcase
run would publish.

The fixture deliberately sets valid frame counts, target FPS, average frame
time, percentile frame time, RSS budget, pixel count, nonzero pixel proof,
retained render mode, one redraw frame, native build mode, and fallback state.
That isolates checksum parsing from unrelated performance or platform gates.

## Failure Ordering

The aggregate reports the first release-blocking reason that makes a retained
showcase row untrusted. If timing evidence is missing, timing must fail before
checksum. If native proof is missing, native proof may fail before checksum.
This contract therefore includes trusted timing and native artifact proof so a
malformed checksum remains the selected reason.

The assertion checks both the normalized status field and the rendered reason.
That catches regressions where the aggregate notices the bad value internally
but leaves the row status as pass, and it catches regressions where the row
fails without explaining which readback field was invalid.

## Debugging

When this scenario fails, inspect
`build/test-gui-showcase-perf-checksum-contract/out/evidence.env`. The relevant
keys are `gui_showcase_4k_200fps_checksum`,
`gui_showcase_4k_200fps_checksum_status`,
`gui_showcase_4k_200fps_reason`, `gui_showcase_8k_perf_checksum`,
`gui_showcase_8k_perf_checksum_status`, and `gui_showcase_8k_perf_reason`.

If the reason mentions frame timing, source revision, native binary format, RSS,
resolution, nonzero pixels, or retained redraw status, then this fixture is no
longer isolating the checksum gate and should be refreshed before changing the
aggregate behavior.

## Evidence Checklist

- `*_status=fail` proves the row cannot pass the release gate.
- `*_checksum_status=fail` proves the checksum parser rejected the text.
- `*_reason=invalid-*-readback-checksum:*` proves the checksum gate selected
  the failure reason.
- `*_frame_elapsed_ns_status=pass` proves timing trust did not mask checksum
  validation.
- `*_retained_render_mode_status=pass` and `*_retained_redraw_status=pass`
  prove retained rendering did not mask checksum validation.
- `*_native_bin_format_status=pass` proves the native binary placeholder was
  accepted by the aggregate.
- The 4K and 8K rows are both checked because a regression can affect one
  prefix without affecting the other.

## Scenarios

### GUI showcase perf checksum contract

#### rejects malformed retained 4K and 8K checksum proof

- Create retained 4K and 8K perf rows with contradictory checksum status
- "printf 'fn main
   - Expected: code equals `0`
- Assert malformed checksum text overrides status-only pass claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create retained 4K and 8K perf rows with contradictory checksum status")
val command = "rm -rf build/test-gui-showcase-perf-checksum-contract && mkdir -p build/test-gui-showcase-perf-checksum-contract/4k build/test-gui-showcase-perf-checksum-contract/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > build/test-gui-showcase-perf-checksum-contract/4k/native.bin && chmod +x build/test-gui-showcase-perf-checksum-contract/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > build/test-gui-showcase-perf-checksum-contract/8k/native.bin && chmod +x build/test-gui-showcase-perf-checksum-contract/8k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > build/test-gui-showcase-perf-checksum-contract/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > build/test-gui-showcase-perf-checksum-contract/8k/showcase.spl && " +
    "printf 'native build log\\n' > build/test-gui-showcase-perf-checksum-contract/4k/build.log && printf 'native build log\\n' > build/test-gui-showcase-perf-checksum-contract/8k/build.log && " +
    "printf 'showcase retained log\\n' > build/test-gui-showcase-perf-checksum-contract/4k/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-showcase-perf-checksum-contract/4k/time.log && " +
    "printf 'showcase retained log\\n' > build/test-gui-showcase-perf-checksum-contract/8k/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-showcase-perf-checksum-contract/8k/time.log && " +
    "printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-200fps\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_nonzero_pixels_status=pass\\ngui_showcase_4k_200fps_checksum=not-a-number\\ngui_showcase_4k_200fps_checksum_status=pass\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=testrev123\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-checksum-contract/4k/native.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-checksum-contract/4k/showcase.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-checksum-contract/4k/build.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-checksum-contract/4k/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-checksum-contract/4k/time.log\\n' > build/test-gui-showcase-perf-checksum-contract/4k/status.env && " +
    "printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_resolution=8k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_nonzero_pixels_status=pass\\ngui_showcase_8k_perf_checksum=also-bad\\ngui_showcase_8k_perf_checksum_status=pass\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=testrev123\\ngui_showcase_8k_perf_source_revision_kind=content-sha256\\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-showcase-perf-checksum-contract/8k/native.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-showcase-perf-checksum-contract/8k/showcase.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-showcase-perf-checksum-contract/8k/build.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-showcase-perf-checksum-contract/8k/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-showcase-perf-checksum-contract/8k/time.log\\n' > build/test-gui-showcase-perf-checksum-contract/8k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-checksum-contract/4k/status.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-showcase-perf-checksum-contract/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-checksum-contract/out REPORT_PATH=build/test-gui-showcase-perf-checksum-contract/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert malformed checksum text overrides status-only pass claims")
val evidence = file_read("build/test-gui-showcase-perf-checksum-contract/out/evidence.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_checksum=not-a-number")
expect(evidence).to_contain("gui_showcase_4k_200fps_checksum_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-readback-checksum:fail;checksum=not-a-number")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_checksum=also-bad")
expect(evidence).to_contain("gui_showcase_8k_perf_checksum_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=invalid-8k-readback-checksum:fail;checksum=also-bad")
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
