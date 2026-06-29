# GUI retained performance source freshness

> Validates the aggregate RenderDoc/GUI audit contract for retained 4K and 8K performance evidence source revisions. Release-grade evidence can opt into strict freshness so stale 4K/8K rows remain diagnostics instead of completion proof.

<!-- sdn-diagram:id=gui_retained_perf_source_freshness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_retained_perf_source_freshness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_retained_perf_source_freshness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_retained_perf_source_freshness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI retained performance source freshness

Validates the aggregate RenderDoc/GUI audit contract for retained 4K and 8K performance evidence source revisions. Release-grade evidence can opt into strict freshness so stale 4K/8K rows remain diagnostics instead of completion proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md |
| Source | `test/03_system/check/gui_retained_perf_source_freshness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the aggregate RenderDoc/GUI audit contract for retained 4K and 8K
performance evidence source revisions. Release-grade evidence can opt into
strict freshness so stale 4K/8K rows remain diagnostics instead of completion
proof.

**Plan:** doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Operator Flow

1. Produce retained 4K and 8K showcase evidence with
   `scripts/check/check-widget-showcase-4k-200fps.shs`.
2. Pass the produced env files into
   `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` through
   `GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`.
3. For release or goal-completion evidence, set
   `GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1` so stale measurements fail
   instead of being accepted as current proof. The default freshness revision is
   a content hash of the retained perf wrapper, measured showcase source, and
   Simple Web renderer implementation, not a docs-only commit hash.
4. Read the aggregate `evidence.env` rows before claiming a 4K or 8K pass:
   source revision status, current source revision, source revision files,
   binary path, native build mode, fallback state, FPS, checksum, frame timing,
   and RSS status must all be compatible with the claim.

## Evidence Contract

The aggregate must emit these source freshness rows for retained 4K evidence:

- `gui_showcase_4k_200fps_current_source_revision`
- `gui_showcase_4k_200fps_source_revision_kind`
- `gui_showcase_4k_200fps_source_revision_files`
- `gui_showcase_4k_200fps_source_revision_status`
- `gui_showcase_4k_200fps_require_current_source_revision`
- `gui_showcase_4k_200fps_simple_bin_source`
- `gui_showcase_4k_200fps_simple_bin_status`
- `gui_showcase_4k_200fps_alias_src_file_status`
- `gui_showcase_4k_200fps_alias_raw_rt_count`
- `gui_showcase_4k_200fps_native_bin_file_status`
- `gui_showcase_4k_200fps_native_bin_executable_status`
- `gui_showcase_4k_200fps_native_bin_format`
- `gui_showcase_4k_200fps_native_bin_format_status`
- `gui_showcase_4k_200fps_native_build_log_file_status`

The aggregate must emit the matching 8K rows:

- `gui_showcase_8k_perf_current_source_revision`
- `gui_showcase_8k_perf_source_revision_kind`
- `gui_showcase_8k_perf_source_revision_files`
- `gui_showcase_8k_perf_source_revision_status`
- `gui_showcase_8k_perf_require_current_source_revision`
- `gui_showcase_8k_perf_simple_bin_source`
- `gui_showcase_8k_perf_simple_bin_status`
- `gui_showcase_8k_perf_alias_src_file_status`
- `gui_showcase_8k_perf_alias_raw_rt_count`
- `gui_showcase_8k_perf_native_bin_file_status`
- `gui_showcase_8k_perf_native_bin_executable_status`
- `gui_showcase_8k_perf_native_bin_format`
- `gui_showcase_8k_perf_native_bin_format_status`
- `gui_showcase_8k_perf_native_build_log_file_status`

With strict freshness enabled, a retained row whose `source_revision` does not
match the current checkout must fail with
`stale-4k-source-revision:mismatch` or `stale-8k-source-revision:mismatch`.
The report summary must also expose `source_status`, `current_source`, and
`alias_raw_rt_count` so a human reviewer can identify stale performance rows
and raw runtime alias shortcuts without opening the raw env file.

The default source file list must include the Simple Web renderer, the retained
8K showcase entrypoint, and the shared scroll/dirty-region render cores so
renderer or retained 8K hardening changes invalidate stale retained 4K/8K perf
evidence.

Explicit producer artifact statuses are claims, not authority. When a retained
row says `*_native_bin_file_status=pass`,
`*_native_bin_executable_status=pass`, or `*_native_bin_format_status=pass`,
the aggregate must still inspect the referenced file and fail completion if the
actual bytes are not a recognized native binary.

Retained frame timing and checksum rows are claims too. A passing row must carry
positive numeric `frame_avg_ns`, `frame_p50_ns`, `frame_p95_ns`, and checksum
values; zero timing or nonnumeric checksum values are diagnostics, not 4K/8K
completion evidence.

Retained performance rows must come from the self-hosted release Simple binary,
not the Rust seed bootstrap binary. Rows that point at `src/compiler_rust/` or
omit `*_simple_bin_source` / `*_simple_bin_status` are diagnostics, not
completion evidence.

Retained native alias rows must be generated from pure Simple alias source that
does not contain raw `rt_*` calls. Nonzero or missing
`*_alias_raw_rt_count` rows invalidate otherwise passing retained 4K/8K
completion claims.

Retained perf reports that include an aggregate rerun command must pass both
produced env files into `check-gui-renderdoc-feature-coverage-status.shs`;
otherwise the aggregate reports missing 4K/8K evidence even after the producer
commands pass.

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_retained_perf_source_freshness_spec.spl --native
```

## Scenarios

### GUI retained performance source freshness

#### documents aggregate consumption of produced retained perf env files

- Read the retained performance evidence report
- Assert the aggregate command consumes the produced 4K and 8K env rows
- Assert the report records retained 4K and 8K aggregate pass evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the retained performance evidence report")
val report = file_read("doc/09_report/perf/gui_showcase_retained_perf_2026-06-26.md")

step("Assert the aggregate command consumes the produced 4K and 8K env rows")
expect(report).to_contain("GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1")
expect(report).to_contain("GUI_SHOWCASE_4K_PERF_ENV=build/widget-showcase-4k-200fps/status.env")
expect(report).to_contain("GUI_SHOWCASE_8K_PERF_ENV=build/widget-showcase-8k-perf/status.env")
expect(report).to_contain("sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Assert the report records retained 4K and 8K aggregate pass evidence")
expect(report).to_contain("`gui_showcase_4k_200fps_status=pass`")
expect(report).to_contain("`gui_showcase_8k_perf_status=pass`")
expect(report).to_contain("`blocked_completion_gate_count=")
```

</details>

#### includes Simple Web and retained 8K render sources in perf freshness fingerprints

- Read the producer and aggregate scripts
- Assert both defaults include the renderer and retained 8K sources
- Run the producer in plan-only mode to inspect emitted provenance
   - Expected: code equals `0`
- Assert the emitted source revision file list includes all retained render sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the producer and aggregate scripts")
val producer = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")
val renderer_path = "src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl"
val scroll_showcase_path = "examples/06_io/ui/showcase_8k_scroll_gui.spl"
val scroll_surface_path = "src/lib/common/ui/scroll_surface.spl"
val dirty_region_path = "src/lib/common/ui/dirty_region.spl"

step("Assert both defaults include the renderer and retained 8K sources")
expect(producer).to_contain(renderer_path)
expect(aggregate).to_contain(renderer_path)
expect(producer).to_contain(scroll_showcase_path)
expect(aggregate).to_contain(scroll_showcase_path)
expect(producer).to_contain(scroll_surface_path)
expect(aggregate).to_contain(scroll_surface_path)
expect(producer).to_contain(dirty_region_path)
expect(aggregate).to_contain(dirty_region_path)

step("Run the producer in plan-only mode to inspect emitted provenance")
val command = "rm -rf build/test-gui-retained-perf-source-files && PLAN_ONLY=1 BUILD_DIR=build/test-gui-retained-perf-source-files sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the emitted source revision file list includes all retained render sources")
val evidence = file_read("build/test-gui-retained-perf-source-files/status.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision_files=")
expect(evidence).to_contain(renderer_path)
expect(evidence).to_contain(scroll_showcase_path)
expect(evidence).to_contain(scroll_surface_path)
expect(evidence).to_contain(dirty_region_path)
```

</details>

#### rejects retained perf rows that point at missing native artifacts

- Create a retained 4K performance row with missing native artifacts
   - Expected: code equals `0`
- Assert missing native artifacts fail the retained 4K row


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K performance row with missing native artifacts")
val command = "rm -rf build/test-gui-retained-perf-missing-native-artifacts && mkdir -p build/test-gui-retained-perf-missing-native-artifacts/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-missing-native-artifacts/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-missing-native-artifacts/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=argb-checksum\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=0\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-missing-native-artifacts/source/missing-native.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-missing-native-artifacts/source/missing-alias.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-missing-native-artifacts/source/missing-build.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-missing-native-artifacts/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-missing-native-artifacts/source/time.log\\n' > build/test-gui-retained-perf-missing-native-artifacts/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-missing-native-artifacts/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-missing-native-artifacts/out REPORT_PATH=build/test-gui-retained-perf-missing-native-artifacts/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert missing native artifacts fail the retained 4K row")
val evidence = file_read("build/test-gui-retained-perf-missing-native-artifacts/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-missing-native-artifacts/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_alias_src_file_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=unknown")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_log_file_status=missing")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=missing-4k-native-artifacts:alias_src=missing;native_bin=missing;native_bin_executable=missing;native_bin_format=fail;native_build_log=missing")
expect(report).to_contain("4K retained perf native artifacts: alias_src missing; native_bin missing; native_bin_executable missing; native_bin_format fail (unknown); native_build_log missing")
```

</details>

#### rejects retained perf rows whose explicit native artifact pass claims contradict the file bytes

- Create a retained 4K performance row with a chmodded text file pretending to be native
   - Expected: code equals `0`
- Assert the aggregate uses actual native binary magic over explicit pass claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K performance row with a chmodded text file pretending to be native")
val command = "rm -rf build/test-gui-retained-perf-spoofed-native-artifact && mkdir -p build/test-gui-retained-perf-spoofed-native-artifact/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/alias4k.spl && printf 'not-native\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/native4k.bin && chmod +x build/test-gui-retained-perf-spoofed-native-artifact/source/native4k.bin && printf 'native build log\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/build4k.log && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=argb-checksum\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=0\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-spoofed-native-artifact/source/native4k.bin\\ngui_showcase_4k_200fps_native_bin_file_status=pass\\ngui_showcase_4k_200fps_native_bin_executable_status=pass\\ngui_showcase_4k_200fps_native_bin_magic=7f454c46\\ngui_showcase_4k_200fps_native_bin_format=elf\\ngui_showcase_4k_200fps_native_bin_format_status=pass\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-spoofed-native-artifact/source/alias4k.spl\\ngui_showcase_4k_200fps_alias_src_file_status=pass\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-spoofed-native-artifact/source/build4k.log\\ngui_showcase_4k_200fps_native_build_log_file_status=pass\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-spoofed-native-artifact/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-spoofed-native-artifact/source/time.log\\n' > build/test-gui-retained-perf-spoofed-native-artifact/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-spoofed-native-artifact/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-spoofed-native-artifact/out REPORT_PATH=build/test-gui-retained-perf-spoofed-native-artifact/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate uses actual native binary magic over explicit pass claims")
val evidence = file_read("build/test-gui-retained-perf-spoofed-native-artifact/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-spoofed-native-artifact/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=unknown")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=missing-4k-native-artifacts:alias_src=pass;native_bin=pass;native_bin_executable=pass;native_bin_format=fail;native_build_log=pass")
expect(report).to_contain("4K retained perf native artifacts: alias_src pass; native_bin pass; native_bin_executable pass; native_bin_format fail (unknown); native_build_log pass")
```

</details>

#### rejects stale 4K and 8K retained perf rows when strict source freshness is required

- Create stale retained 4K and 8K performance evidence
   - Expected: code equals `0`
- Assert stale rows fail and expose source freshness provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create stale retained 4K and 8K performance evidence")
val command = "rm -rf build/test-gui-retained-perf-source-freshness && mkdir -p build/test-gui-retained-perf-source-freshness/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-source-freshness/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-source-freshness/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-source-freshness/source/alias4k.spl && printf '\\177ELFbin4k\\n' > build/test-gui-retained-perf-source-freshness/source/native4k.bin && printf 'build4k\\n' > build/test-gui-retained-perf-source-freshness/source/build4k.log && printf 'alias8k\\n' > build/test-gui-retained-perf-source-freshness/source/alias8k.spl && printf '\\177ELFbin8k\\n' > build/test-gui-retained-perf-source-freshness/source/native8k.bin && printf 'build8k\\n' > build/test-gui-retained-perf-source-freshness/source/build8k.log && chmod +x build/test-gui-retained-perf-source-freshness/source/native4k.bin build/test-gui-retained-perf-source-freshness/source/native8k.bin && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=argb-checksum\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=stale-source\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=0\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-source-freshness/source/native4k.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-source-freshness/source/alias4k.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-source-freshness/source/build4k.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-source-freshness/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-source-freshness/source/time.log\\n' > build/test-gui-retained-perf-source-freshness/source/status4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\\ngui_showcase_8k_perf_resolution=8k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_checksum=123456\\ngui_showcase_8k_perf_readback_mode=argb-checksum\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=stale-source\\ngui_showcase_8k_perf_source_revision_kind=content-sha256\\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_8k_perf_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_8k_perf_simple_bin_source=self-hosted-release\\ngui_showcase_8k_perf_simple_bin_status=pass\\ngui_showcase_8k_perf_alias_raw_rt_count=0\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-retained-perf-source-freshness/source/native8k.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-retained-perf-source-freshness/source/alias8k.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-retained-perf-source-freshness/source/build8k.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-retained-perf-source-freshness/source/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-retained-perf-source-freshness/source/time.log\\n' > build/test-gui-retained-perf-source-freshness/source/status8k.env && GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-source-freshness/source/status4k.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-retained-perf-source-freshness/source/status8k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-source-freshness/out REPORT_PATH=build/test-gui-retained-perf-source-freshness/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert stale rows fail and expose source freshness provenance")
val evidence = file_read("build/test-gui-retained-perf-source-freshness/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-source-freshness/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_current_source_revision=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision_kind=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision_files=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision_status=mismatch")
expect(evidence).to_contain("gui_showcase_4k_200fps_require_current_source_revision=1")
expect(evidence).to_contain("gui_showcase_4k_200fps_alias_src_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_executable_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format=elf")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_bin_format_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_log_file_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=stale-4k-source-revision:mismatch")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_current_source_revision=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision_kind=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision_files=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision_status=mismatch")
expect(evidence).to_contain("gui_showcase_8k_perf_require_current_source_revision=1")
expect(evidence).to_contain("gui_showcase_8k_perf_alias_src_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_executable_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_format=elf")
expect(evidence).to_contain("gui_showcase_8k_perf_native_bin_format_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_native_build_log_file_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=stale-8k-source-revision:mismatch")
expect(report).to_contain("source_status mismatch")
expect(report).to_contain("current_source")
expect(report).to_contain("4K retained perf native artifacts: alias_src pass; native_bin pass; native_bin_executable pass; native_bin_format pass (elf); native_build_log pass")
expect(report).to_contain("8K retained perf native artifacts: alias_src pass; native_bin pass; native_bin_executable pass; native_bin_format pass (elf); native_build_log pass")
```

</details>

#### rejects retained 4K perf rows with zero frame timing

- Create a retained 4K performance row with zero timing values
   - Expected: code equals `0`
- Assert zero timing invalidates the retained 4K completion row


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K performance row with zero timing values")
val command = "rm -rf build/test-gui-retained-perf-zero-frame-timing && mkdir -p build/test-gui-retained-perf-zero-frame-timing/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-zero-frame-timing/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-zero-frame-timing/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-zero-frame-timing/source/alias4k.spl && printf '\\177ELFbin4k\\n' > build/test-gui-retained-perf-zero-frame-timing/source/native4k.bin && chmod +x build/test-gui-retained-perf-zero-frame-timing/source/native4k.bin && printf 'build4k\\n' > build/test-gui-retained-perf-zero-frame-timing/source/build4k.log && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=0\\ngui_showcase_4k_200fps_frame_p50_ns=0\\ngui_showcase_4k_200fps_frame_p95_ns=0\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=argb-checksum\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=0\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-zero-frame-timing/source/native4k.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-zero-frame-timing/source/alias4k.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-zero-frame-timing/source/build4k.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-zero-frame-timing/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-zero-frame-timing/source/time.log\\n' > build/test-gui-retained-perf-zero-frame-timing/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-zero-frame-timing/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-zero-frame-timing/out REPORT_PATH=build/test-gui-retained-perf-zero-frame-timing/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert zero timing invalidates the retained 4K completion row")
val evidence = file_read("build/test-gui-retained-perf-zero-frame-timing/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-zero-frame-timing/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_avg_ns=0")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_p50_ns=0")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_p95_ns=0")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-frame-timing:avg=0;p50=0;p95=0")
expect(report).to_contain("GUI/web/2D 4K retained perf: fail (invalid-4k-frame-timing:avg=0;p50=0;p95=0")
```

</details>

#### rejects retained 8K perf rows with nonnumeric readback checksum

- Create a retained 8K performance row with nonnumeric checksum evidence
   - Expected: code equals `0`
- Assert nonnumeric checksum invalidates the retained 8K completion row


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 8K performance row with nonnumeric checksum evidence")
val command = "rm -rf build/test-gui-retained-perf-nonnumeric-checksum && mkdir -p build/test-gui-retained-perf-nonnumeric-checksum/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-nonnumeric-checksum/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-nonnumeric-checksum/source/time.log && printf 'alias8k\\n' > build/test-gui-retained-perf-nonnumeric-checksum/source/alias8k.spl && printf '\\177ELFbin8k\\n' > build/test-gui-retained-perf-nonnumeric-checksum/source/native8k.bin && chmod +x build/test-gui-retained-perf-nonnumeric-checksum/source/native8k.bin && printf 'build8k\\n' > build/test-gui-retained-perf-nonnumeric-checksum/source/build8k.log && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\\ngui_showcase_8k_perf_resolution=8k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_checksum=not-a-number\\ngui_showcase_8k_perf_readback_mode=argb-checksum\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=artifact-test\\ngui_showcase_8k_perf_source_revision_kind=content-sha256\\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_8k_perf_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_8k_perf_simple_bin_source=self-hosted-release\\ngui_showcase_8k_perf_simple_bin_status=pass\\ngui_showcase_8k_perf_alias_raw_rt_count=0\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-retained-perf-nonnumeric-checksum/source/native8k.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-retained-perf-nonnumeric-checksum/source/alias8k.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-retained-perf-nonnumeric-checksum/source/build8k.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-retained-perf-nonnumeric-checksum/source/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-retained-perf-nonnumeric-checksum/source/time.log\\n' > build/test-gui-retained-perf-nonnumeric-checksum/source/status8k.env && GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-retained-perf-nonnumeric-checksum/source/status8k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-nonnumeric-checksum/out REPORT_PATH=build/test-gui-retained-perf-nonnumeric-checksum/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert nonnumeric checksum invalidates the retained 8K completion row")
val evidence = file_read("build/test-gui-retained-perf-nonnumeric-checksum/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-nonnumeric-checksum/report.md")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_checksum=not-a-number")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=invalid-8k-readback-checksum:fail;checksum=not-a-number")
expect(report).to_contain("GUI/web/2D 8K retained perf: fail (invalid-8k-readback-checksum:fail;checksum=not-a-number")
```

</details>

#### rejects retained perf rows whose explicit readback mode is not ARGB checksum

- Create a retained 4K performance row with a bad explicit readback mode
   - Expected: code equals `0`
- Assert the aggregate does not mask a bad producer readback mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K performance row with a bad explicit readback mode")
val command = "rm -rf build/test-gui-retained-perf-readback-mode && mkdir -p build/test-gui-retained-perf-readback-mode/source && printf 'showcase retained log\\ngui_showcase_8k_perf_readback_mode=argb-checksum\\n' > build/test-gui-retained-perf-readback-mode/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-readback-mode/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-readback-mode/source/alias4k.spl && printf '\\177ELFbin4k\\n' > build/test-gui-retained-perf-readback-mode/source/native4k.bin && chmod +x build/test-gui-retained-perf-readback-mode/source/native4k.bin && printf 'build4k\\n' > build/test-gui-retained-perf-readback-mode/source/build4k.log && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=cpu-mirror\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=0\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-readback-mode/source/native4k.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-readback-mode/source/alias4k.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-readback-mode/source/build4k.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-readback-mode/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-readback-mode/source/time.log\\n' > build/test-gui-retained-perf-readback-mode/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-readback-mode/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-readback-mode/out REPORT_PATH=build/test-gui-retained-perf-readback-mode/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate does not mask a bad producer readback mode")
val evidence = file_read("build/test-gui-retained-perf-readback-mode/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-readback-mode/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_readback_mode=cpu-mirror")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-readback-mode:cpu-mirror")
expect(report).to_contain("GUI/web/2D 4K retained perf: fail (invalid-4k-readback-mode:cpu-mirror")
```

</details>

#### rejects retained perf rows with missing producer readback mode

- Create an otherwise valid retained 4K performance row without readback mode
   - Expected: code equals `0`
- Assert the aggregate does not infer readback mode from checksum fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an otherwise valid retained 4K performance row without readback mode")
val command = "rm -rf build/test-gui-retained-perf-missing-readback-mode && mkdir -p build/test-gui-retained-perf-missing-readback-mode/source && printf 'gui_showcase_4k_200fps_status=pass\ngui_showcase_4k_200fps_reason=met-target-fps\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\ngui_showcase_4k_200fps_width=3840\ngui_showcase_4k_200fps_height=2160\ngui_showcase_4k_200fps_pixels=8294400\ngui_showcase_4k_200fps_frames=200\ngui_showcase_4k_200fps_fps_x1000=201000\ngui_showcase_4k_200fps_frame_avg_ns=4975124\ngui_showcase_4k_200fps_frame_p50_ns=4975124\ngui_showcase_4k_200fps_frame_p95_ns=4975124\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\ngui_showcase_4k_200fps_target_fps=200\ngui_showcase_4k_200fps_max_rss_kb=131072\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\ngui_showcase_4k_200fps_rss_status=pass\ngui_showcase_4k_200fps_nonzero_pixels=1000\ngui_showcase_4k_200fps_checksum=123456\ngui_showcase_4k_200fps_render_mode=retained-static-frame\ngui_showcase_4k_200fps_redraw_frames=1\n' > build/test-gui-retained-perf-missing-readback-mode/source/status4k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-missing-readback-mode/source/status4k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-missing-readback-mode/out REPORT_PATH=build/test-gui-retained-perf-missing-readback-mode/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert the aggregate does not infer readback mode from checksum fields")
val evidence = file_read("build/test-gui-retained-perf-missing-readback-mode/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-missing-readback-mode/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_readback_mode=")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=missing-required-4k-200fps-evidence:readback_mode")
expect(report).to_contain("GUI/web/2D 4K retained perf: fail (missing-required-4k-200fps-evidence:readback_mode")
```

</details>

#### rejects retained 4K and 8K perf rows whose native alias sources still use raw rt calls

- Create otherwise valid retained 4K and 8K rows with raw rt alias counts
   - Expected: code equals `0`
- Assert raw rt aliases invalidate retained performance completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create otherwise valid retained 4K and 8K rows with raw rt alias counts")
val command = "rm -rf build/test-gui-retained-perf-raw-rt-alias && mkdir -p build/test-gui-retained-perf-raw-rt-alias/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-raw-rt-alias/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-raw-rt-alias/source/time.log && printf 'rt_raw_call4k\\n' > build/test-gui-retained-perf-raw-rt-alias/source/alias4k.spl && printf '\\177ELFbin4k\\n' > build/test-gui-retained-perf-raw-rt-alias/source/native4k.bin && printf 'build4k\\n' > build/test-gui-retained-perf-raw-rt-alias/source/build4k.log && printf 'rt_raw_call8k\\n' > build/test-gui-retained-perf-raw-rt-alias/source/alias8k.spl && printf '\\177ELFbin8k\\n' > build/test-gui-retained-perf-raw-rt-alias/source/native8k.bin && printf 'build8k\\n' > build/test-gui-retained-perf-raw-rt-alias/source/build8k.log && chmod +x build/test-gui-retained-perf-raw-rt-alias/source/native4k.bin build/test-gui-retained-perf-raw-rt-alias/source/native8k.bin && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=argb-checksum\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=3\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-raw-rt-alias/source/native4k.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-raw-rt-alias/source/alias4k.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-raw-rt-alias/source/build4k.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-raw-rt-alias/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-raw-rt-alias/source/time.log\\n' > build/test-gui-retained-perf-raw-rt-alias/source/status4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\\ngui_showcase_8k_perf_resolution=8k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_checksum=123456\\ngui_showcase_8k_perf_readback_mode=argb-checksum\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=artifact-test\\ngui_showcase_8k_perf_source_revision_kind=content-sha256\\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_8k_perf_simple_bin=release/x86_64-unknown-linux-gnu/simple\\ngui_showcase_8k_perf_simple_bin_source=self-hosted-release\\ngui_showcase_8k_perf_simple_bin_status=pass\\ngui_showcase_8k_perf_alias_raw_rt_count=2\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-retained-perf-raw-rt-alias/source/native8k.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-retained-perf-raw-rt-alias/source/alias8k.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-retained-perf-raw-rt-alias/source/build8k.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-retained-perf-raw-rt-alias/source/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-retained-perf-raw-rt-alias/source/time.log\\n' > build/test-gui-retained-perf-raw-rt-alias/source/status8k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-raw-rt-alias/source/status4k.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-retained-perf-raw-rt-alias/source/status8k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-raw-rt-alias/out REPORT_PATH=build/test-gui-retained-perf-raw-rt-alias/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert raw rt aliases invalidate retained performance completion")
val evidence = file_read("build/test-gui-retained-perf-raw-rt-alias/out/evidence.env")
val report = file_read("build/test-gui-retained-perf-raw-rt-alias/report.md")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_alias_raw_rt_count=3")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=raw-rt-in-4k-alias:3")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_alias_raw_rt_count=2")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=raw-rt-in-8k-alias:2")
expect(report).to_contain("GUI/web/2D 4K retained perf: fail (raw-rt-in-4k-alias:3")
expect(report).to_contain("GUI/web/2D 8K retained perf: fail (raw-rt-in-8k-alias:2")
expect(report).to_contain("alias_raw_rt_count 3")
expect(report).to_contain("alias_raw_rt_count 2")
```

</details>

#### rejects retained 4K and 8K perf rows produced by the Rust seed binary

- Create otherwise valid retained 4K and 8K performance rows with seed binary provenance
   - Expected: code equals `0`
- Assert seed provenance fails both retained performance rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create otherwise valid retained 4K and 8K performance rows with seed binary provenance")
val command = "rm -rf build/test-gui-retained-perf-seed-provenance && mkdir -p build/test-gui-retained-perf-seed-provenance/source && printf 'showcase retained log\\n' > build/test-gui-retained-perf-seed-provenance/source/showcase.log && printf 'elapsed_ms=597\\n' > build/test-gui-retained-perf-seed-provenance/source/time.log && printf 'alias4k\\n' > build/test-gui-retained-perf-seed-provenance/source/alias4k.spl && printf '\\177ELFbin4k\\n' > build/test-gui-retained-perf-seed-provenance/source/native4k.bin && printf 'build4k\\n' > build/test-gui-retained-perf-seed-provenance/source/build4k.log && printf 'alias8k\\n' > build/test-gui-retained-perf-seed-provenance/source/alias8k.spl && printf '\\177ELFbin8k\\n' > build/test-gui-retained-perf-seed-provenance/source/native8k.bin && printf 'build8k\\n' > build/test-gui-retained-perf-seed-provenance/source/build8k.log && chmod +x build/test-gui-retained-perf-seed-provenance/source/native4k.bin build/test-gui-retained-perf-seed-provenance/source/native8k.bin && printf 'gui_showcase_4k_200fps_status=pass\\ngui_showcase_4k_200fps_reason=met-target-fps\\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\\ngui_showcase_4k_200fps_resolution=4k\\ngui_showcase_4k_200fps_width=3840\\ngui_showcase_4k_200fps_height=2160\\ngui_showcase_4k_200fps_frames=200\\ngui_showcase_4k_200fps_fps_x1000=201000\\ngui_showcase_4k_200fps_frame_avg_ns=4975124\\ngui_showcase_4k_200fps_frame_p50_ns=4975124\\ngui_showcase_4k_200fps_frame_p95_ns=4975124\\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\\ngui_showcase_4k_200fps_target_fps=200\\ngui_showcase_4k_200fps_max_rss_kb=131072\\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\\ngui_showcase_4k_200fps_rss_status=pass\\ngui_showcase_4k_200fps_pixels=8294400\\ngui_showcase_4k_200fps_nonzero_pixels=1000\\ngui_showcase_4k_200fps_checksum=123456\\ngui_showcase_4k_200fps_readback_mode=argb-checksum\\ngui_showcase_4k_200fps_render_mode=retained-static-frame\\ngui_showcase_4k_200fps_redraw_frames=1\\ngui_showcase_4k_200fps_source_revision=artifact-test\\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\\ngui_showcase_4k_200fps_simple_bin_status=pass\\ngui_showcase_4k_200fps_alias_raw_rt_count=0\\ngui_showcase_4k_200fps_use_native=1\\ngui_showcase_4k_200fps_native_bin=build/test-gui-retained-perf-seed-provenance/source/native4k.bin\\ngui_showcase_4k_200fps_alias_src=build/test-gui-retained-perf-seed-provenance/source/alias4k.spl\\ngui_showcase_4k_200fps_native_build_log=build/test-gui-retained-perf-seed-provenance/source/build4k.log\\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\\ngui_showcase_4k_200fps_fallback_state=none\\ngui_showcase_4k_200fps_log=build/test-gui-retained-perf-seed-provenance/source/showcase.log\\ngui_showcase_4k_200fps_time_log=build/test-gui-retained-perf-seed-provenance/source/time.log\\n' > build/test-gui-retained-perf-seed-provenance/source/status4k.env && printf 'gui_showcase_8k_perf_status=pass\\ngui_showcase_8k_perf_reason=met-target-fps\\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\\ngui_showcase_8k_perf_resolution=8k\\ngui_showcase_8k_perf_width=7680\\ngui_showcase_8k_perf_height=4320\\ngui_showcase_8k_perf_frames=200\\ngui_showcase_8k_perf_fps_x1000=201000\\ngui_showcase_8k_perf_frame_avg_ns=4975124\\ngui_showcase_8k_perf_frame_p50_ns=4975124\\ngui_showcase_8k_perf_frame_p95_ns=4975124\\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\\ngui_showcase_8k_perf_target_fps=200\\ngui_showcase_8k_perf_max_rss_kb=524288\\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\\ngui_showcase_8k_perf_rss_status=pass\\ngui_showcase_8k_perf_pixels=33177600\\ngui_showcase_8k_perf_nonzero_pixels=1000\\ngui_showcase_8k_perf_checksum=123456\\ngui_showcase_8k_perf_readback_mode=argb-checksum\\ngui_showcase_8k_perf_render_mode=retained-static-frame\\ngui_showcase_8k_perf_redraw_frames=1\\ngui_showcase_8k_perf_source_revision=artifact-test\\ngui_showcase_8k_perf_source_revision_kind=content-sha256\\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\\ngui_showcase_8k_perf_simple_bin_source=self-hosted-release\\ngui_showcase_8k_perf_simple_bin_status=pass\\ngui_showcase_8k_perf_alias_raw_rt_count=0\\ngui_showcase_8k_perf_use_native=1\\ngui_showcase_8k_perf_native_bin=build/test-gui-retained-perf-seed-provenance/source/native8k.bin\\ngui_showcase_8k_perf_alias_src=build/test-gui-retained-perf-seed-provenance/source/alias8k.spl\\ngui_showcase_8k_perf_native_build_log=build/test-gui-retained-perf-seed-provenance/source/build8k.log\\ngui_showcase_8k_perf_native_build_mode=aggressive-native\\ngui_showcase_8k_perf_fallback_state=none\\ngui_showcase_8k_perf_log=build/test-gui-retained-perf-seed-provenance/source/showcase.log\\ngui_showcase_8k_perf_time_log=build/test-gui-retained-perf-seed-provenance/source/time.log\\n' > build/test-gui-retained-perf-seed-provenance/source/status8k.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-retained-perf-seed-provenance/source/status4k.env GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-retained-perf-seed-provenance/source/status8k.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-retained-perf-seed-provenance/out REPORT_PATH=build/test-gui-retained-perf-seed-provenance/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert seed provenance fails both retained performance rows")
val evidence = file_read("build/test-gui-retained-perf-seed-provenance/out/evidence.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-simple-bin-provenance:simple_bin=rust-seed-forbidden")
expect(evidence).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=invalid-8k-simple-bin-provenance:simple_bin=rust-seed-forbidden")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md](doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md)


</details>
