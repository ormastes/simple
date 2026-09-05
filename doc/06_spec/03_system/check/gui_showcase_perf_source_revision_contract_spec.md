# GUI Showcase Perf Source Revision Contract

> Validates that strict GUI showcase completion mode rejects retained 4K/8K performance evidence produced from stale source revisions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Source Revision Contract

Validates that strict GUI showcase completion mode rejects retained 4K/8K performance evidence produced from stale source revisions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that strict GUI showcase completion mode rejects retained 4K/8K
performance evidence produced from stale source revisions.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl --mode=interpreter
```

## Operator Flow

1. Run this spec after changing source-revision handling in
   `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` or the 4K/8K
   showcase wrappers.
2. Inspect `build/test-gui-showcase-perf-source-revision-4k/out/evidence.env`
   for the strict 4K source freshness result.
3. Inspect `build/test-gui-showcase-perf-source-revision-8k/out/evidence.env`
   for the strict 8K source freshness result.
4. Treat a stale row passing under `GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1`
   as a completion-gate regression.

## Acceptance

- A complete 4K performance row with stale `source_revision` fails when strict
  freshness is required.
- A complete 8K performance row with stale `source_revision` fails when strict
  freshness is required.
- The aggregate emits `*_source_revision_status=mismatch`.
- The failure reason names the stale source revision and expected current
  revision.

## Test Matrix

Each test uses `GUI_SHOWCASE_CURRENT_SOURCE_REVISION=current123` and a synthetic
evidence row with `source_revision=stale123`. All other timing, geometry,
readback, RSS, retained-mode, native binary, alias source, build log, showcase
log, and time-log evidence is valid. The only invalid completion field is the
source revision freshness.

The 4K case must emit:

- `gui_showcase_4k_200fps_status=fail`
- `gui_showcase_4k_200fps_source_revision_status=mismatch`
- `gui_showcase_4k_200fps_reason=stale-4k-source-revision:mismatch;source=stale123;current=current123`

The 8K case must emit:

- `gui_showcase_8k_perf_status=fail`
- `gui_showcase_8k_perf_source_revision_status=mismatch`
- `gui_showcase_8k_perf_reason=stale-8k-source-revision:mismatch;source=stale123;current=current123`

## Evidence Keys

The spec validates these 4K aggregate keys:

- `gui_showcase_4k_200fps_status`
- `gui_showcase_4k_200fps_reason`
- `gui_showcase_4k_200fps_source_revision`
- `gui_showcase_4k_200fps_current_source_revision`
- `gui_showcase_4k_200fps_source_revision_status`

The spec validates these 8K aggregate keys:

- `gui_showcase_8k_perf_status`
- `gui_showcase_8k_perf_reason`
- `gui_showcase_8k_perf_source_revision`
- `gui_showcase_8k_perf_current_source_revision`
- `gui_showcase_8k_perf_source_revision_status`

## Failure Semantics

Strict source freshness is opt-in because many diagnostic aggregate runs use
historic fixture rows. Completion claims for current 4K/8K GUI showcase
performance should set `GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1` so a
stale retained benchmark row cannot be reused after the wrapper or showcase
source changes.

## Troubleshooting

If this spec fails with missing native artifacts, inspect the synthetic binary,
alias source, and build log paths in the generated `status.env`. If it fails by
returning `pass`, the strict source freshness gate is not enforcing mismatched
source revisions. If it fails with `unchecked`, the current-source revision was
not available and the strict completion environment needs to provide or derive
one.

## Completion Boundary

This spec proves strict aggregate source freshness handling only. It does not
prove real 4K/8K throughput, live GPU backend selection, platform render-log
capture, or actual RenderDoc artifact validity.

## Scenarios

### GUI showcase perf source revision contract

#### rejects stale retained 4K rows when current source revision is required

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects stale retained 4K rows when current source revision is required
- Create a complete 4K row with stale source revision
- Assert strict source freshness rejects the stale 4K row
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_source_revision_status") equals `mismatch`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `stale-4k-source-revision:mismatch;source=stale123;current=current123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects stale retained 4K rows when current source revision is required")
step("Create a complete 4K row with stale source revision")
val command = "rm -rf build/test-gui-showcase-perf-source-revision-4k && mkdir -p build/test-gui-showcase-perf-source-revision-4k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-source-revision-4k/source/native4k.bin && chmod +x build/test-gui-showcase-perf-source-revision-4k/source/native4k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-source-revision-4k/source/build4k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-source-revision-4k/source/showcase4k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-source-revision-4k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-source-revision-4k/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\ngui_showcase_4k_200fps_reason=met-target-fps\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\ngui_showcase_4k_200fps_resolution=4k\ngui_showcase_4k_200fps_width=3840\ngui_showcase_4k_200fps_height=2160\ngui_showcase_4k_200fps_frames=200\ngui_showcase_4k_200fps_warmup_frames=12\ngui_showcase_4k_200fps_frame_sample_count=200\ngui_showcase_4k_200fps_fps_x1000=201000\ngui_showcase_4k_200fps_frame_avg_ns=4975124\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\ngui_showcase_4k_200fps_frame_p50_ns=4975124\ngui_showcase_4k_200fps_frame_p95_ns=4975124\ngui_showcase_4k_200fps_target_fps=200\ngui_showcase_4k_200fps_max_rss_kb=131072\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\ngui_showcase_4k_200fps_rss_status=pass\ngui_showcase_4k_200fps_pixels=8294400\ngui_showcase_4k_200fps_nonzero_pixels=1000\ngui_showcase_4k_200fps_checksum=123456\ngui_showcase_4k_200fps_readback_mode=argb-checksum\ngui_showcase_4k_200fps_render_mode=retained-static-frame\ngui_showcase_4k_200fps_redraw_frames=1\ngui_showcase_4k_200fps_source_revision=stale123\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl src/lib/gc_async_mut/gpu/engine2d/engine.spl src/lib/gc_async_mut/gpu/engine2d/backend_software.spl\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\ngui_showcase_4k_200fps_simple_bin_status=pass\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-source-revision-4k/source/native4k.bin\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-source-revision-4k/source/showcase4k.spl\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-source-revision-4k/source/build4k.log\ngui_showcase_4k_200fps_use_native=1\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\ngui_showcase_4k_200fps_fallback_state=none\ngui_showcase_4k_200fps_alias_raw_rt_count=0\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-source-revision-4k/source/showcase.log\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-source-revision-4k/source/time.log\n' > build/test-gui-showcase-perf-source-revision-4k/source/status.env && GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 GUI_SHOWCASE_CURRENT_SOURCE_REVISION=current123 GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-source-revision-4k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-source-revision-4k/out REPORT_PATH=build/test-gui-showcase-perf-source-revision-4k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, _code) = process_run("/bin/sh", ["-c", command])
# NOTE (2026-08-07, T9): do NOT assert the wrapper's overall process exit
# code here. `check-gui-renderdoc-feature-coverage-status.shs` is a
# whole-repo aggregate gate that `exit 1`s whenever ANY of its many
# unrelated evidence categories (widget-kind coverage, layout manifest,
# etc.) is incomplete -- which this synthetic fixture (only the 4K row
# populated) always leaves incomplete. That is correct behavior of the
# aggregate gate, not a defect; the 4K-row source-freshness contract
# this spec actually tests is captured entirely in evidence.env below,
# which the wrapper writes before it exits non-zero. See
# doc/08_tracking/bug/gui_showcase_source_revision_spec_asserted_wrong_exit_code_2026-08-07.md.

step("Assert strict source freshness rejects the stale 4K row")
val evidence = file_read("build/test-gui-showcase-perf-source-revision-4k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_source_revision_status")).to_equal("mismatch")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("stale-4k-source-revision:mismatch;source=stale123;current=current123")
```

</details>

#### rejects stale retained 8K rows when current source revision is required

- rejects stale retained 8K rows when current source revision is required
- Create a complete 8K row with stale source revision
- Assert strict source freshness rejects the stale 8K row
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_source_revision_status") equals `mismatch`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_reason") equals `stale-8k-source-revision:mismatch;source=stale123;current=current123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects stale retained 8K rows when current source revision is required")
step("Create a complete 8K row with stale source revision")
val command = "rm -rf build/test-gui-showcase-perf-source-revision-8k && mkdir -p build/test-gui-showcase-perf-source-revision-8k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-source-revision-8k/source/native8k.bin && chmod +x build/test-gui-showcase-perf-source-revision-8k/source/native8k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-source-revision-8k/source/build8k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-source-revision-8k/source/showcase8k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-source-revision-8k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-source-revision-8k/source/time.log && printf 'gui_showcase_8k_perf_status=pass\ngui_showcase_8k_perf_reason=met-target-fps\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\ngui_showcase_8k_perf_resolution=8k\ngui_showcase_8k_perf_width=7680\ngui_showcase_8k_perf_height=4320\ngui_showcase_8k_perf_frames=200\ngui_showcase_8k_perf_warmup_frames=12\ngui_showcase_8k_perf_frame_sample_count=200\ngui_showcase_8k_perf_fps_x1000=201000\ngui_showcase_8k_perf_frame_avg_ns=4975124\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\ngui_showcase_8k_perf_frame_p50_ns=4975124\ngui_showcase_8k_perf_frame_p95_ns=4975124\ngui_showcase_8k_perf_target_fps=200\ngui_showcase_8k_perf_max_rss_kb=524288\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\ngui_showcase_8k_perf_rss_status=pass\ngui_showcase_8k_perf_pixels=33177600\ngui_showcase_8k_perf_nonzero_pixels=1000\ngui_showcase_8k_perf_checksum=123456\ngui_showcase_8k_perf_readback_mode=argb-checksum\ngui_showcase_8k_perf_render_mode=retained-static-frame\ngui_showcase_8k_perf_redraw_frames=1\ngui_showcase_8k_perf_source_revision=stale123\ngui_showcase_8k_perf_source_revision_kind=content-sha256\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl src/lib/gc_async_mut/gpu/engine2d/engine.spl src/lib/gc_async_mut/gpu/engine2d/backend_software.spl\ngui_showcase_8k_perf_simple_bin=release/x86_64-unknown-linux-gnu/simple\ngui_showcase_8k_perf_simple_bin_source=self-hosted-release\ngui_showcase_8k_perf_simple_bin_status=pass\ngui_showcase_8k_perf_native_bin=build/test-gui-showcase-perf-source-revision-8k/source/native8k.bin\ngui_showcase_8k_perf_alias_src=build/test-gui-showcase-perf-source-revision-8k/source/showcase8k.spl\ngui_showcase_8k_perf_native_build_log=build/test-gui-showcase-perf-source-revision-8k/source/build8k.log\ngui_showcase_8k_perf_use_native=1\ngui_showcase_8k_perf_native_build_mode=aggressive-native\ngui_showcase_8k_perf_fallback_state=none\ngui_showcase_8k_perf_alias_raw_rt_count=0\ngui_showcase_8k_perf_log=build/test-gui-showcase-perf-source-revision-8k/source/showcase.log\ngui_showcase_8k_perf_time_log=build/test-gui-showcase-perf-source-revision-8k/source/time.log\n' > build/test-gui-showcase-perf-source-revision-8k/source/status.env && GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 GUI_SHOWCASE_CURRENT_SOURCE_REVISION=current123 GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-showcase-perf-source-revision-8k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-source-revision-8k/out REPORT_PATH=build/test-gui-showcase-perf-source-revision-8k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, _code) = process_run("/bin/sh", ["-c", command])
# See the 4K case above for why the wrapper's overall exit code is not
# asserted here.

step("Assert strict source freshness rejects the stale 8K row")
val evidence = file_read("build/test-gui-showcase-perf-source-revision-8k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_source_revision_status")).to_equal("mismatch")
expect(_value_of(evidence, "gui_showcase_8k_perf_reason")).to_equal("stale-8k-source-revision:mismatch;source=stale123;current=current123")
```

</details>

#### does not flag a fresh (matching) 4K source revision as stale (sabotage control)

- does not flag a fresh (matching) 4K source revision as stale (sabotage control)
- Create a complete 4K row whose source revision matches the current one
- Assert a matching source revision is NOT flagged as mismatch (proves the earlier failures are sensitive to staleness, not vacuous)
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_source_revision_status") equals `current`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `met-200fps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag a fresh (matching) 4K source revision as stale (sabotage control)")
step("Create a complete 4K row whose source revision matches the current one")
val command = "rm -rf build/test-gui-showcase-perf-source-revision-4k-fresh && mkdir -p build/test-gui-showcase-perf-source-revision-4k-fresh/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-source-revision-4k-fresh/source/native4k.bin && chmod +x build/test-gui-showcase-perf-source-revision-4k-fresh/source/native4k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-source-revision-4k-fresh/source/build4k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-source-revision-4k-fresh/source/showcase4k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-source-revision-4k-fresh/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-source-revision-4k-fresh/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\ngui_showcase_4k_200fps_reason=met-target-fps\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\ngui_showcase_4k_200fps_resolution=4k\ngui_showcase_4k_200fps_width=3840\ngui_showcase_4k_200fps_height=2160\ngui_showcase_4k_200fps_frames=200\ngui_showcase_4k_200fps_warmup_frames=12\ngui_showcase_4k_200fps_frame_sample_count=200\ngui_showcase_4k_200fps_fps_x1000=201000\ngui_showcase_4k_200fps_frame_avg_ns=4975124\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\ngui_showcase_4k_200fps_frame_p50_ns=4975124\ngui_showcase_4k_200fps_frame_p95_ns=4975124\ngui_showcase_4k_200fps_target_fps=200\ngui_showcase_4k_200fps_max_rss_kb=131072\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\ngui_showcase_4k_200fps_rss_status=pass\ngui_showcase_4k_200fps_pixels=8294400\ngui_showcase_4k_200fps_nonzero_pixels=1000\ngui_showcase_4k_200fps_checksum=123456\ngui_showcase_4k_200fps_readback_mode=argb-checksum\ngui_showcase_4k_200fps_render_mode=retained-static-frame\ngui_showcase_4k_200fps_redraw_frames=1\ngui_showcase_4k_200fps_source_revision=current123\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl src/lib/gc_async_mut/gpu/engine2d/engine.spl src/lib/gc_async_mut/gpu/engine2d/backend_software.spl\ngui_showcase_4k_200fps_simple_bin=release/x86_64-unknown-linux-gnu/simple\ngui_showcase_4k_200fps_simple_bin_source=self-hosted-release\ngui_showcase_4k_200fps_simple_bin_status=pass\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-source-revision-4k-fresh/source/native4k.bin\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-source-revision-4k-fresh/source/showcase4k.spl\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-source-revision-4k-fresh/source/build4k.log\ngui_showcase_4k_200fps_use_native=1\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\ngui_showcase_4k_200fps_fallback_state=none\ngui_showcase_4k_200fps_alias_raw_rt_count=0\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-source-revision-4k-fresh/source/showcase.log\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-source-revision-4k-fresh/source/time.log\n' > build/test-gui-showcase-perf-source-revision-4k-fresh/source/status.env && GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1 GUI_SHOWCASE_CURRENT_SOURCE_REVISION=current123 GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-source-revision-4k-fresh/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-source-revision-4k-fresh/out REPORT_PATH=build/test-gui-showcase-perf-source-revision-4k-fresh/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, _code) = process_run("/bin/sh", ["-c", command])

step("Assert a matching source revision is NOT flagged as mismatch (proves the earlier failures are sensitive to staleness, not vacuous)")
val evidence = file_read("build/test-gui-showcase-perf-source-revision-4k-fresh/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_source_revision_status")).to_equal("current")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("met-200fps")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `985f7ffc3c75c9368946d467ee476ff4360737138a3ba125c940d780420774be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `985f7ffc3c75c9368946d467ee476ff4360737138a3ba125c940d780420774be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `985f7ffc3c75c9368946d467ee476ff4360737138a3ba125c940d780420774be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl
mirror: doc/06_spec/03_system/check/gui_showcase_perf_source_revision_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_showcase_perf_source_revision_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_showcase_perf_source_revision_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale retained 4K rows when current source revision is required' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale retained 8K rows when current source revision is required' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag a fresh (matching) 4K source revision as stale (sabotage control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
