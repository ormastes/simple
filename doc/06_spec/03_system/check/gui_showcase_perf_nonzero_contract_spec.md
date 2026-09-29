# GUI Showcase Perf Nonzero Contract

> Validates that the GUI RenderDoc aggregate does not trust a self-reported nonzero-pixel pass row when the retained 4K or 8K showcase readback value is not a positive integer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Nonzero Contract

Validates that the GUI RenderDoc aggregate does not trust a self-reported nonzero-pixel pass row when the retained 4K or 8K showcase readback value is not a positive integer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_nonzero_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the GUI RenderDoc aggregate does not trust a self-reported
nonzero-pixel pass row when the retained 4K or 8K showcase readback value is
not a positive integer.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_nonzero_contract_spec.spl --mode=interpreter
```

## Operator Flow

1. Run this focused spec after changing the retained-showcase portion of
   `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.
2. Inspect `build/test-gui-showcase-perf-nonzero-4k/out/evidence.env` for the
   retained 4K aggregate result.
3. Inspect `build/test-gui-showcase-perf-nonzero-8k/out/evidence.env` for the
   retained 8K aggregate result.
4. Treat any `*_nonzero_pixels_status=pass` result for malformed pixel text as
   a regression in the aggregate gate.

## Acceptance

- A retained 4K row with malformed `gui_showcase_4k_200fps_nonzero_pixels` is
  downgraded to `fail`.
- A retained 8K row with malformed `gui_showcase_8k_perf_nonzero_pixels` is
  downgraded to `fail`.
- Explicit producer-side `*_nonzero_pixels_status=pass` cannot override the
  malformed readback value.

## Test Matrix

The 4K case creates a complete synthetic retained-showcase row, including
timing, RSS, checksum, source revision, alias source, native binary, build log,
showcase log, and time log artifacts. The only invalid field is
`gui_showcase_4k_200fps_nonzero_pixels=not-a-number`, while
`gui_showcase_4k_200fps_nonzero_pixels_status=pass` is deliberately forged.
The aggregate must emit:

- `gui_showcase_4k_200fps_status=fail`
- `gui_showcase_4k_200fps_nonzero_pixels_status=fail`
- `gui_showcase_4k_200fps_reason=blank-4k-readback:fail`

The 8K case mirrors the same structure with
`gui_showcase_8k_perf_nonzero_pixels=also-bad` and a forged
`gui_showcase_8k_perf_nonzero_pixels_status=pass`. The aggregate must emit:

- `gui_showcase_8k_perf_status=fail`
- `gui_showcase_8k_perf_nonzero_pixels_status=fail`
- `gui_showcase_8k_perf_reason=blank-8k-readback:fail`

## Failure Semantics

This spec is fail-closed. A producer-provided status is accepted only after the
aggregate derives that the source value is a positive integer. Empty, zero,
negative, or malformed pixel counts are blank readback evidence and must keep
the retained 4K/8K completion lanes failed even when every other synthetic
artifact is present.

## Evidence Keys

The 4K regression row must write and validate these aggregate keys:

- `gui_showcase_4k_200fps_env`
- `gui_showcase_4k_200fps_status`
- `gui_showcase_4k_200fps_reason`
- `gui_showcase_4k_200fps_resolution`
- `gui_showcase_4k_200fps_width`
- `gui_showcase_4k_200fps_height`
- `gui_showcase_4k_200fps_pixels`
- `gui_showcase_4k_200fps_nonzero_pixels`
- `gui_showcase_4k_200fps_nonzero_pixels_status`
- `gui_showcase_4k_200fps_checksum`
- `gui_showcase_4k_200fps_log_file_status`
- `gui_showcase_4k_200fps_time_log_file_status`
- `gui_showcase_4k_200fps_native_bin_file_status`
- `gui_showcase_4k_200fps_native_bin_executable_status`
- `gui_showcase_4k_200fps_native_bin_format_status`

The 8K regression row must write and validate the matching keys:

- `gui_showcase_8k_perf_env`
- `gui_showcase_8k_perf_status`
- `gui_showcase_8k_perf_reason`
- `gui_showcase_8k_perf_resolution`
- `gui_showcase_8k_perf_width`
- `gui_showcase_8k_perf_height`
- `gui_showcase_8k_perf_pixels`
- `gui_showcase_8k_perf_nonzero_pixels`
- `gui_showcase_8k_perf_nonzero_pixels_status`
- `gui_showcase_8k_perf_checksum`
- `gui_showcase_8k_perf_log_file_status`
- `gui_showcase_8k_perf_time_log_file_status`
- `gui_showcase_8k_perf_native_bin_file_status`
- `gui_showcase_8k_perf_native_bin_executable_status`
- `gui_showcase_8k_perf_native_bin_format_status`

## Troubleshooting

If this spec fails with a native artifact reason, check that the synthetic ELF
files are still executable and that the status row points at the generated
alias source and build log. If it fails with a missing log reason, inspect the
two generated `source/showcase.log` and `source/time.log` files. If it fails by
returning `pass`, the aggregate is trusting a producer status before validating
the raw nonzero-pixel value and must be fixed before any 4K/8K completion claim.

## Completion Boundary

This test covers aggregate validation of retained-showcase nonzero-pixel rows.
It does not prove real 4K/8K throughput, real GPU readback, Vulkan/Metal/D3D12
capture, browser GPU backing, or RenderDoc artifact validity. Those remain
separate platform evidence gates.

## Scenarios

### GUI showcase perf nonzero contract

#### rejects retained 4K rows with malformed nonzero-pixel evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects retained 4K rows with malformed nonzero-pixel evidence
- Create a 4K retained performance row with a forged nonzero-pixel pass
- Assert the aggregate ignores the forged producer pass
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_nonzero_pixels_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `blank-4k-readback:fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects retained 4K rows with malformed nonzero-pixel evidence")
step("Create a 4K retained performance row with a forged nonzero-pixel pass")
val command = "rm -rf build/test-gui-showcase-perf-nonzero-4k && mkdir -p build/test-gui-showcase-perf-nonzero-4k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-nonzero-4k/source/native4k.bin && chmod +x build/test-gui-showcase-perf-nonzero-4k/source/native4k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-nonzero-4k/source/build4k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-nonzero-4k/source/showcase4k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-nonzero-4k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-nonzero-4k/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\ngui_showcase_4k_200fps_reason=met-target-fps\ngui_showcase_4k_200fps_resolution=4k\ngui_showcase_4k_200fps_width=3840\ngui_showcase_4k_200fps_height=2160\ngui_showcase_4k_200fps_frames=200\ngui_showcase_4k_200fps_warmup_frames=12\ngui_showcase_4k_200fps_frame_sample_count=200\ngui_showcase_4k_200fps_fps_x1000=201000\ngui_showcase_4k_200fps_frame_avg_ns=4975124\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\ngui_showcase_4k_200fps_frame_p50_ns=4975124\ngui_showcase_4k_200fps_frame_p95_ns=4975124\ngui_showcase_4k_200fps_target_fps=200\ngui_showcase_4k_200fps_max_rss_kb=131072\ngui_showcase_4k_200fps_max_rss_budget_kb=262144\ngui_showcase_4k_200fps_rss_status=pass\ngui_showcase_4k_200fps_pixels=8294400\ngui_showcase_4k_200fps_nonzero_pixels=not-a-number\ngui_showcase_4k_200fps_nonzero_pixels_status=pass\ngui_showcase_4k_200fps_checksum=123456\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\ngui_showcase_4k_200fps_readback_mode=argb-checksum\ngui_showcase_4k_200fps_render_mode=retained-static-frame\ngui_showcase_4k_200fps_redraw_frames=1\ngui_showcase_4k_200fps_source_revision=testrev123\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-nonzero-4k/source/native4k.bin\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-nonzero-4k/source/showcase4k.spl\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-nonzero-4k/source/build4k.log\ngui_showcase_4k_200fps_use_native=1\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\ngui_showcase_4k_200fps_fallback_state=none\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-nonzero-4k/source/showcase.log\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-nonzero-4k/source/time.log\n' > build/test-gui-showcase-perf-nonzero-4k/source/status.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-nonzero-4k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-nonzero-4k/out REPORT_PATH=build/test-gui-showcase-perf-nonzero-4k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
# NOTE (2026-08-07, T18): do NOT assert the wrapper's overall process
# exit code here. check-gui-renderdoc-feature-coverage-status.shs is a
# whole-repo aggregate gate that exits non-zero whenever ANY of its many
# unrelated evidence categories (widget-kind coverage, layout manifest,
# etc.) is incomplete -- which this synthetic single-row fixture always
# leaves incomplete. That is correct behavior of the aggregate gate, not
# a defect; the contract this spec tests is captured entirely in
# evidence.env below, which the wrapper writes before it exits non-zero.
# See doc/08_tracking/bug/gui_showcase_source_revision_spec_asserted_wrong_exit_code_2026-08-07.md.

step("Assert the aggregate ignores the forged producer pass")
val evidence = file_read("build/test-gui-showcase-perf-nonzero-4k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_nonzero_pixels_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("blank-4k-readback:fail")
```

</details>

#### rejects retained 8K rows with malformed nonzero-pixel evidence

- rejects retained 8K rows with malformed nonzero-pixel evidence
- Create an 8K retained performance row with a forged nonzero-pixel pass
- Assert the aggregate ignores the forged producer pass
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_nonzero_pixels_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_reason") equals `blank-8k-readback:fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects retained 8K rows with malformed nonzero-pixel evidence")
step("Create an 8K retained performance row with a forged nonzero-pixel pass")
val command = "rm -rf build/test-gui-showcase-perf-nonzero-8k && mkdir -p build/test-gui-showcase-perf-nonzero-8k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-nonzero-8k/source/native8k.bin && chmod +x build/test-gui-showcase-perf-nonzero-8k/source/native8k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-nonzero-8k/source/build8k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-nonzero-8k/source/showcase8k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-nonzero-8k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-nonzero-8k/source/time.log && printf 'gui_showcase_8k_perf_status=pass\ngui_showcase_8k_perf_reason=met-target-fps\ngui_showcase_8k_perf_resolution=8k\ngui_showcase_8k_perf_width=7680\ngui_showcase_8k_perf_height=4320\ngui_showcase_8k_perf_frames=200\ngui_showcase_8k_perf_warmup_frames=12\ngui_showcase_8k_perf_frame_sample_count=200\ngui_showcase_8k_perf_fps_x1000=201000\ngui_showcase_8k_perf_frame_avg_ns=4975124\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\ngui_showcase_8k_perf_frame_p50_ns=4975124\ngui_showcase_8k_perf_frame_p95_ns=4975124\ngui_showcase_8k_perf_target_fps=200\ngui_showcase_8k_perf_max_rss_kb=524288\ngui_showcase_8k_perf_max_rss_budget_kb=1048576\ngui_showcase_8k_perf_rss_status=pass\ngui_showcase_8k_perf_pixels=33177600\ngui_showcase_8k_perf_nonzero_pixels=also-bad\ngui_showcase_8k_perf_nonzero_pixels_status=pass\ngui_showcase_8k_perf_checksum=123456\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\ngui_showcase_8k_perf_readback_mode=argb-checksum\ngui_showcase_8k_perf_render_mode=retained-static-frame\ngui_showcase_8k_perf_redraw_frames=1\ngui_showcase_8k_perf_source_revision=testrev123\ngui_showcase_8k_perf_source_revision_kind=content-sha256\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\ngui_showcase_8k_perf_native_bin=build/test-gui-showcase-perf-nonzero-8k/source/native8k.bin\ngui_showcase_8k_perf_alias_src=build/test-gui-showcase-perf-nonzero-8k/source/showcase8k.spl\ngui_showcase_8k_perf_native_build_log=build/test-gui-showcase-perf-nonzero-8k/source/build8k.log\ngui_showcase_8k_perf_use_native=1\ngui_showcase_8k_perf_native_build_mode=aggressive-native\ngui_showcase_8k_perf_fallback_state=none\ngui_showcase_8k_perf_log=build/test-gui-showcase-perf-nonzero-8k/source/showcase.log\ngui_showcase_8k_perf_time_log=build/test-gui-showcase-perf-nonzero-8k/source/time.log\n' > build/test-gui-showcase-perf-nonzero-8k/source/status.env && GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-showcase-perf-nonzero-8k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-nonzero-8k/out REPORT_PATH=build/test-gui-showcase-perf-nonzero-8k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
# See the 4K case above for why the wrapper's overall exit code is not
# asserted here.

step("Assert the aggregate ignores the forged producer pass")
val evidence = file_read("build/test-gui-showcase-perf-nonzero-8k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_nonzero_pixels_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_reason")).to_equal("blank-8k-readback:fail")
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

- Canonical SPipe generation for source `557cb6972f5be2413c0395d63a46d951851b5e4f4547e077b45acee817e0c546`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `557cb6972f5be2413c0395d63a46d951851b5e4f4547e077b45acee817e0c546`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `557cb6972f5be2413c0395d63a46d951851b5e4f4547e077b45acee817e0c546`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/check/gui_showcase_perf_nonzero_contract_spec.spl
mirror: doc/06_spec/03_system/check/gui_showcase_perf_nonzero_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_showcase_perf_nonzero_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_showcase_perf_nonzero_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_showcase_perf_nonzero_contract_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects retained 4K rows with malformed nonzero-pixel evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_showcase_perf_nonzero_contract_spec.spl:170:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects retained 8K rows with malformed nonzero-pixel evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
