# GUI Showcase Perf RSS Contract

> Validates that the GUI RenderDoc aggregate derives retained 4K/8K RSS budget proof from numeric RSS values instead of trusting producer-side `*_rss_status=pass`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf RSS Contract

Validates that the GUI RenderDoc aggregate derives retained 4K/8K RSS budget proof from numeric RSS values instead of trusting producer-side `*_rss_status=pass`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_rss_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the GUI RenderDoc aggregate derives retained 4K/8K RSS budget
proof from numeric RSS values instead of trusting producer-side
`*_rss_status=pass`.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_rss_contract_spec.spl --mode=interpreter
```

## Operator Flow

1. Run this focused spec after changing retained-showcase RSS budget checks in
   `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.
2. Inspect `build/test-gui-showcase-perf-rss-4k/out/evidence.env` for the 4K
   aggregate result.
3. Inspect `build/test-gui-showcase-perf-rss-8k/out/evidence.env` for the 8K
   aggregate result.
4. Treat any malformed or over-budget RSS row that still reports aggregate
   `pass` as a completion-gate regression.

## Acceptance

- A retained 4K row with malformed RSS numbers and forged `rss_status=pass` is
  downgraded to `fail`.
- A retained 8K row with malformed RSS numbers and forged `rss_status=pass` is
  downgraded to `fail`.
- Raw numeric RSS evidence wins over producer-side `*_rss_status=pass`.

## Test Matrix

Each case creates complete synthetic retained-showcase evidence except for the
RSS fields. The invalid 4K fields are:

- `gui_showcase_4k_200fps_max_rss_kb=not-a-number`
- `gui_showcase_4k_200fps_max_rss_budget_kb=also-bad`
- `gui_showcase_4k_200fps_rss_status=pass`

The invalid 8K fields mirror the same forged proof under
`gui_showcase_8k_perf_*`. The aggregate must emit `*_rss_status=fail` and a
`*-rss-budget-not-pass:fail` reason.

## Evidence Keys

The spec validates these 4K aggregate keys:

- `gui_showcase_4k_200fps_status`
- `gui_showcase_4k_200fps_reason`
- `gui_showcase_4k_200fps_max_rss_kb`
- `gui_showcase_4k_200fps_max_rss_budget_kb`
- `gui_showcase_4k_200fps_rss_status`

The spec validates these 8K aggregate keys:

- `gui_showcase_8k_perf_status`
- `gui_showcase_8k_perf_reason`
- `gui_showcase_8k_perf_max_rss_kb`
- `gui_showcase_8k_perf_max_rss_budget_kb`
- `gui_showcase_8k_perf_rss_status`

## Failure Semantics

This spec is fail-closed. Producer `rss_status=pass` is accepted only after the
aggregate proves both RSS fields are positive integers and the observed RSS is
less than or equal to the budget.

## Troubleshooting

If this spec fails with missing native artifacts, inspect the generated
`source/native*.bin`, `source/showcase*.spl`, and native build log paths in the
synthetic `status.env`. If it fails with missing log artifacts, inspect
`source/showcase.log` and `source/time.log`. If it fails by returning aggregate
`pass`, the aggregate is accepting producer RSS status without validating the
raw numeric memory budget evidence.

## Relation To Performance Gates

The real 4K and 8K wrappers may emit diagnostic RSS states while a benchmark is
still being tuned. Completion evidence requires `rss_status=pass` backed by a
positive observed RSS value, a positive budget, and observed RSS no greater than
that budget. This contract keeps the aggregate from treating malformed memory
strings as proof of the 4K 200fps or 8K retained performance goal.

## Non-goals

This spec does not decide the RSS budget value, tune allocations, or prove that
the native showcase meets the budget on this host. It only verifies that the
aggregate refuses malformed or over-budget rows before claiming completion.

## Completion Boundary

This test covers aggregate validation of retained-showcase RSS budget evidence
only. It does not prove real 4K/8K throughput, platform GPU backing, browser
RenderDoc capture, or native render-log parity.

## Scenarios

### GUI showcase perf RSS contract

#### rejects retained 4K rows with forged RSS pass status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects retained 4K rows with forged RSS pass status
- Create a 4K performance row with malformed RSS values
- Assert the aggregate rejects forged RSS proof
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_rss_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `4k-rss-budget-not-pass:fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects retained 4K rows with forged RSS pass status")
step("Create a 4K performance row with malformed RSS values")
val command = "rm -rf build/test-gui-showcase-perf-rss-4k && mkdir -p build/test-gui-showcase-perf-rss-4k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-rss-4k/source/native4k.bin && chmod +x build/test-gui-showcase-perf-rss-4k/source/native4k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-rss-4k/source/build4k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-rss-4k/source/showcase4k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-rss-4k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-rss-4k/source/time.log && printf 'gui_showcase_4k_200fps_status=pass\ngui_showcase_4k_200fps_reason=met-target-fps\ngui_showcase_4k_200fps_resolution=4k\ngui_showcase_4k_200fps_width=3840\ngui_showcase_4k_200fps_height=2160\ngui_showcase_4k_200fps_frames=200\ngui_showcase_4k_200fps_warmup_frames=12\ngui_showcase_4k_200fps_frame_sample_count=200\ngui_showcase_4k_200fps_fps_x1000=201000\ngui_showcase_4k_200fps_frame_avg_ns=4975124\ngui_showcase_4k_200fps_frame_elapsed_ns_status=pass\ngui_showcase_4k_200fps_frame_p50_ns=4975124\ngui_showcase_4k_200fps_frame_p95_ns=4975124\ngui_showcase_4k_200fps_target_fps=200\ngui_showcase_4k_200fps_max_rss_kb=not-a-number\ngui_showcase_4k_200fps_max_rss_budget_kb=also-bad\ngui_showcase_4k_200fps_rss_status=pass\ngui_showcase_4k_200fps_pixels=8294400\ngui_showcase_4k_200fps_nonzero_pixels=1000\ngui_showcase_4k_200fps_checksum=123456\ngui_showcase_4k_200fps_backend=simple-retained-widget-showcase\ngui_showcase_4k_200fps_readback_mode=argb-checksum\ngui_showcase_4k_200fps_render_mode=retained-static-frame\ngui_showcase_4k_200fps_redraw_frames=1\ngui_showcase_4k_200fps_source_revision=testrev123\ngui_showcase_4k_200fps_source_revision_kind=content-sha256\ngui_showcase_4k_200fps_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\ngui_showcase_4k_200fps_simple_bin=src/compiler_rust/target/release/simple\ngui_showcase_4k_200fps_native_bin=build/test-gui-showcase-perf-rss-4k/source/native4k.bin\ngui_showcase_4k_200fps_alias_src=build/test-gui-showcase-perf-rss-4k/source/showcase4k.spl\ngui_showcase_4k_200fps_native_build_log=build/test-gui-showcase-perf-rss-4k/source/build4k.log\ngui_showcase_4k_200fps_use_native=1\ngui_showcase_4k_200fps_native_build_mode=aggressive-native\ngui_showcase_4k_200fps_fallback_state=none\ngui_showcase_4k_200fps_log=build/test-gui-showcase-perf-rss-4k/source/showcase.log\ngui_showcase_4k_200fps_time_log=build/test-gui-showcase-perf-rss-4k/source/time.log\n' > build/test-gui-showcase-perf-rss-4k/source/status.env && GUI_SHOWCASE_4K_PERF_ENV=build/test-gui-showcase-perf-rss-4k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-rss-4k/out REPORT_PATH=build/test-gui-showcase-perf-rss-4k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
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

step("Assert the aggregate rejects forged RSS proof")
val evidence = file_read("build/test-gui-showcase-perf-rss-4k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_rss_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("4k-rss-budget-not-pass:fail")
```

</details>

#### rejects retained 8K rows with forged RSS pass status

- rejects retained 8K rows with forged RSS pass status
- Create an 8K performance row with malformed RSS values
- Assert the aggregate rejects forged RSS proof
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_rss_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_reason") equals `8k-rss-budget-not-pass:fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects retained 8K rows with forged RSS pass status")
step("Create an 8K performance row with malformed RSS values")
val command = "rm -rf build/test-gui-showcase-perf-rss-8k && mkdir -p build/test-gui-showcase-perf-rss-8k/source && printf '%b' '\\177ELFsynthetic-native\n' > build/test-gui-showcase-perf-rss-8k/source/native8k.bin && chmod +x build/test-gui-showcase-perf-rss-8k/source/native8k.bin && printf 'native build log\n' > build/test-gui-showcase-perf-rss-8k/source/build8k.log && printf 'fn main() -> i64:\n    0\n' > build/test-gui-showcase-perf-rss-8k/source/showcase8k.spl && printf 'showcase retained log\n' > build/test-gui-showcase-perf-rss-8k/source/showcase.log && printf 'elapsed_ms=597\n' > build/test-gui-showcase-perf-rss-8k/source/time.log && printf 'gui_showcase_8k_perf_status=pass\ngui_showcase_8k_perf_reason=met-target-fps\ngui_showcase_8k_perf_resolution=8k\ngui_showcase_8k_perf_width=7680\ngui_showcase_8k_perf_height=4320\ngui_showcase_8k_perf_frames=200\ngui_showcase_8k_perf_warmup_frames=12\ngui_showcase_8k_perf_frame_sample_count=200\ngui_showcase_8k_perf_fps_x1000=201000\ngui_showcase_8k_perf_frame_avg_ns=4975124\ngui_showcase_8k_perf_frame_elapsed_ns_status=pass\ngui_showcase_8k_perf_frame_p50_ns=4975124\ngui_showcase_8k_perf_frame_p95_ns=4975124\ngui_showcase_8k_perf_target_fps=200\ngui_showcase_8k_perf_max_rss_kb=not-a-number\ngui_showcase_8k_perf_max_rss_budget_kb=also-bad\ngui_showcase_8k_perf_rss_status=pass\ngui_showcase_8k_perf_pixels=33177600\ngui_showcase_8k_perf_nonzero_pixels=1000\ngui_showcase_8k_perf_checksum=123456\ngui_showcase_8k_perf_backend=simple-retained-widget-showcase\ngui_showcase_8k_perf_readback_mode=argb-checksum\ngui_showcase_8k_perf_render_mode=retained-static-frame\ngui_showcase_8k_perf_redraw_frames=1\ngui_showcase_8k_perf_source_revision=testrev123\ngui_showcase_8k_perf_source_revision_kind=content-sha256\ngui_showcase_8k_perf_source_revision_files=scripts/check/check-widget-showcase-4k-200fps.shs examples/06_io/ui/widget_showcase_gui.spl examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl\ngui_showcase_8k_perf_simple_bin=src/compiler_rust/target/release/simple\ngui_showcase_8k_perf_native_bin=build/test-gui-showcase-perf-rss-8k/source/native8k.bin\ngui_showcase_8k_perf_alias_src=build/test-gui-showcase-perf-rss-8k/source/showcase8k.spl\ngui_showcase_8k_perf_native_build_log=build/test-gui-showcase-perf-rss-8k/source/build8k.log\ngui_showcase_8k_perf_use_native=1\ngui_showcase_8k_perf_native_build_mode=aggressive-native\ngui_showcase_8k_perf_fallback_state=none\ngui_showcase_8k_perf_log=build/test-gui-showcase-perf-rss-8k/source/showcase.log\ngui_showcase_8k_perf_time_log=build/test-gui-showcase-perf-rss-8k/source/time.log\n' > build/test-gui-showcase-perf-rss-8k/source/status.env && GUI_SHOWCASE_8K_PERF_ENV=build/test-gui-showcase-perf-rss-8k/source/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=build/test-gui-showcase-perf-rss-8k/out REPORT_PATH=build/test-gui-showcase-perf-rss-8k/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
# See the 4K case above for why the wrapper's overall exit code is not
# asserted here.

step("Assert the aggregate rejects forged RSS proof")
val evidence = file_read("build/test-gui-showcase-perf-rss-8k/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_rss_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_reason")).to_equal("8k-rss-budget-not-pass:fail")
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

- Canonical SPipe generation for source `9fd694498012863257d78d9d618169e730adaaec8960a74a6feb571819f9be87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fd694498012863257d78d9d618169e730adaaec8960a74a6feb571819f9be87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fd694498012863257d78d9d618169e730adaaec8960a74a6feb571819f9be87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/check/gui_showcase_perf_rss_contract_spec.spl
mirror: doc/06_spec/03_system/check/gui_showcase_perf_rss_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_showcase_perf_rss_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_showcase_perf_rss_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_showcase_perf_rss_contract_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects retained 4K rows with forged RSS pass status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_showcase_perf_rss_contract_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects retained 8K rows with forged RSS pass status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
