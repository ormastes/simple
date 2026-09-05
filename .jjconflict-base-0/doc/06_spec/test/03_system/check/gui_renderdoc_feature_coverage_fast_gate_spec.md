# GUI RenderDoc feature coverage fast gate

> This fast gate verifies the aggregate GUI RenderDoc feature coverage wrapper without running the historical exhaustive matrix spec. It exists because the matrix spec is intentionally broad and requires a long test timeout profile, while the normal release lane still needs a bounded health check for the aggregate evidence contract.

<!-- sdn-diagram:id=gui_renderdoc_feature_coverage_fast_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_renderdoc_feature_coverage_fast_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_renderdoc_feature_coverage_fast_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_renderdoc_feature_coverage_fast_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI RenderDoc feature coverage fast gate

This fast gate verifies the aggregate GUI RenderDoc feature coverage wrapper without running the historical exhaustive matrix spec. It exists because the matrix spec is intentionally broad and requires a long test timeout profile, while the normal release lane still needs a bounded health check for the aggregate evidence contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md |
| Source | `test/03_system/check/gui_renderdoc_feature_coverage_fast_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This fast gate verifies the aggregate GUI RenderDoc feature coverage wrapper
without running the historical exhaustive matrix spec. It exists because the
matrix spec is intentionally broad and requires a long test timeout profile,
while the normal release lane still needs a bounded health check for the
aggregate evidence contract.

**Plan:** doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/gui_renderdoc_feature_coverage_fast_gate_spec.spl \
  --mode=interpreter --clean --fail-fast
```

The backing aggregate wrapper can be run directly with:

```sh
BUILD_DIR=build/test-gui-renderdoc-feature-coverage-fast \
REPORT_PATH=build/test-gui-renderdoc-feature-coverage-fast/report.md \
GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

## Operator Flow

1. Run this fast gate for normal verification of the aggregate wrapper
   contract.
2. Use `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
   only for exhaustive matrix verification with a long timeout profile or after
   sharding it into smaller scenario files.
3. Use `GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1` only for a
   deliberate cold operator refresh; do not put that cold path in this fast
   SSpec.
4. Treat `gui_renderdoc_feature_coverage_status=incomplete` as a real
   completion blocker. This fast gate proves the evidence contract, not final
   RenderDoc completion.

## Evidence Keys

The fast gate requires these aggregate rows to exist:

- `gui_renderdoc_feature_coverage_status`
- `gui_renderdoc_feature_coverage_reason`
- `gui_showcase_4k_200fps_status`
- `gui_showcase_8k_perf_status`
- `gui_widget_renderdoc_goal_electron_gate_launch_exit_code`
- `gui_widget_renderdoc_goal_electron_gate_launch_timed_out`
- `gui_widget_renderdoc_goal_electron_gate_launch_metadata_status`
- `gui_widget_renderdoc_goal_electron_gate_launch_metadata_reason`
- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_status`
- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_count`
- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_codes`

It also requires the default cache to contain at least one fingerprinted
`sspec-traceability-*` evidence file. That proves the aggregate wrapper reused a
nested gate through the cache path rather than depending on the old caller-only
`GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` behavior.

## Result Interpretation

`gui_renderdoc_feature_coverage_status=incomplete` is acceptable for this fast
gate when the current host still lacks Electron/Chrome/RenderDoc completion
artifacts. The status is still forwarded so completion audits can fail closed.
The fast gate only proves that the aggregate wrapper runs, emits the contract,
and keeps the 4K/8K and Electron diagnostics visible.

`gui_showcase_4k_200fps_status=pass` proves retained 4K performance evidence is
present in the aggregate. `gui_showcase_8k_perf_status=pass` proves retained 8K
evidence is present. These rows do not prove live Vulkan browser capture; those
claims remain gated by the full aggregate and platform RenderDoc evidence.

The Electron launch fields distinguish a renderer launch timeout from a GPU
process crash. The GPU process fields preserve the Chromium crash signature such
as exit code `139` so a missing `.rdc` does not become an untyped failure.

## Troubleshooting

If this fast gate times out, first run the backing aggregate wrapper directly
with the command in the Syntax section. If the direct wrapper is fast but the
SSpec times out, treat it as a test-daemon/spec-size issue and do not rerun the
same full matrix repeatedly.

If the default cache assertion fails, check whether
`GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1` leaked into the test
environment. The fast lane expects the default cache to be enabled.
Do not delete `build/gui-renderdoc-feature-coverage-static-cache` as part of the
fast gate; that turns a bounded contract check into a cold nested-gate refresh.

If 4K or 8K rows are missing, refresh the retained showcase evidence with
`scripts/check/check-widget-showcase-4k-200fps.shs` before claiming GUI
showcase performance. Do not substitute a small viewport or cached replay for an
8K pass.

## Acceptance

- The aggregate wrapper completes with default fingerprinted nested-gate cache.
- The wrapper emits stable aggregate status keys.
- The wrapper forwards retained 4K/8K showcase performance status keys.
- The wrapper forwards Electron RenderDoc launch and GPU-process diagnostics.

## Scenarios

### GUI RenderDoc feature coverage fast gate

#### runs aggregate audit with default nested-gate cache

- Run the aggregate audit from a clean fast-gate build directory
   - Expected: code equals `0`
- Read the emitted aggregate evidence
- Confirm the default cache populated nested gate evidence
   - Expected: cache_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the aggregate audit from a clean fast-gate build directory")
val command = "rm -rf build/test-gui-renderdoc-feature-coverage-fast && BUILD_DIR=build/test-gui-renderdoc-feature-coverage-fast REPORT_PATH=build/test-gui-renderdoc-feature-coverage-fast/report.md GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the emitted aggregate evidence")
val evidence = file_read("build/test-gui-renderdoc-feature-coverage-fast/evidence.env")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_status=")
expect(evidence).to_contain("gui_renderdoc_feature_coverage_reason=")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_launch_exit_code=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_launch_timed_out=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_launch_metadata_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_launch_metadata_reason=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_status=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_count=")
expect(evidence).to_contain("gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_codes=")

step("Confirm the default cache populated nested gate evidence")
val (cache_stdout, _cache_stderr, cache_code) = process_run("/bin/sh", ["-c", "find build/gui-renderdoc-feature-coverage-static-cache -name evidence.env | sort | tr '\\n' ' '"])
expect(cache_code).to_equal(0)
expect(cache_stdout).to_contain("build/gui-renderdoc-feature-coverage-static-cache/sspec-traceability-")
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

- **Plan:** [doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md](doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md)


</details>
