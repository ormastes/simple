# Widget Showcase Perf Wrapper Contract

> Validates the retained GUI showcase performance wrapper without requiring a live 4K or 8K performance host. The wrapper is the canonical producer for `gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` evidence consumed by the GUI RenderDoc feature aggregate.

<!-- sdn-diagram:id=widget_showcase_perf_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_showcase_perf_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_showcase_perf_wrapper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_showcase_perf_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Showcase Perf Wrapper Contract

Validates the retained GUI showcase performance wrapper without requiring a live 4K or 8K performance host. The wrapper is the canonical producer for `gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` evidence consumed by the GUI RenderDoc feature aggregate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/widget_showcase_perf_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the retained GUI showcase performance wrapper without requiring a
live 4K or 8K performance host. The wrapper is the canonical producer for
`gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` evidence consumed by
the GUI RenderDoc feature aggregate.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
PLAN_ONLY=1 RESOLUTION=4k sh scripts/check/check-widget-showcase-4k-200fps.shs
PLAN_ONLY=1 RESOLUTION=8k sh scripts/check/check-widget-showcase-4k-200fps.shs
```

## Operator Flow

1. Use plan-only mode first to confirm wrapper routing without compiling or
   running the expensive native showcase.
2. For the 4K evidence row, run the wrapper with `RESOLUTION=4k` and keep
   `build/widget-showcase-4k-200fps/status.env`.
3. For the 8K evidence row, run the wrapper with `RESOLUTION=8k` and keep
   `build/widget-showcase-8k-perf/status.env`.
4. Feed those env files into the GUI RenderDoc aggregate with
   `GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`.
5. Treat plan-only output as routing evidence only. It is not completion
   evidence because timing, RSS, checksum, and readback measurement rows remain
   empty until a real run executes.

## Acceptance

- 4K plan-only evidence selects `run_4k_perf_probe`, `gui_showcase_4k_perf`,
  `SHOWCASE_4K_PERF`, 3840x2160, 200 frames, and target FPS 200.
- 8K plan-only evidence selects `run_8k_perf_probe`, `gui_showcase_8k_perf`,
  `SHOWCASE_8K_PERF`, 7680x4320, 200 frames, and target FPS 200.
- Plan-only evidence includes native provenance and marks runtime log artifact
  status as `fail` because no expensive benchmark has executed yet.
- Plan-only evidence emits the same measured field keys as a real row with empty
  values for FPS, frame timing, observed RSS, checksum, nonzero readback pixels,
  render mode, and redraw count.
- Native plan-only mode writes the generated alias source that calls the
  selected probe function directly.

## Evidence Contract

The full 4K row must prove:

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_4k_200fps_width=3840`
- `gui_showcase_4k_200fps_height=2160`
- `gui_showcase_4k_200fps_pixels=8294400`
- `gui_showcase_4k_200fps_frames` is at least 200.
- `gui_showcase_4k_200fps_target_fps` is at least 200.
- `gui_showcase_4k_200fps_fps_x1000` meets the target.
- `gui_showcase_4k_200fps_frame_p50_ns` and
  `gui_showcase_4k_200fps_frame_p95_ns` are present for timing distribution
  evidence.
- `gui_showcase_4k_200fps_nonzero_pixels` is positive.
- `gui_showcase_4k_200fps_checksum` is nonempty.
- `gui_showcase_4k_200fps_render_mode=retained-static-frame`
- `gui_showcase_4k_200fps_redraw_frames=1`
- `gui_showcase_4k_200fps_rss_status=pass`
- The showcase log and `/usr/bin/time` log exist.
- Producer-side `*_log_file_status` and `*_time_log_file_status` are `pass`.

The full 8K row has the same contract with:

- `gui_showcase_8k_perf_width=7680`
- `gui_showcase_8k_perf_height=4320`
- `gui_showcase_8k_perf_pixels=33177600`
- `gui_showcase_8k_perf_frames` is at least 200.
- `gui_showcase_8k_perf_frame_p50_ns` and
  `gui_showcase_8k_perf_frame_p95_ns` are present for timing distribution
  evidence.
- Producer-side `*_log_file_status` and `*_time_log_file_status` are `pass`.

## Completion Boundary

This wrapper proves retained static-frame showcase throughput and memory budget
only. It does not prove live redraw throughput, browser GPU backing, native
Vulkan/Metal/D3D12 capture, or production GUI/web parity. Those stay under the
separate RenderDoc, platform render-log, and production parity gates.

## Failure Semantics

The wrapper fails if the probe cannot run, the native build fails, the command
times out before producing probe rows, or the readback does not match the
requested resolution. It also fails when nonzero readback pixels or checksum are
missing, when the render mode is not `retained-static-frame`, when the redraw
count is not exactly one, when the measured FPS is below target, or when the RSS
budget is exceeded. A row with `rss_status=measured` is useful diagnostics but
is not completion evidence for the aggregate gate.

## Aggregate Consumption

The GUI RenderDoc feature aggregate forwards the status rows without launching
the expensive native benchmark. It expects:

- `GUI_SHOWCASE_4K_PERF_ENV` to point at the 4K `status.env`.
- `GUI_SHOWCASE_8K_PERF_ENV` to point at the 8K `status.env`.
- Both rows to include log paths and time-log paths.
- Both log files to exist when the aggregate marks the perf lane complete.

## Native Alias Contract

The wrapper writes a build-local alias source so the native binary enters the
selected probe directly instead of running the full showcase main. This is a
bounded perf harness alias, not a runtime shortcut. The alias must call only
`run_4k_perf_probe()` or `run_8k_perf_probe()` and preserve the original
showcase source imports and helper definitions.

## Test Matrix

The spec covers plan-only 4K and 8K routing. It verifies the selected probe
function, evidence prefix, environment flag, resolution, frame count, target
FPS, pixel count, native provenance fields, empty measured field placeholders,
plan-only log artifact status, and generated native alias source.

## Scenarios

### Widget showcase retained perf wrapper

#### selects the 4K 200fps probe contract

- Run the wrapper in 4K plan-only mode
   - Expected: code equals `0`
- Assert 4K evidence and generated native alias select the 4K probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper in 4K plan-only mode")
val command = "rm -rf build/test-widget-showcase-perf-wrapper-4k && PLAN_ONLY=1 RESOLUTION=4k BUILD_DIR=build/test-widget-showcase-perf-wrapper-4k sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert 4K evidence and generated native alias select the 4K probe")
val evidence = file_read("build/test-widget-showcase-perf-wrapper-4k/status.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=plan-only")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=plan-only")
expect(evidence).to_contain("gui_showcase_4k_200fps_resolution=4k")
expect(evidence).to_contain("gui_showcase_4k_200fps_probe_fn=run_4k_perf_probe")
expect(evidence).to_contain("gui_showcase_4k_200fps_probe_prefix=gui_showcase_4k_perf")
expect(evidence).to_contain("gui_showcase_4k_200fps_perf_env_flag=SHOWCASE_4K_PERF")
expect(evidence).to_contain("gui_showcase_4k_200fps_width=3840")
expect(evidence).to_contain("gui_showcase_4k_200fps_height=2160")
expect(evidence).to_contain("gui_showcase_4k_200fps_frames=200")
expect(evidence).to_contain("gui_showcase_4k_200fps_target_fps=200")
expect(evidence).to_contain("gui_showcase_4k_200fps_pixels=8294400")
expect(evidence).to_contain("gui_showcase_4k_200fps_fps_x1000=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_avg_ns=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_p50_ns=")
expect(evidence).to_contain("gui_showcase_4k_200fps_frame_p95_ns=")
expect(evidence).to_contain("gui_showcase_4k_200fps_max_rss_kb=")
expect(evidence).to_contain("gui_showcase_4k_200fps_rss_status=")
expect(evidence).to_contain("gui_showcase_4k_200fps_nonzero_pixels=")
expect(evidence).to_contain("gui_showcase_4k_200fps_checksum=")
expect(evidence).to_contain("gui_showcase_4k_200fps_render_mode=")
expect(evidence).to_contain("gui_showcase_4k_200fps_redraw_frames=")
expect(evidence).to_contain("gui_showcase_4k_200fps_source_revision=")
expect(evidence).to_contain("gui_showcase_4k_200fps_simple_bin=")
expect(evidence).to_contain("gui_showcase_4k_200fps_use_native=1")
expect(evidence).to_contain("gui_showcase_4k_200fps_native_build_mode=aggressive-native")
expect(evidence).to_contain("gui_showcase_4k_200fps_fallback_state=none")
expect(evidence).to_contain("gui_showcase_4k_200fps_log_file_status=fail")
expect(evidence).to_contain("gui_showcase_4k_200fps_time_log_file_status=fail")

val alias_src = file_read("build/test-widget-showcase-perf-wrapper-4k/widget_showcase_4k_perf.spl")
expect(alias_src).to_contain("fn main() -> i64:")
expect(alias_src).to_contain("run_4k_perf_probe()")
```

</details>

#### selects the 8K retained perf probe contract

- Run the wrapper in 8K plan-only mode
   - Expected: code equals `0`
- Assert 8K evidence and generated native alias select the 8K probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper in 8K plan-only mode")
val command = "rm -rf build/test-widget-showcase-perf-wrapper-8k && PLAN_ONLY=1 RESOLUTION=8k BUILD_DIR=build/test-widget-showcase-perf-wrapper-8k sh scripts/check/check-widget-showcase-4k-200fps.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Assert 8K evidence and generated native alias select the 8K probe")
val evidence = file_read("build/test-widget-showcase-perf-wrapper-8k/status.env")
expect(evidence).to_contain("gui_showcase_8k_perf_status=plan-only")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=plan-only")
expect(evidence).to_contain("gui_showcase_8k_perf_resolution=8k")
expect(evidence).to_contain("gui_showcase_8k_perf_probe_fn=run_8k_perf_probe")
expect(evidence).to_contain("gui_showcase_8k_perf_probe_prefix=gui_showcase_8k_perf")
expect(evidence).to_contain("gui_showcase_8k_perf_perf_env_flag=SHOWCASE_8K_PERF")
expect(evidence).to_contain("gui_showcase_8k_perf_width=7680")
expect(evidence).to_contain("gui_showcase_8k_perf_height=4320")
expect(evidence).to_contain("gui_showcase_8k_perf_frames=200")
expect(evidence).to_contain("gui_showcase_8k_perf_target_fps=200")
expect(evidence).to_contain("gui_showcase_8k_perf_pixels=33177600")
expect(evidence).to_contain("gui_showcase_8k_perf_fps_x1000=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_avg_ns=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_p50_ns=")
expect(evidence).to_contain("gui_showcase_8k_perf_frame_p95_ns=")
expect(evidence).to_contain("gui_showcase_8k_perf_max_rss_kb=")
expect(evidence).to_contain("gui_showcase_8k_perf_rss_status=")
expect(evidence).to_contain("gui_showcase_8k_perf_nonzero_pixels=")
expect(evidence).to_contain("gui_showcase_8k_perf_checksum=")
expect(evidence).to_contain("gui_showcase_8k_perf_render_mode=")
expect(evidence).to_contain("gui_showcase_8k_perf_redraw_frames=")
expect(evidence).to_contain("gui_showcase_8k_perf_source_revision=")
expect(evidence).to_contain("gui_showcase_8k_perf_simple_bin=")
expect(evidence).to_contain("gui_showcase_8k_perf_use_native=1")
expect(evidence).to_contain("gui_showcase_8k_perf_native_build_mode=aggressive-native")
expect(evidence).to_contain("gui_showcase_8k_perf_fallback_state=none")
expect(evidence).to_contain("gui_showcase_8k_perf_log_file_status=fail")
expect(evidence).to_contain("gui_showcase_8k_perf_time_log_file_status=fail")

val alias_src = file_read("build/test-widget-showcase-perf-wrapper-8k/widget_showcase_8k_perf.spl")
expect(alias_src).to_contain("fn main() -> i64:")
expect(alias_src).to_contain("run_8k_perf_probe()")
```

</details>

#### emits retained frame p50 and p95 timing fields for real runs

- Read the wrapper source
- Assert p50 and p95 are derived from the retained timing window


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the wrapper source")
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")

step("Assert p50 and p95 are derived from the retained timing window")
expect(script).to_contain("frame_avg_ns=$((fps_elapsed_ns / FRAMES))")
expect(script).to_contain("frame_p50_ns=$frame_avg_ns")
expect(script).to_contain("frame_p95_ns=$frame_avg_ns")
expect(script).to_contain("_frame_p50_ns=$frame_p50_ns")
expect(script).to_contain("_frame_p95_ns=$frame_p95_ns")
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

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
