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
| 2 | 2 | 0 | 0 |

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

## Acceptance

- 4K plan-only evidence selects `run_4k_perf_probe`, `gui_showcase_4k_perf`,
  `SHOWCASE_4K_PERF`, 3840x2160, 200 frames, and target FPS 200.
- 8K plan-only evidence selects `run_8k_perf_probe`, `gui_showcase_8k_perf`,
  `SHOWCASE_8K_PERF`, 7680x4320, 120 frames, and target FPS 200.
- Native plan-only mode writes the generated alias source that calls the
  selected probe function directly.

## Scenarios

### Widget showcase retained perf wrapper

#### selects the 4K 200fps probe contract

- Run the wrapper in 4K plan-only mode
   - Expected: code equals `0`
- Assert 4K evidence and generated native alias select the 4K probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
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

Runnable source: 22 lines folded for reproduction.
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
expect(evidence).to_contain("gui_showcase_8k_perf_frames=120")
expect(evidence).to_contain("gui_showcase_8k_perf_target_fps=200")
expect(evidence).to_contain("gui_showcase_8k_perf_pixels=33177600")

val alias_src = file_read("build/test-widget-showcase-perf-wrapper-8k/widget_showcase_8k_perf.spl")
expect(alias_src).to_contain("fn main() -> i64:")
expect(alias_src).to_contain("run_8k_perf_probe()")
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
