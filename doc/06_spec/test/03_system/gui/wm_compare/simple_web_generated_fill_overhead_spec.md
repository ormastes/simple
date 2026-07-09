# Simple Web generated fill offload cost evidence

> Measures generated Vulkan fill work against a CPU scalar baseline. The fixture keeps GPU work, artifact submission, synchronization, and readback visible so a faster result cannot hide communication overhead.

<!-- sdn-diagram:id=simple_web_generated_fill_overhead_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_generated_fill_overhead_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_generated_fill_overhead_spec -> std
simple_web_generated_fill_overhead_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_generated_fill_overhead_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web generated fill offload cost evidence

Measures generated Vulkan fill work against a CPU scalar baseline. The fixture keeps GPU work, artifact submission, synchronization, and readback visible so a faster result cannot hide communication overhead.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/gui/wm_compare/simple_web_generated_fill_overhead_spec.spl` |
| Updated | 2026-07-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Measures generated Vulkan fill work against a CPU scalar baseline. The fixture
keeps GPU work, artifact submission, synchronization, and readback visible so
a faster result cannot hide communication overhead.

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Design:** doc/05_design/host_gpu_lane.md

## Syntax

Run the generated fill cost scenarios with:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/gui/wm_compare/simple_web_generated_fill_overhead_spec.spl --mode=interpreter
```

## Acceptance

- A slower generated fill with transfer/submit cost dominating is classified as
  `offload-slower-communication-overhead`.
- A faster generated fill with the same dominant cost is classified as
  `offload-faster-but-overhead-dominates`.

## Scenarios

### Simple Web generated fill GPU offload measurement

#### classifies generated fill offload as communication overhead when transfer dominates

<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_comparison_sample_from_measurement(
    InitializedGpuRuntimeMeasurement(
    backend: "vulkan",
    operation_family: "fill",
    fixture_id: "simple-web:many-tiny-fill:overhead",
    shell: "simple-web",
    command: "simple web renderer generated fill overhead fixture",
    host: "linux-x86_64",
    warmup_count: 1,
    sample_count: 5,
    p50_frame_us: 2500,
    p95_frame_us: 2700,
    max_rss_kb: 72000,
    binary_size_bytes: 2100000,
    baseline_binary_size_bytes: 2050000,
    render_readback_scope: "render+readback",
    cold_start_us: 52000,
    warm_start_us: 7800,
    package_size_bytes: 2200000,
    p95_input_to_paint_us: 2800,
    artifact_build_us: 100,
    artifact_load_us: 100,
    artifact_submit_us: 2100,
    artifact_sync_us: 100,
    artifact_readback_us: 100,
    checksum: "sha256:simple-web:fill-overhead",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "vulkan:fixture",
    width: 16,
    height: 16,
    runtime_ready: true,
    module_ready: true,
    args_ptr: 4096
    )
)
expect(sample.shell).to_equal("simple-web")
expect(sample.operation_family).to_equal("fill")
expect(sample.runtime_execution_path).to_equal("generated_2d_kernel")
expect(sample.runtime_entry_symbol).to_equal("simple_2d_fill_u32")
expect(backend_comparison_offload_efficiency_verdict(sample, 2000)).to_equal("offload-slower-communication-overhead")
```

</details>

#### keeps generated fill overhead visible when offload still wins overall

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = initialized_gpu_comparison_sample_from_measurement(
    InitializedGpuRuntimeMeasurement(
    backend: "vulkan",
    operation_family: "fill",
    fixture_id: "simple-web:many-tiny-fill:faster-overhead",
    shell: "simple-web",
    command: "simple web renderer generated fill faster overhead fixture",
    host: "linux-x86_64",
    warmup_count: 1,
    sample_count: 5,
    p50_frame_us: 1500,
    p95_frame_us: 1700,
    max_rss_kb: 72000,
    binary_size_bytes: 2100000,
    baseline_binary_size_bytes: 2050000,
    render_readback_scope: "render+readback",
    cold_start_us: 52000,
    warm_start_us: 7800,
    package_size_bytes: 2200000,
    p95_input_to_paint_us: 1800,
    artifact_build_us: 100,
    artifact_load_us: 100,
    artifact_submit_us: 1100,
    artifact_sync_us: 100,
    artifact_readback_us: 100,
    checksum: "sha256:simple-web:fill-faster-overhead",
    pixel_proof: "nonzero_pixels:4096",
    device_id: "vulkan:fixture",
    width: 16,
    height: 16,
    runtime_ready: true,
    module_ready: true,
    args_ptr: 4096
    )
)
expect(backend_comparison_offload_efficiency_verdict(sample, 2000)).to_equal("offload-faster-but-overhead-dominates")
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

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
