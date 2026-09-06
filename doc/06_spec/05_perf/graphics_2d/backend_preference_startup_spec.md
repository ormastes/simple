# Backend Preference Startup Specification

> <details>

<!-- sdn-diagram:id=backend_preference_startup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_preference_startup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_preference_startup_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_preference_startup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Preference Startup Specification

## Scenarios

### graphics_2d backend preference startup

#### keeps explicit-native and auto drawing order stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drawing = engine2d_backend_lane_drawing_preference_order()
val full = engine2d_backend_lane_full_preference_order()

expect(drawing[0]).to_equal("metal")
expect(drawing[1]).to_equal("cuda")
expect(drawing[2]).to_equal("rocm")
expect(drawing[4]).to_equal("vulkan")
expect(drawing[5]).to_equal("directx")
expect(full[0]).to_equal("baremetal")
expect(full[1]).to_equal("virtio_gpu")
expect(full[2]).to_equal("metal")
expect(engine2d_backend_lane_preference_summary()).to_contain("vulkan > directx > opencl")
```

</details>

#### keeps vector and bitmap font offload order GPU-first

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = engine2d_font_offload_backend_order()

expect(font[0]).to_equal("metal")
expect(font[1]).to_equal("cuda")
expect(font[2]).to_equal("rocm")
expect(font[4]).to_equal("vulkan")
expect(font[10]).to_equal("cpu_simd")
expect(font[11]).to_equal("software")
expect(font[12]).to_equal("cpu")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["software", "cpu_simd", "vulkan"])).to_equal("vulkan")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["cpu", "amd-hip", "cuda"])).to_equal("cuda")
```

</details>

#### keeps preference helper startup path bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed_us = _bench_preference_helpers(1000)
print "[perf] backend preference helpers: {elapsed_us} us for 1000 iterations"

expect(elapsed_us).to_be_less_than(2000000i64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/backend_preference_startup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- graphics_2d backend preference startup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
