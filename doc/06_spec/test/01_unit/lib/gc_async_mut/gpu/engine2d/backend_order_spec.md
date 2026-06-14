# Backend Order Specification

> <details>

<!-- sdn-diagram:id=backend_order_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_order_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_order_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_order_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Order Specification

## Scenarios

### Engine2D backend preference order

#### keeps platform native and GPU backends ahead of CPU fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val order = backend_default_priority_order()

expect(order.len()).to_equal(13)
expect(order[0]).to_equal("metal")
expect(order[1]).to_equal("cuda")
expect(order[2]).to_equal("rocm")
expect(order[3]).to_equal("qualcomm")
expect(order[4]).to_equal("vulkan")
expect(order[5]).to_equal("directx")
expect(order[6]).to_equal("opencl")
expect(order[7]).to_equal("opengl")
expect(order[8]).to_equal("intel")
expect(order[9]).to_equal("webgpu")
expect(order[10]).to_equal("software")
expect(order[11]).to_equal("cpu_simd")
expect(order[12]).to_equal("cpu")
```

</details>

#### keeps the summary aligned with the executable order

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_preference_summary()).to_equal("explicit native (baremetal/virtio_gpu) > metal > cuda > rocm/hip > qualcomm > vulkan > directx > opencl > opengl > intel > webgpu > software > cpu_simd > cpu")
```

</details>

#### normalizes UI aliases before backend probing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_canonical_name("hip")).to_equal("rocm")
expect(backend_canonical_name("amd_hip")).to_equal("rocm")
expect(backend_canonical_name("amd-hip")).to_equal("rocm")
expect(backend_canonical_name("amd_rocm")).to_equal("rocm")
expect(backend_canonical_name("amd-rocm")).to_equal("rocm")
expect(backend_canonical_name("d3d11")).to_equal("directx")
expect(backend_canonical_name("d3d12")).to_equal("directx")
expect(backend_canonical_name("dx11")).to_equal("directx")
expect(backend_canonical_name("dx12")).to_equal("directx")
expect(backend_canonical_name("simd_cpu")).to_equal("cpu_simd")
expect(backend_canonical_name("cpu-simd")).to_equal("cpu_simd")
expect(backend_canonical_name("simd-cpu")).to_equal("cpu_simd")
```

</details>

#### keeps backend priority numeric order consistent with auto selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_priority("metal")).to_be_less_than(backend_priority("cuda"))
expect(backend_priority("cuda")).to_be_less_than(backend_priority("rocm"))
expect(backend_priority("rocm")).to_be_less_than(backend_priority("vulkan"))
expect(backend_priority("rocm")).to_be_less_than(backend_priority("qualcomm"))
expect(backend_priority("qualcomm")).to_be_less_than(backend_priority("vulkan"))
expect(backend_priority("vulkan")).to_be_less_than(backend_priority("directx"))
expect(backend_priority("directx")).to_be_less_than(backend_priority("opencl"))
expect(backend_priority("opencl")).to_be_less_than(backend_priority("opengl"))
expect(backend_priority("opengl")).to_be_less_than(backend_priority("intel"))
expect(backend_priority("intel")).to_be_less_than(backend_priority("webgpu"))
expect(backend_priority("vulkan")).to_be_less_than(backend_priority("software"))
expect(backend_priority("webgpu")).to_be_less_than(backend_priority("software"))
expect(backend_priority("software")).to_be_less_than(backend_priority("cpu_simd"))
expect(backend_priority("cpu_simd")).to_be_less_than(backend_priority("cpu"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_order_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D backend preference order

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
