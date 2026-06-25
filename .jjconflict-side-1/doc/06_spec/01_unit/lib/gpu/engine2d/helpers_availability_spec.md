# Helpers Availability Specification

> <details>

<!-- sdn-diagram:id=helpers_availability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_availability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_availability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_availability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Availability Specification

## Scenarios

### Engine2D backend availability helpers

#### normalizes explicit platform native backend aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_canonical_name("native")).to_equal("baremetal")
expect(backend_canonical_name("platform-native")).to_equal("baremetal")
expect(backend_canonical_name("virtio-gpu")).to_equal("virtio_gpu")
expect(backend_canonical_name("hip")).to_equal("rocm")
expect(backend_canonical_name("dx11")).to_equal("directx")
expect(backend_canonical_name("simd-cpu")).to_equal("cpu_simd")
```

</details>

#### keeps explicit native backends ahead of auto probed backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val explicit = backend_explicit_native_priority_order()
val full = backend_full_preference_order()
val auto_order = backend_default_priority_order()

expect(explicit).to_equal(["baremetal", "virtio_gpu"])
expect(full[0]).to_equal("baremetal")
expect(full[1]).to_equal("virtio_gpu")
expect(full[2]).to_equal("metal")
expect(auto_order[0]).to_equal("metal")
expect(auto_order).to_equal(["metal", "cuda", "rocm", "qualcomm", "vulkan", "directx", "opencl", "opengl", "intel", "webgpu", "cpu_simd", "software", "cpu"])
```

</details>

#### reports native backend priority and diagnostics without making them auto detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_priority("baremetal")).to_equal(-2)
expect(backend_priority("virtio")).to_equal(-1)
expect(backend_display_name("baremetal")).to_equal("Platform Native Framebuffer")
expect(backend_display_name("virtio_gpu")).to_equal("VirtIO GPU Framebuffer")
expect(backend_display_name("directx")).to_equal("DirectX (D3D11 via DXVK on Linux)")
expect(backend_is_hardware("baremetal")).to_equal(true)
expect(backend_is_hardware("directx")).to_equal(true)
expect(backend_requires_gpu("baremetal")).to_equal(false)
expect(feature_gate_description("virtio_gpu")).to_contain("VirtIO GPU")
expect(feature_gate_description("directx")).to_contain("D3D11")
expect(backend_preference_summary()).to_contain("explicit native")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/helpers_availability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D backend availability helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
