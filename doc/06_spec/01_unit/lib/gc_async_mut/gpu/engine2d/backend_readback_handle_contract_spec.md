# Engine2D backend readback handle contract

> Prevents Engine2D backends from reporting `device_readback` through the zero-handle helper. Vulkan must use `engine2d_readback_with_identity(..., session.device)`; other backends must preserve a concrete handle or prove equivalent identity propagation.

<!-- sdn-diagram:id=backend_readback_handle_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_readback_handle_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_readback_handle_contract_spec -> `engine2d_readback_with_handle(
backend_readback_handle_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_readback_handle_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D backend readback handle contract

Prevents Engine2D backends from reporting `device_readback` through the zero-handle helper. A backend may use `device_readback` only when it also uses `engine2d_readback_with_handle(...)` with a concrete backend handle, or when a platform-specific runtime test proves equivalent handle propagation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_readback_handle_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Prevents Engine2D backends from reporting `device_readback` through the
zero-handle helper. Vulkan uses
`engine2d_readback_with_identity(..., session.device)` so the readback retains
the immutable backend-session identity; other backends preserve a concrete
handle or prove equivalent identity propagation.

This spec is intentionally source-contract evidence because several backends
require platform runtimes that are not available on every CI host. Runtime
queue, BrowserBackend, Vulkan, and CUDA wrappers provide the hardware evidence
where those hosts are available.

**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/05_design/host_gpu_lane.md

## Syntax

Backends with real device readback should preserve a concrete handle:

```simple
engine2d_readback_with_handle(pixels, "device_readback", backend_handle)
```

Backends without a concrete handle should use non-device provenance:

```simple
engine2d_readback(pixels, "cpu_mirror")
engine2d_readback(pixels, "framebuffer_surface")
engine2d_readback(pixels, "not_requested")
engine2d_readback_with_handle(pixels, "surface_upload", surface_handle)
engine2d_readback_with_handle(pixels, "swapchain_present", swapchain_handle)
```

## Examples

Vulkan, CUDA, OpenCL, Metal, OpenGL, ROCm, and initialized DirectX
device-readback branches preserve
their initialized backend handle. Baremetal framebuffer reads remain
`framebuffer_surface` until `FramebufferSurface` exposes a stable handle.
DirectX may report `device_readback` only after its no-GC D3D11/DXVK readback
target returns the expected pixel count through a positive readback handle;
checksum is evidence but must not be the validity gate because an all-zero
frame is valid. Otherwise it may report `swapchain_present` with a positive
swapchain handle when presentation was accepted. WebGPU may report `surface_upload` with
a positive surface handle when an initialized WebGPU surface accepted the frame
upload. Presentation/upload provenance remains separate from production backend
readback proof.

## Acceptance

- CPU mirror, cache, framebuffer-surface, and not-requested paths may use
  `engine2d_readback(...)` with handle `0`; WebGPU surface-upload receipts may
  use `engine2d_readback_with_handle(...)` with non-device `surface_upload`, and
  DirectX presentation receipts may use non-device `swapchain_present`.
- DirectX `device_readback` must be gated by `last_readback_ok`, a positive
  `readback_handle`, and exact no-GC readback pixel count.
- Device readback paths must not use the zero-handle helper.
- Backends without a concrete handle must use a non-device provenance string
  until their API exposes one.

## Scenarios

### Engine2D backend readback handle contract

#### does not classify zero-handle helper readbacks as device readback

- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
- violations = violations + zero handle device readback violations
   - Expected: violations equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var violations = ""
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_intel.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_opencl.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_opengl.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_rocm.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_virtio_gpu.spl")
violations = violations + zero_handle_device_readback_violations("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
expect(violations).to_equal("")
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

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
