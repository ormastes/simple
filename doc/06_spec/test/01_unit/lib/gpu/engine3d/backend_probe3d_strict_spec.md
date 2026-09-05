# Backend Probe3d Strict Specification

> <details>

<!-- sdn-diagram:id=backend_probe3d_strict_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_probe3d_strict_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_probe3d_strict_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_probe3d_strict_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Probe3d Strict Specification

## Scenarios

### Engine3D strict partial backend diagnostics

#### reports CPU and software 3D paths as managed usable renderers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = engine3d_strict_probe_backend("cpu")
val software = engine3d_strict_probe_backend("software")

expect(cpu.status).to_equal(Engine3DBackendStatus.Initialized)
expect(cpu.managed_session).to_equal(true)
expect(cpu.has_compute).to_equal(true)
expect(cpu.has_graphics).to_equal(true)
expect(cpu.has_present).to_equal(true)
expect(cpu.strict_failure_without_fallback()).to_equal(true)
expect(software.status).to_equal(Engine3DBackendStatus.Initialized)
expect(software.api_name).to_equal("software")
expect(software.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports CUDA ROCm HIP Metal Vulkan and WebGPU as managed but unavailable without fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prober = Engine3DBackendProber.create()
val cuda = prober.probe_backend("cuda")
val rocm = prober.probe_backend("rocm")
val hip = prober.probe_backend("hip")
val metal = prober.probe_backend("metal")
val vulkan = prober.probe_backend("vulkan")
val webgpu = prober.probe_backend("webgpu")

expect(cuda.status).to_equal(Engine3DBackendStatus.Unavailable)
expect(cuda.shader_format).to_equal("ptx")
expect(cuda.managed_session).to_equal(true)
expect(cuda.strict_failure_without_fallback()).to_equal(true)
expect(rocm.shader_format).to_equal("hsaco")
expect(rocm.feature_gate).to_equal("rocm_hip_3d_runtime")
expect(hip.api_name).to_equal("hip")
expect(hip.strict_failure_without_fallback()).to_equal(true)
expect(metal.shader_format).to_equal("msl")
expect(metal.has_present).to_equal(true)
expect(vulkan.shader_format).to_equal("spirv")
expect(vulkan.has_graphics).to_equal(true)
expect(webgpu.shader_format).to_equal("wgsl")
expect(webgpu.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports OpenCL as compute-only rather than a complete 3D raster backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = engine3d_strict_probe_backend("opencl")

expect(probe.status).to_equal(Engine3DBackendStatus.Unsupported)
expect(probe.api_name).to_equal("opencl")
expect(probe.feature_gate).to_equal("opencl_compute_only")
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### reports OptiX as ray-tracing-only with no raster or present fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = engine3d_strict_probe_backend("optix")

expect(probe.status).to_equal(Engine3DBackendStatus.Unsupported)
expect(probe.api_name).to_equal("optix")
expect(probe.feature_gate).to_equal("optix_ray_tracing_only")
expect(probe.has_compute).to_equal(true)
expect(probe.has_graphics).to_equal(false)
expect(probe.has_present).to_equal(false)
expect(probe.has_ray_tracing).to_equal(true)
expect(probe.strict_failure_without_fallback()).to_equal(true)
```

</details>

#### summary includes all hardened partial 3D backend names

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = Engine3DBackendProber.create().probe_all_summary()

expect(summary).to_contain("requested=cpu")
expect(summary).to_contain("requested=software")
expect(summary).to_contain("requested=cuda")
expect(summary).to_contain("requested=rocm")
expect(summary).to_contain("requested=hip")
expect(summary).to_contain("requested=opencl")
expect(summary).to_contain("requested=metal")
expect(summary).to_contain("requested=vulkan")
expect(summary).to_contain("requested=webgpu")
expect(summary).to_contain("requested=optix")
```

</details>

#### proves CPU and software partial 3D frames with readback checksums

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = engine3d_reference_render_evidence("cpu", 64, 32, 1)
val software = engine3d_reference_render_evidence("software", 64, 32, 2)

expect(cpu.frame_rendered).to_equal(true)
expect(cpu.status_code).to_equal("frame-rendered")
expect(cpu.readback_available).to_equal(true)
expect(cpu.expected_checksum).to_equal(cpu.actual_checksum)
expect(cpu.expected_checksum).to_be_greater_than(0)
expect(cpu.summary()).to_contain("rendered=true")
expect(software.frame_rendered).to_equal(true)
expect(software.expected_checksum).to_equal(software.actual_checksum)
```

</details>

#### keeps GPU partial 3D evidence unavailable until real readback exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = engine3d_reference_render_evidence("cuda", 64, 32, 1)
val metal = engine3d_reference_render_evidence("metal", 64, 32, 1)
val opencl = engine3d_reference_render_evidence("opencl", 64, 32, 1)

expect(cuda.frame_rendered).to_equal(false)
expect(cuda.status_code).to_equal("backend-not-usable")
expect(cuda.summary()).to_contain("rendered=false")
expect(metal.frame_rendered).to_equal(false)
expect(metal.status_code).to_equal("backend-not-usable")
expect(opencl.frame_rendered).to_equal(false)
expect(opencl.status_code).to_equal("backend-not-usable")
```

</details>

#### fails partial 3D render evidence closed on invalid readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_readback = engine3d_render_evidence_from_readback("cpu", 16, 16, 1, false, 123, 123)
val mismatch = engine3d_render_evidence_from_readback("cpu", 16, 16, 1, true, 123, 122)
val no_draws = engine3d_render_evidence_from_readback("cpu", 16, 16, 0, true, 123, 123)

expect(no_readback.frame_rendered).to_equal(false)
expect(no_readback.status_code).to_equal("readback-unavailable")
expect(mismatch.frame_rendered).to_equal(false)
expect(mismatch.status_code).to_equal("readback-mismatch")
expect(no_draws.frame_rendered).to_equal(false)
expect(no_draws.status_code).to_equal("no-draw-calls")
```

</details>

#### requires runtime target buffer and sync evidence before frame readback is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_runtime = engine3d_readback_evidence("cpu", 16, 16, 1, false, 1, 2, true, 123, 123)
val no_target = engine3d_readback_evidence("cpu", 16, 16, 1, true, 0, 2, true, 123, 123)
val no_buffer = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 0, true, 123, 123)
val no_sync = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, false, 123, 123)
val ready = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, true, 123, 123)

expect(no_runtime.readback_available).to_equal(false)
expect(no_runtime.status_code).to_equal("runtime-device-unavailable")
expect(no_target.status_code).to_equal("missing-render-target-handle")
expect(no_buffer.status_code).to_equal("missing-readback-buffer-handle")
expect(no_sync.status_code).to_equal("readback-sync-incomplete")
expect(ready.readback_available).to_equal(true)
expect(ready.status_code).to_equal("readback-ready")
expect(ready.summary()).to_contain("target=1")
```

</details>

#### converts readback evidence into fail-closed render evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, true, 123, 123)
val rendered = engine3d_render_evidence_from_readback_evidence(ready)
val mismatch = engine3d_readback_evidence("cpu", 16, 16, 1, true, 1, 2, true, 123, 122)
val rejected = engine3d_render_evidence_from_readback_evidence(mismatch)

expect(rendered.frame_rendered).to_equal(true)
expect(rendered.status_code).to_equal("frame-rendered")
expect(rejected.frame_rendered).to_equal(false)
expect(rejected.status_code).to_equal("readback-mismatch")
```

</details>

#### does not accept GPU readback handles while strict backend probe lacks real runtime evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = engine3d_readback_evidence("cuda", 16, 16, 1, true, 10, 11, true, 123, 123)
val hip = engine3d_readback_evidence("hip", 16, 16, 1, true, 10, 11, true, 123, 123)
val opencl = engine3d_readback_evidence("opencl", 16, 16, 1, true, 10, 11, true, 123, 123)
val metal = engine3d_readback_evidence("metal", 16, 16, 1, true, 10, 11, true, 123, 123)
val vulkan = engine3d_readback_evidence("vulkan", 16, 16, 1, true, 10, 11, true, 123, 123)
val webgpu = engine3d_readback_evidence("webgpu", 16, 16, 1, true, 10, 11, true, 123, 123)
val optix = engine3d_readback_evidence("optix", 16, 16, 1, true, 10, 11, true, 123, 123)

expect(cuda.status_code).to_equal("backend-not-usable")
expect(hip.status_code).to_equal("backend-not-usable")
expect(opencl.status_code).to_equal("backend-not-usable")
expect(metal.status_code).to_equal("backend-not-usable")
expect(vulkan.status_code).to_equal("backend-not-usable")
expect(webgpu.status_code).to_equal("backend-not-usable")
expect(optix.status_code).to_equal("backend-not-usable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/backend_probe3d_strict_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D strict partial backend diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
