# Graphics Backend Acceleration Specification

> 1. var st = AccelProbeStatus available

<!-- sdn-diagram:id=graphics_backend_acceleration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graphics_backend_acceleration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graphics_backend_acceleration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graphics_backend_acceleration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphics Backend Acceleration Specification

## Scenarios

### graphics backend acceleration

#### AccelProbeStatus

#### available status has correct code

1. var st = AccelProbeStatus available
   - Expected: st.code equals `available`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = AccelProbeStatus.available("ready")
expect(st.code).to_equal("available")
```

</details>

#### unavailable status is not available

1. var st = AccelProbeStatus unavailable
   - Expected: st.is_available() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = AccelProbeStatus.unavailable("no device")
expect(st.is_available() == false).to_equal(true)
```

</details>

#### fallback status has fallback code

1. var st = AccelProbeStatus fallback
   - Expected: st.code equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = AccelProbeStatus.fallback("using cpu")
expect(st.code).to_equal("fallback")
```

</details>

#### AccelProbeResult

#### create returns a result with empty device and none shader format

1. var r = AccelProbeResult create
   - Expected: r.device_name equals ``
   - Expected: r.shader_format equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = AccelProbeResult.create("test", AccelProbeStatus.available("ok"))
expect(r.device_name).to_equal("")
expect(r.shader_format).to_equal("none")
```

</details>

#### with_device sets device name and shader format

1. var r = AccelProbeResult with device
   - Expected: r.device_name equals `AMD GPU`
   - Expected: r.shader_format equals `spirv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = AccelProbeResult.with_device("vulkan", AccelProbeStatus.available("ok"), "AMD GPU", "spirv")
expect(r.device_name).to_equal("AMD GPU")
expect(r.shader_format).to_equal("spirv")
```

</details>

#### is_usable reflects status availability

1. var r = AccelProbeResult create
   - Expected: r.is_usable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = AccelProbeResult.create("cpu", AccelProbeStatus.available("ok"))
expect(r.is_usable()).to_equal(true)
```

</details>

#### summary includes backend name and status code

1. var r = AccelProbeResult create
2. var s = r summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = AccelProbeResult.create("cuda", AccelProbeStatus.unavailable("no cuda"))
var s = r.summary()
expect(s).to_contain("cuda")
```

</details>

#### StrictAccelFactory

#### rejects GLSL shader format

1. var fac = StrictAccelFactory permissive
2. var r = AccelProbeResult with device
   - Expected: fac.is_admitted(r) == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fac = StrictAccelFactory.permissive()
var r = AccelProbeResult.with_device("vulkan", AccelProbeStatus.available("ok"), "GPU", "glsl")
expect(fac.is_admitted(r) == false).to_equal(true)
```

</details>

#### admits SPIR-V shader format in permissive mode

1. var fac = StrictAccelFactory permissive
2. var r = AccelProbeResult with device
   - Expected: fac.is_admitted(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fac = StrictAccelFactory.permissive()
var r = AccelProbeResult.with_device("vulkan", AccelProbeStatus.available("ok"), "GPU", "spirv")
expect(fac.is_admitted(r)).to_equal(true)
```

</details>

#### strict mode rejects wrong backend name

1. var fac = StrictAccelFactory create
2. var r = AccelProbeResult with device
   - Expected: fac.is_admitted(r) == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fac = StrictAccelFactory.create("cuda")
var r = AccelProbeResult.with_device("vulkan", AccelProbeStatus.available("ok"), "GPU", "spirv")
expect(fac.is_admitted(r) == false).to_equal(true)
```

</details>

#### rejection reason mentions GLSL for glsl format

1. var fac = StrictAccelFactory permissive
2. var r = AccelProbeResult with device
3. var reason = fac rejection reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fac = StrictAccelFactory.permissive()
var r = AccelProbeResult.with_device("vulkan", AccelProbeStatus.available("ok"), "GPU", "glsl")
var reason = fac.rejection_reason(r)
expect(reason).to_contain("GLSL")
```

</details>

#### VulkanAccelBackend

#### starts uninitialized with invalid pipeline

1. var b = VulkanAccelBackend create
   - Expected: b.initialized == false is true
   - Expected: b.pipeline.is_valid() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanAccelBackend.create(64, 64)
expect(b.initialized == false).to_equal(true)
expect(b.pipeline.is_valid() == false).to_equal(true)
```

</details>

#### init makes backend ready with valid SPIR-V pipeline

1. var b = VulkanAccelBackend create
2. var b2 = b init
   - Expected: b2.is_ready() is true
   - Expected: b2.pipeline.shader_is_spirv() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanAccelBackend.create(32, 32)
var b2 = b.init()
expect(b2.is_ready()).to_equal(true)
expect(b2.pipeline.shader_is_spirv()).to_equal(true)
```

</details>

#### name is vulkan-accel

1. var b = VulkanAccelBackend create
   - Expected: b.name() equals `vulkan-accel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanAccelBackend.create(16, 16)
expect(b.name()).to_equal("vulkan-accel")
```

</details>

#### readback_buf_size equals width times height times 4 after init

1. var b = VulkanAccelBackend create
2. var b2 = b init
   - Expected: b2.readback_buf_size equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanAccelBackend.create(8, 8)
var b2 = b.init()
expect(b2.readback_buf_size).to_equal(256)
```

</details>

#### CudaAccelBackend

#### dispatch_fill returns a dispatch with non-zero grid

1. var b = CudaAccelBackend create
2. var b2 = b init
3. var d = b2 dispatch fill
   - Expected: d.grid_x > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = CudaAccelBackend.create(512, 512)
var b2 = b.init()
var d = b2.dispatch_fill(0xFF0000FF)
expect(d.grid_x > 0).to_equal(true)
```

</details>

#### mark_complete transitions dispatch to completed

1. var b = CudaAccelBackend create
2. var b2 = b init
3. var d = b2 dispatch fill
4. var d2 = d mark complete
   - Expected: d2.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = CudaAccelBackend.create(64, 64)
var b2 = b.init()
var d = b2.dispatch_fill(0)
var d2 = d.mark_complete()
expect(d2.is_complete()).to_equal(true)
```

</details>

#### readback_size equals width times height times 4

1. var b = CudaAccelBackend create
2. var b2 = b init
   - Expected: b2.readback_size() equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = CudaAccelBackend.create(16, 16)
var b2 = b.init()
expect(b2.readback_size()).to_equal(1024)
```

</details>

#### MetalAccelBackend

#### without platform init leaves backend not ready

1. var b = MetalAccelBackend create
2. var b2 = b init
   - Expected: b2.is_ready() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalAccelBackend.create(64, 64)
var b2 = b.init()
expect(b2.is_ready() == false).to_equal(true)
```

</details>

#### with platform enabled init makes backend ready

1. var b = MetalAccelBackend create
2. var b2 = b with platform
3. var b3 = b2 init
   - Expected: b3.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalAccelBackend.create(64, 64)
var b2 = b.with_platform(true)
var b3 = b2.init()
expect(b3.is_ready()).to_equal(true)
```

</details>

#### submit fails when backend not initialized

1. var b = MetalAccelBackend create
2. var cmdbuf = b make command buffer
3. var cmdbuf2 = cmdbuf commit
4. var result = b submit
   - Expected: result.is_ok() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalAccelBackend.create(32, 32)
var cmdbuf = b.make_command_buffer()
var cmdbuf2 = cmdbuf.commit()
var result = b.submit(cmdbuf2)
expect(result.is_ok() == false).to_equal(true)
```

</details>

#### submit succeeds when initialized and command buffer committed

1. var b = MetalAccelBackend create
2. var b2 = b with platform
3. var b3 = b2 init
4. var cmdbuf = b3 make command buffer
5. var cmdbuf2 = cmdbuf commit
6. var result = b3 submit
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalAccelBackend.create(32, 32)
var b2 = b.with_platform(true)
var b3 = b2.init()
var cmdbuf = b3.make_command_buffer()
var cmdbuf2 = cmdbuf.commit()
var result = b3.submit(cmdbuf2)
expect(result.is_ok()).to_equal(true)
```

</details>

#### submit fails when command buffer not committed

1. var b = MetalAccelBackend create
2. var b2 = b with platform
3. var b3 = b2 init
4. var cmdbuf = b3 make command buffer
5. var result = b3 submit
   - Expected: result.is_ok() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalAccelBackend.create(32, 32)
var b2 = b.with_platform(true)
var b3 = b2.init()
var cmdbuf = b3.make_command_buffer()
var result = b3.submit(cmdbuf)
expect(result.is_ok() == false).to_equal(true)
```

</details>

#### pipeline thread_groups_for returns zero when not valid

1. var p = MetalAccelPipeline unavailable
   - Expected: p.thread_groups_for(1024) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = MetalAccelPipeline.unavailable()
expect(p.thread_groups_for(1024)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/graphics_backend_acceleration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- graphics backend acceleration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
