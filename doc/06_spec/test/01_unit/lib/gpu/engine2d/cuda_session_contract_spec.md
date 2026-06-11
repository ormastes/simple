# Cuda Session Contract Specification

> <details>

<!-- sdn-diagram:id=cuda_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Session Contract Specification

## Scenarios

### CudaSession compute contract

#### reports CUDA kind and availability without initializing hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = CudaSession.create()

expect(session.kind() == BackendSessionKind.Cuda).to_equal(true)
expect(session.is_available()).to_equal(cuda_available())
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when launching without a loaded module

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = CudaSession.create()

expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 4096)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)
```

</details>

#### fails generated 2D launches closed for invalid argument buffers

- var session = CudaSession create
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0) equals `1`
   - Expected: session.fill_kernel(64, 64, 0) equals `1`
   - Expected: session.fill_kernel(0, 64, 4096) equals `1`
   - Expected: session.launch_generated_2d("unsupported", 64, 64, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()
session.module_cache = 1234

expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0)).to_equal(1)
expect(session.fill_kernel(64, 64, 0)).to_equal(1)
expect(session.fill_kernel(0, 64, 4096)).to_equal(1)
expect(session.launch_generated_2d("unsupported", 64, 64, 4096)).to_equal(1)
```

</details>

#### supports injected CUDA FFI for the shared backend interface

- var session = CudaSession create with ffi
   - Expected: session.kind() == BackendSessionKind.Cuda is true
   - Expected: session.alloc(0) equals `0`
   - Expected: session.launch_kernel("kernel_clear", 1, 1, 1, 1) equals `1`
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0) equals `1`
   - Expected: session.synchronize() equals `1`
- session shutdown
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create_with_ffi(CudaFfi.create_static())

expect(session.kind() == BackendSessionKind.Cuda).to_equal(true)
expect(session.alloc(0)).to_equal(0)
expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0)).to_equal(1)
expect(session.synchronize()).to_equal(1)
session.shutdown()
expect(session.ref_count).to_equal(0)
```

</details>

#### reports shared generated 2D runtime provenance without hardware

- var session = CudaSession create
   - Expected: missing_runtime.ready is false
   - Expected: missing_runtime.typed_status equals `cuda-runtime-unavailable`
   - Expected: missing_module.typed_status equals `cuda-module-unavailable`
   - Expected: missing_args.typed_status equals `args-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 64, 64, 4096)
session.is_initialized = true
session.ctx = 7
val missing_module = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 64, 64, 4096)
session.module_cache = 11
val missing_args = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 64, 64, 0)

expect(missing_runtime.ready).to_equal(false)
expect(missing_runtime.typed_status).to_equal("cuda-runtime-unavailable")
expect(missing_module.typed_status).to_equal("cuda-module-unavailable")
expect(missing_args.typed_status).to_equal("args-unavailable")
expect(missing_args.diagnostic_text()).to_contain("launch=rt_cuda_launch_kernel")
```

</details>

#### reports typed CUDA launch evidence through the shared gate classifier

- var session = CudaSession create
   - Expected: missing_runtime.success is false
   - Expected: missing_runtime.status_code equals `runtime-not-ready`
   - Expected: missing_runtime.reason equals `cuda-runtime-not-ready`
   - Expected: missing_module.status_code equals `missing-module`
   - Expected: missing_module.reason equals `missing-cuda-generated-module`
   - Expected: missing_args.status_code equals `missing-args-pointer`
   - Expected: missing_args.reason equals `missing-generated-2d-args-pointer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()
val missing_runtime = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 4096)
session.is_initialized = true
session.ctx = 7
val missing_module = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 4096)
session.module_cache = 11
val missing_args = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 0)

expect(missing_runtime.success).to_equal(false)
expect(missing_runtime.status_code).to_equal("runtime-not-ready")
expect(missing_runtime.reason).to_equal("cuda-runtime-not-ready")
expect(missing_module.status_code).to_equal("missing-module")
expect(missing_module.reason).to_equal("missing-cuda-generated-module")
expect(missing_args.status_code).to_equal("missing-args-pointer")
expect(missing_args.reason).to_equal("missing-generated-2d-args-pointer")
expect(missing_args.diagnostic_text()).to_contain("CudaSessionEvidence")
```

</details>

#### routes generated bitmap glyph raster through the CUDA session helper

- var session = CudaSession create
   - Expected: missing_runtime.operation equals `GENERATED_2D_BITMAP_GLYPH_RASTER`
   - Expected: missing_runtime.entry_name equals `simple_2d_bitmap_glyph_raster_u32`
   - Expected: missing_runtime.typed_status equals `cuda-runtime-unavailable`
   - Expected: missing_module.typed_status equals `cuda-module-unavailable`
   - Expected: missing_args.typed_status equals `args-unavailable`
   - Expected: session.bitmap_glyph_raster_kernel(9, 4, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 4096)
session.is_initialized = true
session.ctx = 7
val missing_module = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 4096)
session.module_cache = 11
val missing_args = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 0)

expect(missing_runtime.operation).to_equal(GENERATED_2D_BITMAP_GLYPH_RASTER)
expect(missing_runtime.entry_name).to_equal("simple_2d_bitmap_glyph_raster_u32")
expect(missing_runtime.typed_status).to_equal("cuda-runtime-unavailable")
expect(missing_module.typed_status).to_equal("cuda-module-unavailable")
expect(missing_args.typed_status).to_equal("args-unavailable")
expect(missing_args.diagnostic_text()).to_contain("op=bitmap_glyph_raster")
session.module_cache = 0
expect(session.bitmap_glyph_raster_kernel(9, 4, 4096)).to_equal(1)
```

</details>

#### reports CUDA readback evidence through the shared checksum classifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = CudaSession.create()
val matched = session.readback_evidence(true, 1234, 1234)
val unavailable = session.readback_evidence(false, 1234, 1234)
val mismatch = session.readback_evidence(true, 1234, 999)
val invalid = session.readback_evidence(true, 0, 1234)

expect(matched.success).to_equal(true)
expect(matched.status_code).to_equal("readback-matched")
expect(matched.reason).to_equal("readback-checksum-matched")
expect(matched.readback_available).to_equal(true)
expect(unavailable.success).to_equal(false)
expect(unavailable.status_code).to_equal("readback-unavailable")
expect(unavailable.reason).to_equal("device-readback-required")
expect(mismatch.status_code).to_equal("readback-mismatch")
expect(mismatch.reason).to_equal("device-readback-checksum-mismatch")
expect(invalid.status_code).to_equal("invalid-checksum")
expect(invalid.reason).to_equal("device-readback-checksum-required")
expect(matched.diagnostic_text()).to_contain("op=readback")
```

</details>

#### shutdown is safe on an uninitialized session

- var session = CudaSession create
- session shutdown
   - Expected: session.is_valid() is false
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CudaSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CudaSession compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
