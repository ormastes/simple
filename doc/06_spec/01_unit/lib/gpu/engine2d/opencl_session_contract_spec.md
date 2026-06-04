# Opencl Session Contract Specification

> <details>

<!-- sdn-diagram:id=opencl_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opencl_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opencl_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opencl_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencl Session Contract Specification

## Scenarios

### OpenClSession compute contract

#### reports OpenCL kind and unavailable without an injected ICD FFI

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

expect(session.kind() == BackendSessionKind.OpenCl).to_equal(true)
expect(session.is_available()).to_equal(false)
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when initializing or launching without OpenCL FFI

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

expect(session.init()).to_equal(1)
expect(session.load_module("")).to_equal(0)
expect(session.alloc(16)).to_equal(0)
expect(session.write_buffer(1, 1, 16)).to_equal(false)
expect(session.read_buffer(1, 1, 16)).to_equal(false)
expect(session.set_kernel_arg_i64(1, 0, 1)).to_equal(false)
expect(session.set_kernel_arg_buffer(1, 0, 1)).to_equal(false)
expect(session.synchronize()).to_equal(1)
expect(session.launch_kernel("simple_2d_fill_u32", 1, 1, 1, 1)).to_equal(1)
expect(session.launch_fill_u32(1, 4, 4, 0xff112233 as i64)).to_equal(1)
expect(session.launch_rect_filled_u32(1, 4, 4, 1, 1, 2, 2, 0xff445566 as i64)).to_equal(1)
expect(session.launch_rect_outline_u32(1, 4, 4, 0, 0, 4, 4, 0xff778899 as i64)).to_equal(1)
expect(session.launch_line_u32(1, 4, 4, 0, 0, 3, 3, 0xff778899 as i64, 1)).to_equal(1)
expect(session.launch_gradient_rect_u32(1, 4, 4, 0, 0, 4, 4, 0xffff0000 as i64, 0xff0000ff as i64)).to_equal(1)
expect(session.launch_circle_u32(1, 4, 4, 1, 1, 1, 0xffabcdef as i64, false)).to_equal(1)
expect(session.launch_circle_u32(1, 4, 4, 2, 2, 1, 0xff135724 as i64, true)).to_equal(1)
expect(session.launch_rounded_rect_u32(1, 4, 4, 0, 0, 4, 4, 1, 0xff2468ac as i64)).to_equal(1)
expect(session.launch_triangle_filled_u32(1, 4, 4, 0, 0, 3, 0, 0, 3, 0xff55aa11 as i64)).to_equal(1)
expect(session.launch_blit_image_u32(1, 2, 0, 0, 4, 4, 8, 8)).to_equal(1)
expect(session.launch_blit_nonzero_u32(1, 2, 0, 0, 4, 4, 8, 8)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)
```

</details>

#### shutdown is safe on an uninitialized session

1. var session = OpenClSession create

2. session shutdown
   - Expected: session.is_valid() is false
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)
```

</details>

#### retains and releases shared OpenCL sessions like CUDA sessions

1. var session = OpenClSession create
   - Expected: retained.ref_count equals `2`
   - Expected: session.is_valid() is true

2. session release
   - Expected: session.ref_count equals `1`
   - Expected: session.context equals `2`
   - Expected: session.queue equals `3`

3. session release
   - Expected: session.ref_count equals `0`
   - Expected: session.is_valid() is false
   - Expected: session.platform equals `0`
   - Expected: session.context equals `0`
   - Expected: session.queue equals `0`
   - Expected: session.program equals `0`
   - Expected: session.kernel_cache equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create()
session.platform = 1
session.context = 2
session.queue = 3
session.program = 4
session.kernel_cache = 5
session.is_initialized = true
session.ref_count = 1
val generation_before = session.generation

val retained = session.retain()
expect(retained.ref_count).to_equal(2)
expect(session.is_valid()).to_equal(true)

session.release()
expect(session.ref_count).to_equal(1)
expect(session.context).to_equal(2)
expect(session.queue).to_equal(3)

session.release()
expect(session.ref_count).to_equal(0)
expect(session.is_valid()).to_equal(false)
expect(session.platform).to_equal(0)
expect(session.context).to_equal(0)
expect(session.queue).to_equal(0)
expect(session.program).to_equal(0)
expect(session.kernel_cache).to_equal(0)
```

</details>

#### fails closed for OpenCL session buffer and kernel argument operations without valid handles

1. var session = OpenClSession create with ffi
   - Expected: session.alloc(16) equals `0`
   - Expected: session.write_buffer(1, 1, 16) is false
   - Expected: session.read_buffer(1, 1, 16) is false
   - Expected: session.set_kernel_arg_i64(1, 0, 1) is false
   - Expected: session.set_kernel_arg_buffer(1, 0, 1) is false
   - Expected: session.alloc(0) equals `0`
   - Expected: session.alloc(16) equals `0`
   - Expected: session.write_buffer(1, 1, 16) is false
   - Expected: session.read_buffer(1, 1, 16) is false
   - Expected: session.set_kernel_arg_i64(1, -1, 1) is false
   - Expected: session.set_kernel_arg_buffer(1, 0, 0) is false
   - Expected: session.launch_fill_u32(0, 4, 4, 1) equals `1`
   - Expected: session.launch_fill_u32(1, 0, 4, 1) equals `1`
   - Expected: session.launch_rect_filled_u32(0, 4, 4, 1, 1, 2, 2, 1) equals `1`
   - Expected: session.launch_rect_filled_u32(1, 4, 4, 1, 1, 0, 2, 1) equals `1`
   - Expected: session.launch_rect_outline_u32(1, 4, 4, 1, 1, 2, 0, 1) equals `1`
   - Expected: session.launch_line_u32(0, 4, 4, 0, 0, 3, 3, 1, 1) equals `1`
   - Expected: session.launch_line_u32(1, 0, 4, 0, 0, 3, 3, 1, 1) equals `1`
   - Expected: session.launch_line_u32(1, 4, 4, 0, 0, 3, 3, 1, 0) equals `1`
   - Expected: session.launch_gradient_rect_u32(0, 4, 4, 0, 0, 4, 4, 1, 2) equals `1`
   - Expected: session.launch_gradient_rect_u32(1, 0, 4, 0, 0, 4, 4, 1, 2) equals `1`
   - Expected: session.launch_gradient_rect_u32(1, 4, 4, 0, 0, 0, 4, 1, 2) equals `1`
   - Expected: session.launch_circle_u32(0, 4, 4, 1, 1, 1, 1, false) equals `1`
   - Expected: session.launch_circle_u32(1, 0, 4, 1, 1, 1, 1, false) equals `1`
   - Expected: session.launch_circle_u32(1, 4, 4, 1, 1, 0, 1, true) equals `1`
   - Expected: session.launch_rounded_rect_u32(0, 4, 4, 0, 0, 4, 4, 1, 1) equals `1`
   - Expected: session.launch_rounded_rect_u32(1, 0, 4, 0, 0, 4, 4, 1, 1) equals `1`
   - Expected: session.launch_rounded_rect_u32(1, 4, 4, 0, 0, 0, 4, 1, 1) equals `1`
   - Expected: session.launch_rounded_rect_u32(1, 4, 4, 0, 0, 4, 4, -1, 1) equals `1`
   - Expected: session.launch_triangle_filled_u32(0, 4, 4, 0, 0, 3, 0, 0, 3, 1) equals `1`
   - Expected: session.launch_triangle_filled_u32(1, 0, 4, 0, 0, 3, 0, 0, 3, 1) equals `1`
   - Expected: session.launch_blit_image_u32(0, 2, 0, 0, 4, 4, 8, 8) equals `1`
   - Expected: session.launch_blit_image_u32(1, 0, 0, 0, 4, 4, 8, 8) equals `1`
   - Expected: session.launch_blit_image_u32(1, 2, 0, 0, 0, 4, 8, 8) equals `1`
   - Expected: session.launch_blit_nonzero_u32(1, 2, 0, 0, 4, 0, 8, 8) equals `1`
   - Expected: session.generation equals `generation_before`


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create_with_ffi(OpenClFfi.create_static())
val generation_before = session.generation
expect(session.alloc(16)).to_equal(0)
expect(session.write_buffer(1, 1, 16)).to_equal(false)
expect(session.read_buffer(1, 1, 16)).to_equal(false)
expect(session.set_kernel_arg_i64(1, 0, 1)).to_equal(false)
expect(session.set_kernel_arg_buffer(1, 0, 1)).to_equal(false)

session.context = 1
session.queue = 2
expect(session.alloc(0)).to_equal(0)
expect(session.alloc(16)).to_equal(0)
expect(session.write_buffer(1, 1, 16)).to_equal(false)
expect(session.read_buffer(1, 1, 16)).to_equal(false)
expect(session.set_kernel_arg_i64(1, -1, 1)).to_equal(false)
expect(session.set_kernel_arg_buffer(1, 0, 0)).to_equal(false)
expect(session.launch_fill_u32(0, 4, 4, 1)).to_equal(1)
expect(session.launch_fill_u32(1, 0, 4, 1)).to_equal(1)
expect(session.launch_rect_filled_u32(0, 4, 4, 1, 1, 2, 2, 1)).to_equal(1)
expect(session.launch_rect_filled_u32(1, 4, 4, 1, 1, 0, 2, 1)).to_equal(1)
expect(session.launch_rect_outline_u32(1, 4, 4, 1, 1, 2, 0, 1)).to_equal(1)
expect(session.launch_line_u32(0, 4, 4, 0, 0, 3, 3, 1, 1)).to_equal(1)
expect(session.launch_line_u32(1, 0, 4, 0, 0, 3, 3, 1, 1)).to_equal(1)
expect(session.launch_line_u32(1, 4, 4, 0, 0, 3, 3, 1, 0)).to_equal(1)
expect(session.launch_gradient_rect_u32(0, 4, 4, 0, 0, 4, 4, 1, 2)).to_equal(1)
expect(session.launch_gradient_rect_u32(1, 0, 4, 0, 0, 4, 4, 1, 2)).to_equal(1)
expect(session.launch_gradient_rect_u32(1, 4, 4, 0, 0, 0, 4, 1, 2)).to_equal(1)
expect(session.launch_circle_u32(0, 4, 4, 1, 1, 1, 1, false)).to_equal(1)
expect(session.launch_circle_u32(1, 0, 4, 1, 1, 1, 1, false)).to_equal(1)
expect(session.launch_circle_u32(1, 4, 4, 1, 1, 0, 1, true)).to_equal(1)
expect(session.launch_rounded_rect_u32(0, 4, 4, 0, 0, 4, 4, 1, 1)).to_equal(1)
expect(session.launch_rounded_rect_u32(1, 0, 4, 0, 0, 4, 4, 1, 1)).to_equal(1)
expect(session.launch_rounded_rect_u32(1, 4, 4, 0, 0, 0, 4, 1, 1)).to_equal(1)
expect(session.launch_rounded_rect_u32(1, 4, 4, 0, 0, 4, 4, -1, 1)).to_equal(1)
expect(session.launch_triangle_filled_u32(0, 4, 4, 0, 0, 3, 0, 0, 3, 1)).to_equal(1)
expect(session.launch_triangle_filled_u32(1, 0, 4, 0, 0, 3, 0, 0, 3, 1)).to_equal(1)
expect(session.launch_blit_image_u32(0, 2, 0, 0, 4, 4, 8, 8)).to_equal(1)
expect(session.launch_blit_image_u32(1, 0, 0, 0, 4, 4, 8, 8)).to_equal(1)
expect(session.launch_blit_image_u32(1, 2, 0, 0, 0, 4, 8, 8)).to_equal(1)
expect(session.launch_blit_nonzero_u32(1, 2, 0, 0, 4, 0, 8, 8)).to_equal(1)
expect(session.generation).to_equal(generation_before)
```

</details>

#### validates generated fill packed args before submitting OpenCL work

1. var session = OpenClSession create with ffi

2. rt ptr write i64

3. rt ptr write i64

4. rt ptr write i64

5. rt ptr write i64
   - Expected: session.fill_kernel(8, 4, args) equals `1`
   - Expected: missing_args.success is false
   - Expected: missing_args.reason equals `missing-generated-2d-args-pointer`

6. rt free


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create_with_ffi(OpenClFfi.create_static())
session.queue = 1
session.program = 2
val args = rt_alloc(32)
rt_ptr_write_i64(args, 0, 1234)
rt_ptr_write_i64(args, 8, 4)
rt_ptr_write_i64(args, 16, 4)
rt_ptr_write_i64(args, 24, 0xff112233 as i64)

expect(session.fill_kernel(8, 4, args)).to_equal(1)
val missing_args = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 4, 4, 0)
expect(missing_args.success).to_equal(false)
expect(missing_args.reason).to_equal("missing-generated-2d-args-pointer")

rt_free(args, 32)
```

</details>

#### reports shared generated 2D runtime provenance as typed OpenCL unavailable states

1. var session = OpenClSession create
   - Expected: missing_runtime.ready is false
   - Expected: missing_runtime.typed_status equals `opencl-runtime-or-queue-unavailable`
   - Expected: missing_program.typed_status equals `opencl-runtime-or-queue-unavailable`
   - Expected: missing_args.typed_status equals `opencl-runtime-or-queue-unavailable`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 4, 4, 4096)
session.queue = 3
val missing_program = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 4, 4, 4096)
session.program = 5
val missing_args = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 4, 4, 0)

expect(missing_runtime.ready).to_equal(false)
expect(missing_runtime.typed_status).to_equal("opencl-runtime-or-queue-unavailable")
expect(missing_program.typed_status).to_equal("opencl-runtime-or-queue-unavailable")
expect(missing_args.typed_status).to_equal("opencl-runtime-or-queue-unavailable")
expect(missing_runtime.diagnostic_text()).to_contain("artifact=simple_2d_optimization.spirv")
```

</details>

#### cleans up through injected OpenCL FFI release hooks

1. var session = OpenClSession create with ffi

2. session release
   - Expected: session.ref_count equals `0`
   - Expected: session.is_valid() is false
   - Expected: session.context equals `0`
   - Expected: session.queue equals `0`
   - Expected: session.program equals `0`
   - Expected: session.kernel_cache equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create_with_ffi(OpenClFfi.create_static())
session.platform = 1
session.context = 2
session.queue = 3
session.program = 4
session.kernel_cache = 5
session.is_initialized = true
session.ref_count = 1

session.release()

expect(session.ref_count).to_equal(0)
expect(session.is_valid()).to_equal(false)
expect(session.context).to_equal(0)
expect(session.queue).to_equal(0)
expect(session.program).to_equal(0)
expect(session.kernel_cache).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/opencl_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenClSession compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
