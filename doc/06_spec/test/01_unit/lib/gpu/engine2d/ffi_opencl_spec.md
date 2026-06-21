# Engine2D OpenCL FFI Specification

> Verifies that the static OpenCL FFI wrapper advertises its dispatch mode and fails closed for invalid OpenCL handles instead of pretending to execute GPU work without a valid device context.

<!-- sdn-diagram:id=ffi_opencl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_opencl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_opencl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_opencl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D OpenCL FFI Specification

Verifies that the static OpenCL FFI wrapper advertises its dispatch mode and fails closed for invalid OpenCL handles instead of pretending to execute GPU work without a valid device context.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Reference | `src/lib/gc_async_mut/gpu/engine2d/sffi_opencl.spl` |
| Requirements | N/A |
| Plan | doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md |
| Design | doc/05_design/ui/renderer_unification_2026-06-15.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_opencl_spec.spl` |
| Updated | 2026-06-21 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the static OpenCL FFI wrapper advertises its dispatch mode and
fails closed for invalid OpenCL handles instead of pretending to execute GPU
work without a valid device context.

**Source:** `src/lib/gc_async_mut/gpu/engine2d/sffi_opencl.spl`
**Requirements:** N/A
**Research:** doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md
**Plan:** doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md
**Design:** doc/05_design/ui/renderer_unification_2026-06-15.md

## Syntax

Use `OpenClFfi.create_static()` for strict static-dispatch checks. Invalid
contexts, queues, programs, kernels, buffers, and kernel arguments must return
false or zero handles.

## Examples

The scenarios cover mode reporting, kernel launch rejection, invalid resource
creation, invalid enqueue/finish calls, release calls, buffer operations, and
kernel argument binding.

## Scenarios

### OpenClFfi

#### exposes a static generic ICD wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.mode() == GpuFfiMode.Static).to_equal(true)
```

</details>

#### fails closed instead of dispatching a name-only OpenCL kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.launch_kernel("simple_2d_fill_u32", 1, 1, 1, 1, 1, 1)).to_equal(false)
```

</details>

#### fails closed when creating a queue from an invalid OpenCL context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.create_queue(0)).to_equal(0)
```

</details>

#### fails closed when creating and building a program from an invalid context

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
val program = ffi.create_program(0, "opencl-source")
expect(program).to_equal(0)
expect(ffi.build_program(program)).to_equal(false)
```

</details>

#### fails closed when creating a kernel from an invalid program

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.create_kernel(0, "simple_2d_fill_u32")).to_equal(0)
```

</details>

#### fails closed when enqueueing and finishing invalid OpenCL handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.enqueue_ndrange(0, 0, 1, 1, 1, 1, 1, 1)).to_equal(false)
expect(ffi.finish(0)).to_equal(false)
```

</details>

#### fails closed when releasing invalid OpenCL handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.release_kernel(0)).to_equal(false)
expect(ffi.release_program(0)).to_equal(false)
expect(ffi.release_queue(0)).to_equal(false)
expect(ffi.release_context(0)).to_equal(false)
```

</details>

#### fails closed for invalid OpenCL buffers and kernel args

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.mem_alloc(0, 16)).to_equal(0)
expect(ffi.mem_alloc(1, 0)).to_equal(0)
expect(ffi.mem_free(0)).to_equal(false)
expect(ffi.write_buffer(0, 0, 0, 16)).to_equal(false)
expect(ffi.read_buffer(0, 0, 0, 16)).to_equal(false)
expect(ffi.set_kernel_arg_i64(0, 0, 1)).to_equal(false)
expect(ffi.set_kernel_arg_buffer(0, 0, 0)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md](doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md)
- **Design:** [doc/05_design/ui/renderer_unification_2026-06-15.md](doc/05_design/ui/renderer_unification_2026-06-15.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md](doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md)


</details>
