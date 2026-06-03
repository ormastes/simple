# Ffi Opencl Specification

## Scenarios

### OpenClFfi

#### exposes a static generic ICD wrapper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.mode() == GpuFfiMode.Static).to_equal(true)
```

</details>

#### fails closed instead of dispatching a name-only OpenCL kernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.launch_kernel("simple_2d_fill_u32", 1, 1, 1, 1, 1, 1)).to_equal(false)
```

</details>

#### fails closed when creating a queue from an invalid OpenCL context

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.create_queue(0)).to_equal(0)
```

</details>

#### fails closed when creating and building a program from an invalid context

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.create_kernel(0, "simple_2d_fill_u32")).to_equal(0)
```

</details>

#### fails closed when enqueueing and finishing invalid OpenCL handles

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi = OpenClFfi.create_static()
expect(ffi.enqueue_ndrange(0, 0, 1, 1, 1, 1, 1, 1)).to_equal(false)
expect(ffi.finish(0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/ffi_opencl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenClFfi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
