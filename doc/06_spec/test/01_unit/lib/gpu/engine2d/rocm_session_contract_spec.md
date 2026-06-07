# Rocm Session Contract Specification

> <details>

<!-- sdn-diagram:id=rocm_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rocm_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rocm_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rocm_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rocm Session Contract Specification

## Scenarios

### RocmSession compute contract

#### reports ROCm kind and unavailable without an injected HIP FFI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = RocmSession.create()

expect(session.kind() == BackendSessionKind.Rocm).to_equal(true)
expect(session.is_available()).to_equal(false)
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when initializing or launching without HIP FFI

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = RocmSession.create()

expect(session.init()).to_equal(1)
expect(session.load_module("")).to_equal(0)
expect(session.alloc(16)).to_equal(0)
expect(session.read_pixels(1, [], 16)).to_equal(false)
expect(session.synchronize()).to_equal(1)
expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)
```

</details>

#### shutdown is safe on an uninitialized session

1. var session = RocmSession create
2. session shutdown
   - Expected: session.is_valid() is false
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = RocmSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)
```

</details>

#### reports shared generated 2D runtime provenance without HIP FFI

1. var session = RocmSession create
   - Expected: missing_runtime.ready is false
   - Expected: missing_runtime.typed_status equals `hip-runtime-unavailable`
   - Expected: still_missing_runtime.ready is false
   - Expected: still_missing_runtime.typed_status equals `hip-runtime-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = RocmSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_ALPHA, 64, 64, 4096)
session.is_initialized = true
session.module_cache = 11
val still_missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_ALPHA, 64, 64, 4096)

expect(missing_runtime.ready).to_equal(false)
expect(missing_runtime.typed_status).to_equal("hip-runtime-unavailable")
expect(still_missing_runtime.ready).to_equal(false)
expect(still_missing_runtime.typed_status).to_equal("hip-runtime-unavailable")
expect(still_missing_runtime.diagnostic_text()).to_contain("launch=rt_rocm_launch_kernel")
```

</details>

#### reports typed ROCm session evidence for generated module launch and readback gates

1. var session = RocmSession create
   - Expected: init_ev.success is false
   - Expected: init_ev.status_code equals `missing-ffi`
   - Expected: load_ev.success is false
   - Expected: load_ev.reason equals `missing-rocm-ffi`
   - Expected: launch_missing_args.status_code equals `missing-args-pointer`
   - Expected: launch_missing_ffi.status_code equals `missing-ffi`
   - Expected: read_ev.status_code equals `missing-ffi`
   - Expected: matched.success is true
   - Expected: matched.status_code equals `readback-matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = RocmSession.create()
val init_ev = session.init_evidence()
val load_ev = session.load_module_evidence(rocm_2d_generated_source())
val launch_missing_args = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 0)
val launch_missing_ffi = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 4096)
val read_ev = session.read_pixels_evidence(0, [], 0, 1, 1)
val matched = session.readback_evidence(true, 99, 99)

expect(init_ev.success).to_equal(false)
expect(init_ev.status_code).to_equal("missing-ffi")
expect(load_ev.success).to_equal(false)
expect(load_ev.reason).to_equal("missing-rocm-ffi")
expect(launch_missing_args.status_code).to_equal("missing-args-pointer")
expect(launch_missing_ffi.status_code).to_equal("missing-ffi")
expect(read_ev.status_code).to_equal("missing-ffi")
expect(matched.success).to_equal(true)
expect(matched.status_code).to_equal("readback-matched")
```

</details>

#### validates generated glyph packed args before ROCm launch

1. var session = RocmSession create with ffi
2. rt ptr write i64
3. rt ptr write i64
4. rt ptr write i64
5. rt ptr write i64
6. rt ptr write i64
   - Expected: missing_plan.status_code equals `invalid-args`
   - Expected: missing_plan.reason equals `missing-rocm-glyph-plan`
   - Expected: session.launch_generated_2d(GENERATED_2D_GLYPH, 4, 4, args) equals `1`
7. rt ptr write i64
8. rt ptr write i64
   - Expected: missing_dst.reason equals `missing-rocm-glyph-dst`
9. rt ptr write i64
10. rt ptr write i64
   - Expected: bad_dims.reason equals `rocm-glyph-dimensions-mismatch`
11. rt ptr write i64
12. rt ptr write i64
   - Expected: bad_font.reason equals `invalid-rocm-glyph-font-size`
13. rt free


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = RocmSession.create_with_ffi(RocmFfi.create_static())
session.is_initialized = true
session.module_cache = 11
val args = rt_alloc(40)
rt_ptr_write_i64(args, 0, 0)
rt_ptr_write_i64(args, 8, 1234)
rt_ptr_write_i64(args, 16, 4)
rt_ptr_write_i64(args, 24, 4)
rt_ptr_write_i64(args, 32, 16)

val missing_plan = session.launch_generated_2d_evidence(GENERATED_2D_GLYPH, 4, 4, args)
expect(missing_plan.status_code).to_equal("invalid-args")
expect(missing_plan.reason).to_equal("missing-rocm-glyph-plan")
expect(session.launch_generated_2d(GENERATED_2D_GLYPH, 4, 4, args)).to_equal(1)

rt_ptr_write_i64(args, 0, 4321)
rt_ptr_write_i64(args, 8, 0)
val missing_dst = session.launch_generated_2d_evidence(GENERATED_2D_GLYPH, 4, 4, args)
expect(missing_dst.reason).to_equal("missing-rocm-glyph-dst")

rt_ptr_write_i64(args, 8, 1234)
rt_ptr_write_i64(args, 16, 5)
val bad_dims = session.launch_generated_2d_evidence(GENERATED_2D_GLYPH, 4, 4, args)
expect(bad_dims.reason).to_equal("rocm-glyph-dimensions-mismatch")

rt_ptr_write_i64(args, 16, 4)
rt_ptr_write_i64(args, 32, 0)
val bad_font = session.launch_generated_2d_evidence(GENERATED_2D_GLYPH, 4, 4, args)
expect(bad_font.reason).to_equal("invalid-rocm-glyph-font-size")

rt_free(args, 40)
```

</details>

#### static HIP FFI exposes runtime-backed init evidence without missing FFI

1. var session = RocmSession create with ffi
   - Expected: init_ev.reason == "missing-rocm-ffi" is false
   - Expected: init_ev.status_code == "initialized" or init_ev.status_code == "runtime-unavailable" or init_ev.status_code == "device-unavailable" or init_ev.status_code == "init-failed" is true
2. session shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = RocmSession.create_with_ffi(RocmFfi.create_static())
val init_ev = session.init_evidence()

expect(init_ev.reason == "missing-rocm-ffi").to_equal(false)
expect(init_ev.status_code == "initialized" or init_ev.status_code == "runtime-unavailable" or init_ev.status_code == "device-unavailable" or init_ev.status_code == "init-failed").to_equal(true)
session.shutdown()
```

</details>

#### exports the HIP nonzero image blit kernel for transparent text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _engine2d_hip_source()

expect(source).to_contain("kernel_blit_image_nonzero")
expect(source).to_contain("if (pixel == 0) return")
```

</details>

#### exports shared generated HIP kernels with CUDA and OpenCL entry names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rocm_2d_generated_source()

expect(source).to_contain("simple_2d_fill_u32")
expect(source).to_contain("simple_2d_copy_u32")
expect(source).to_contain("simple_2d_alpha_u32")
expect(source).to_contain("simple_2d_scroll_u32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RocmSession compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
