# Frozen Phase2 GPU loader ABI partition v1

Baseline: `e6ffda6849e6aa7fe01a7d23ddc71e9773286532`.
Merge owner: `/root/stage2_after_backend_receiver`.
Source tree: `/Users/ormastes/simple-tmp/phase2-runner-gpu-provider-20260923`.
Final reviewer: independent Astra-high assigned by root after integration.

The runner linker reports its first 20 missing CUDA/Vulkan symbols. An `nm`
census against its retained `libspl_objects.a`, selected core runtime, and this
lane's initial corrected loader exposes 58 more. This partition covers exactly
78 originally distinct symbols plus the composition-induced checksum export
below (79 total). It does not imply their callers, GPU hardware, Phase2 or
the full runner have passed. Required symbols already present in the old
loader (init/allocation/dtoh) are included among the reported20 because that
build did not link the loader at all.

## Shared rules and interfaces — frozen before sidecars

- Main owns Rust host-gpu composition, `runtime_dynload.c`, its existing macros
  `GPU_CALL0` through `GPU_CALL4`, `SimpleGpuCallPinV1`,
  `simple_gpu_call_acquire_v1(bit,name,&pin)`,
  `simple_gpu_call_release_v1(&pin)`, and
  `simple_gpu_array_to_bytes(int64_t,uint8_t **,int64_t *)`.
  Sidecars MUST NOT modify these helpers, registry admission or required lists.
- Main additionally owns checked integer-array transfers in runtime_native.c:
  `rt_array_i64_validate(int64_t value)->int64_t length/-22` and
  `rt_array_i64_copy_checked(int64_t value,int64_t *out,int64_t capacity)`.
  Copy returns length/-22, never partially writes on validation/capacity failure;
  accepts registered tagged-integer arrays, rejects byte/u64/tuple storage.
  A/P sidecars may use these functions for region records without header casts.
- Every provider call acquires/releases its existing lease; no registry lock
  is held over provider code. No global-symbol fallback, stub generation,
  success-on-unavailable or directly linked CUDA/Vulkan implementations.
- Sidecars each create ONE private implementation include under `src/runtime`
  as named below. Main will include them after the existing array helper.
  Those include fragments use only the shared interfaces above. No cross-lane
  helper dependency: scalar uses prefix `simple_gpu_scalar_`, arrays uses
  `simple_gpu_readback_`, pipeline uses `simple_gpu_pipeline_` for private
  helpers. Duplication may be consolidated by main after reviewed evidence.
- `i` means signed64 C scalar; `u` unsigned64; `p` byte pointer; `cstr` NUL
  string pointer; `v` is one core-C native value word (array/text). Public `v`
  values MUST NOT be forwarded into a Rust provider's boxed RuntimeValue ABI.
  Decode/pack to a pinned raw pointer/length call and construct core-C output.
- CUDA module_get_function is a critical exception: Simple declares text but
  it is absent from native text-span expansion registries. Public signature
  is `(i,v)->i`; decode via `rt_string_data/rt_string_len`, reject interior NUL,
  pass a bounded temporary C string to provider `(i,cstr)->i`. The former
  direct-C-string forward is invalid. Native Simple-boundary proof required.
- CUDA module_load/module_load_data and launch_kernel ARE explicit text-span
  expansion owners: their public C ABI is pointer+length as shown below.
- Returned provider C strings must be copied while the lease is live; never
  return borrowed provider memory after release. Preserve documented empty or
  descriptive unavailable values. Test post-unload use.
- Array/output size products/sums must be checked before allocations; bound
  transfers using provider's existing limits, free every temporary on every
  path, leave destination unchanged on failure, preserve valid empty behavior.
- Synthetic provider checks must validate argument values/bytes/order and
  negative/mutated inputs. C-only literal fixtures do not prove Simple text or
  array representation; include a focused native Simple-boundary regression.
- Each sidecar works isolated from baseline, no full runner/bootstrap/push,
  max3 fix/verify cycles. Share host for short probes only; coordinate heavier
  compiles. Use LLVM23 pins and sampled RSS cap5859375KiB. Independent review
  must distinguish synthetic ABI proof from GPU/device evidence.

## Main — first20 plus CUDA9 (29)

| Symbol | Public C signature | Unavailable | Provider boundary |
|---|---|---|---|
| rt_cuda_init | ()->i | 3 (existing ABI) | same |
| rt_cuda_device_get | (i)->i | -3 | same |
| rt_cuda_ctx_create | (i)->i | -3 | same |
| rt_cuda_ctx_destroy | (i)->i | -3 | same |
| rt_cuda_mem_alloc | (i)->i | -3 | same |
| rt_cuda_mem_free | (i)->i | -3 | same |
| rt_cuda_memcpy_dtoh | (i,i,i)->i | -3 | same |
| rt_cuda_module_load_data_array | (v)->i | -3; invalid -1 | module_load_data_bytes(ptr,len) |
| rt_cuda_module_unload | (i)->i | -3 | same |
| rt_cuda_module_get_function | (i,v)->i | -3; invalid -1 | same name (i,cstr) |
| rt_cuda_launch_kernel | (i,p,u,i,i,i,i,i,i,i)->i | -3; invalid -1 | launch_kernel_name ten i64 args |
| rt_cuda_launch_kernel_name_array | (i,v,i,i,i,i,i,i,i)->i | -3; invalid -1 | launch_kernel_name ten i64 args |
| rt_cuda_sync | ()->i | -3 | same |
| rt_cuda_memcpy_htod_array | (i,v,i)->i | -3; invalid -1 | memcpy_htod(dst,ptr,count) |
| rt_cuda_device_identity | (i)->i | 0 | same optional provider operation |
| rt_cuda_device_name | (i)->cstr | No CUDA | same; copy before release |
| rt_vulkan_copy_to_buffer | (i,v,i)->i | 0 | copy_to_buffer_raw(handle,ptr,len,offset) |
| rt_vulkan_copy_to_buffer_array | (i,v,i,i)->i | 0 | copy_to_buffer_raw(handle,ptr,count,offset) |
| rt_vulkan_compile_spirv | (v)->i | 0 | compile_spirv_raw(ptr,len) |
| rt_vulkan_compile_spirv_array | (v)->i | 0 | compile_spirv_raw(ptr,len) |
| rt_cuda_ctx_set_current | (i)->i | -3 | same |
| rt_cuda_ctx_synchronize | ()->i | -3 | same |
| rt_cuda_device_compute_capability | (i)->i | 0 | same |
| rt_cuda_get_error_string | (i)->cstr | canonical static CUDA_ERROR_* code mapping | same; copy before release |
| rt_cuda_memcpy_dtod | (i,i,i)->i | -3 | same |
| rt_cuda_memcpy_htod | (i,i,i)->i | -3 | same |
| rt_cuda_memset | (i,i,i)->i | -3 | same |
| rt_cuda_module_load | (p,u)->i | -3 | same optional provider operation |
| rt_cuda_module_load_data | (p,u)->i | -3 | module_load_data_bytes(ptr,len) |

## Sidecar S — Vulkan scalar/text (29)

Own `src/runtime/runtime_gpu_vulkan_scalar_private.h` and uniquely named
`phase2_gpu_vulkan_scalar` fixtures/checker/docs. Scalar outputs below return
0 when absent unless specified. Text outputs copy before releasing the pin.
Canonical sources: `vulkan_graphics_runtime_{core,device,compute,sync,buffer,shader}.rs`.

| Symbol | Public C signature | Unavailable |
|---|---|---|
| rt_vulkan_accepted_compute_submit_count | ()->i | 0 |
| rt_vulkan_begin_compute | ()->i | 0 |
| rt_vulkan_bind_buffer | (i,i,i)->i | 0 |
| rt_vulkan_bind_descriptors | (i,i)->i | 0 |
| rt_vulkan_bind_pipeline | (i,i)->i | 0 |
| rt_vulkan_create_descriptor_set | (i)->i | 0 |
| rt_vulkan_destroy_descriptor_set | (i)->i | 0 |
| rt_vulkan_destroy_fence | (i)->i | 0 |
| rt_vulkan_destroy_pipeline | (i)->i | 0 |
| rt_vulkan_destroy_shader | (i)->i | 0 |
| rt_vulkan_device_driver_identity | (i)->cstr | empty string |
| rt_vulkan_device_name | (i)->cstr | empty string |
| rt_vulkan_device_type | (i)->cstr | empty string |
| rt_vulkan_discard_command | (i)->i | 0 |
| rt_vulkan_dispatch | (i,i,i,i)->i | 0 |
| rt_vulkan_end_compute | (i)->i | 0 |
| rt_vulkan_fence_submission_supported | ()->i | 0 |
| rt_vulkan_free_buffer | (i)->i | 0 |
| rt_vulkan_get_last_error | ()->cstr | descriptive provider-unavailable error |
| rt_vulkan_select_device | (i)->i | 0 |
| rt_vulkan_selected_device_driver_identity | ()->cstr | empty string |
| rt_vulkan_selected_device_driver_identity_hash | ()->i | 0 |
| rt_vulkan_selected_device_type | ()->cstr | empty string |
| rt_vulkan_shutdown | ()->i | 0 |
| rt_vulkan_submit_and_wait | (i)->i | 0 |
| rt_vulkan_submit_and_wait_fence | (i)->i | 0 |
| rt_vulkan_submit_no_wait | (i)->i | 0 |
| rt_vulkan_wait_fence | (i,i)->i | 0 |
| rt_vulkan_wait_idle | ()->i | 0 |

Most provider names match public names. `submit_and_wait` may route through
the canonical required `submit_and_wait_fence` surface only if return and
lifetime behavior are proven equivalent; otherwise forward its optional name.

## Sidecar A — Vulkan arrays/readback (8)

Own `src/runtime/runtime_gpu_vulkan_readback_private.h` and uniquely named
`phase2_gpu_vulkan_readback` fixtures/checker/docs. Canonical source:
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs`.

| Symbol | Public C signature | Unavailable | Raw provider boundary |
|---|---|---|---|
| rt_vulkan_copy_from_buffer_array | (v,i,i,i)->i | 0 | copy_from_buffer_raw |
| rt_vulkan_copy_from_buffer_regions | (v,i,v)->i | 0 | copy_from_buffer_regions_raw |
| rt_vulkan_copy_from_buffer_strided | (v,i,i,i,i,i)->i | 0 | copy_from_buffer_strided_raw |
| rt_vulkan_copy_to_buffer_u32 | (i,v,i)->i | 0 | copy_to_buffer_raw with LE u32 packing |
| rt_vulkan_read_buffer_bytes | (i,i,i)->v | empty core-C byte array | copy_from_buffer_raw |
| rt_vulkan_readback_u32_array | (i,i,i)->v | empty core-C array | copy_from_buffer_raw; LE u32 decoding |
| rt_vulkan_readback_u32_array_checksum | (i,i,i)->i | -1 | same bytes; sum modulo2147483647 |
| rt_vulkan_readback_u32_checksum | (v,i,i,i)->i | -1 | caller-owned core-C integer array,pixel count,handle,offset; checked raw readback, array update and fold |

The eighth row is introduced by selecting `SIMPLE_RUNTIME_DYNLOAD_OWNER`: that
flag removes the original core weak checksum fallback. Its real loader owner
must therefore exist even though the initial old-core census counted it present.

Regions are i64 tuples, not byte arrays; preserve canonical packed LE record
format and required stride/offset/length checks. Empty core-C arrays are real
array values, not bare0 or a Rust RuntimeValue payload. A sidecar may privately
share its own readback helpers; do not modify main's byte helper.

## Sidecar P — Vulkan pipeline/present/push constants (13)

Own `src/runtime/runtime_gpu_vulkan_pipeline_private.h` and uniquely named
`phase2_gpu_vulkan_pipeline` fixtures/checker/docs. Canonical sources:
`vulkan_graphics_runtime_{shader,compute,swapchain}.rs`.

| Symbol | Public C signature | Unavailable | Provider boundary |
|---|---|---|---|
| rt_vulkan_compile_glsl | (v)->i | 0 | canonical operation unsupported; preserve fail-closed result/diagnostic, no Rust-value forwarding |
| rt_vulkan_create_compute_pipeline | (i,v,i)->i | 0 | create_compute_pipeline_raw(shader,entry_ptr,entry_len,push_size) |
| rt_vulkan_create_compute_pipeline_raw | (i,i,i,i)->i | 0 | same |
| rt_vulkan_destroy_swapchain | (i)->i | 0 | same |
| rt_vulkan_init_external_window_present | (i,i,i,i,i,i)->i | 0 | same |
| rt_vulkan_init_headless_present | (i,i,i)->i | 0 | same |
| rt_vulkan_init_window_present | (i,i,i)->i | 0 | same |
| rt_vulkan_last_present_copy_bytes | (i)->i | -1 | same |
| rt_vulkan_last_present_copy_rects | (i)->i | -1 | same |
| rt_vulkan_present_buffer | (i,i,i,i,i)->i | 0 | same |
| rt_vulkan_present_buffer_regions | (i,i,i,i,i,v)->i | 0 | present_buffer_regions_raw(sc,buf,w,h,revision,rects_ptr,rects_len) |
| rt_vulkan_push_constants | (i,i,v)->i | 0 | push_constants_raw(cmd,pipe,ptr,len) |
| rt_vulkan_push_constants_array | (i,i,v,i)->i | 0 | push_constants_raw(cmd,pipe,ptr,count) |

No new GPU implementation is authorized. Unsupported GLSL cannot become fake
success. Entry text must use existing core-C text accessors, bounded length and
NUL rules. Rect arrays use canonical packed LE i64 records; a raw pointer to a
core array or Rust-encoded value is invalid across the provider boundary.

## Merge and validation

Main integrates reviewed fragments and header fingerprint inputs, then runs
one combined focused native link/ABI regression and complete retained-object
GPU-symbol census. Individual sidecars do not rerun unchanged passing gates.
The canonical full runner rebuild remains a separate parent-controlled gate.
No compiler-matrix PASS, physical GPU PASS or Phase3 admission is implied.
