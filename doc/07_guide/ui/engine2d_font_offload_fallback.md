# Engine2D font offload fallback

How `Engine2D` decides which backend draws configured text, and what it records
while deciding. Read this before changing backend routing in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` or the preference order in
`src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl`.

## The two mechanisms are separate

Engine2D has **two** distinct routing paths, and conflating them is the usual
source of confusion.

**Primitive/readback routing** is a single five-arm chain, repeated at ~28 call
sites (`clear()` at L1300 is representative):

| Arm | Backend | Readiness guard |
|---|---|---|
| 1 | `virtio_gpu_backend` | none needed |
| 2 | `baremetal_backend` | none needed |
| 3 | `cuda_backend` | gated on `selected_backend_name == "cuda"` |
| 4 | `vulkan_backend` via `_vulkan_primitive_target()` | poison check **and** `.initialized` |
| 5 | `self.backend` | terminal |

`metal_backend`, `opencl_backend`, `rocm_backend` and `software_backend` are
**not in this chain at all** — they reach drawing only through `self.backend`.

**Font offload** (`_draw_font_batch_staged`, L1607-1720) is different: each
candidate target is *tried*, and judged by whether it consumed the batch
(`quad_index == batch.quads.len()`). A target that fails records
`<name>:failed` and the walk continues.

## Why only Vulkan carries an `.initialized` guard

Because Vulkan is the only arm where `self.backend` can diverge from a non-nil
sibling field.

For arms 1 and 2 the create paths (`create_with_virtio_gpu_backend` L824,
`create_with_baremetal_backend` L791) pass the **same object** as both
`backend:` and the sibling field — they cannot disagree. For arm 3, the only
site that sets `selected_backend_name = "cuda"` (L632) is one where
`cuda.init()` already returned true and `backend: cuda` is that same object.

Vulkan is the exception: `_poison_vulkan_font_surface` (L391) deliberately
swaps `self.backend` while keeping `vulkan_backend` non-nil, and tests attach a
bare `VulkanBackend.create()` directly. An attached-but-uninitialized Vulkan
backend has no framebuffer, so every primitive dispatched into it is a silent
no-op returning empty pixels — while the surface that was actually painted
lives in `self.backend`. Hence the guard at L436:

```
if val Some(vulkan) = self.vulkan_backend:
    if not vulkan.initialized:
        return nil
```

Returning `nil` falls the caller through to `self.backend`.

> **Do not "fix" this by calling `backend_probe_initialized`.** That helper
> (`backend_probe.spl:36`) takes a `BackendProbeResult` and tests
> `probe.status == BackendStatus.Initialized`. `VulkanBackend.initialized` is a
> plain `bool` field (`backend_vulkan.spl:247`). Different types, different
> objects — substituting it does not compile. The import at `engine.spl:57`
> serves the strict-create paths, not this guard.

## Backend name canonicalization

`_engine2d_backend_canonical_name` (`backend_lane.spl:86`) normalizes with
`.trim().lower()` and folds aliases before comparing against the preference
order:

```
["metal", "cuda", "rocm", "vulkan", "directx", "opencl",
 "opengl", "webgpu", "cpu_simd", "software", "cpu"]
```

`hip`/`amd`/`amd_hip`/`amd-hip`/`amd_rocm`/`amd-rocm` → `rocm`;
`d3d11`/`d3d12`/`dx11`/`dx12` → `directx`; empty → `software`.

The order list is all-lowercase, which is what makes the `.lower()`
normalization safe. If you add an entry, keep it lowercase.

All three call sites in that file use the underscore-prefixed local function.
There is no `backend_canonical_name` — that name was called at L129 while being
defined and imported nowhere in the file, which is the bug `b10f1b4309c` fixed.

## The attempt ledger

`font_execution_attempts()` returns one `backend:outcome` entry per target
tried, in order. For a batch the attached CUDA backend cannot service:

```
cuda:failed, metal:unavailable, opencl:unavailable,
vulkan:unavailable, rocm:unavailable, cpu:success
```

`cpu:success` is the documented last resort and must terminate the ledger. A
ledger that does not end in a success entry means the batch was dropped, not
merely offloaded elsewhere.

Raising `FontExecutionPolicy` from `Suggested` to `Preferred` changes neither
the order nor the outcome — only how hard a target is pursued before it is
judged failed.

## Coverage

| Level | Spec |
|---|---|
| Unit, in-process | `test/01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl` |
| Unit, uninitialized Vulkan | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:73-92` |
| System, native binary | `test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl` |

The system lane is **fail-closed and currently unexecuted** — it requires a
qualified pure-Simple runtime, and none exists on the reference machine. See
`doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md`.

## Known asymmetry (open)

The rocm arms (`engine.spl` L1700-1701, L1941-1942, L2006-2007) do
`if rocm.initialized: self.backend = rocm`, hijacking `self.backend` on an
engine whose `selected_backend_name` is something else, whereas the cuda arm
gates on the name. Not reachable from any current construction path, so it is
recorded rather than patched.
