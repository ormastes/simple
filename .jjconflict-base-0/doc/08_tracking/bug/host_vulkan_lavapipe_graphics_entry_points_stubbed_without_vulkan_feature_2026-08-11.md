# Host Vulkan reaches lavapipe, but every graphics entry point is a 0-returning stub without the `vulkan` cargo feature

**Date:** 2026-08-11
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Severity:** High — blocks all pixel-level host-GPU evidence (SCCT image comparison, offscreen readback), while presenting as a silent, error-free zero
**Area:** host GPU / Vulkan runtime FFI, seed build configuration

## Summary

Simple's **host** Vulkan code does reach a real software Vulkan device. With
`VK_DRIVER_FILES` pinned to the Mesa lavapipe ICD, `rt_vulkan_init()` succeeds,
one device is enumerated, and the driver reports its real name. This is the
first time a Simple-side Vulkan device has been reached at all — the prior
board-Vulkan effort only ever got as far as `spirv-val`.

The **graphics half** of the same surface is entirely non-functional on the
deployed binary. `rt_vulkan_create_offscreen_render_pass`,
`rt_vulkan_create_image`, `rt_vulkan_create_framebuffer`, and
`rt_vulkan_begin_graphics` all return `0`, and `rt_vulkan_get_last_error()`
returns **empty text** — so the failure carries no diagnostic whatsoever. A
caller that only checks the error string sees success.

The cause is a build-configuration gap, not a lavapipe limitation and not a
missing symbol.

## Evidence — device reachability (verbatim probe output)

Probe: pins the ICD, initialises, enumerates, selects, and reads identity
strings. Binary under test:
`bin/release/x86_64-unknown-linux-gnu/simple`, 59210792 bytes,
mtime `2026-08-11 05:18:56` (Rust bootstrap seed — emits the seed banner).

With `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`:

```
PROBE-BEGIN
is_available_pre_init=1
init=true
is_available_post_init=1
device_count=1
last_error_after_count=[]
device[0].name=[llvmpipe (LLVM 20.1.2, 256 bits)]
device[0].driver_identity=[llvmpipe (LLVM 20.1.2, 256 bits)|vendor=00010005|device=00000000|driver=06402008|api=0040413e]
select_device(0)=1
get_device_handle=137210381441072
selected_device_type=[cpu]
selected_driver_identity=[llvmpipe (LLVM 20.1.2, 256 bits)|vendor=00010005|device=00000000|driver=06402008|api=0040413e]
last_error_after_select=[]
PROBE-END
```

With `VK_DRIVER_FILES=/nonexistent/bogus.json` (control):

```
PROBE-BEGIN
is_available_pre_init=1
init=false
is_available_post_init=1
device_count=0
last_error_after_count=[]
PROBE-END
```

The two runs differ, which proves the loader really honours the variable and
that the `llvmpipe` result above is genuinely lavapipe answering.

### Secondary finding: `rt_vulkan_is_available()` is not an availability oracle

Note `is_available_pre_init=1` and `is_available_post_init=1` in **both** runs —
including the bogus-ICD run where `init=false` and `device_count=0`. Any code
gating on `rt_vulkan_is_available()` will proceed on a host with no usable
driver. Use `rt_vulkan_init()` + `rt_vulkan_device_count() > 0` instead.

### In-process ICD pinning works

`env_set("VK_DRIVER_FILES", ...)` followed by `rt_vulkan_shutdown()` and a fresh
`rt_vulkan_init()` genuinely reselects the driver inside one process:

```
ENV-BEGIN
set_bogus=true
init_bogus=false
count_bogus=0
shutdown=true
set_good=true
init_good=true
count_good=1
ENV-END
```

## Evidence — the graphics half returns 0 with no error

Probe: same pinned lavapipe ICD, then a 64x64 RGBA8 offscreen clear
(`format=37` `DRAW_IR_FORMAT_R8G8B8A8_UNORM`, `depth=126`
`DRAW_IR_FORMAT_D32_SFLOAT`, `usage=0x04|0x10|0x01`) and a device readback:

```
CLEAR-BEGIN
init=true
device_count=1
device_name=[llvmpipe (LLVM 20.1.2, 256 bits)]
device_handle_positive=true
render_pass_positive=false
color_image_positive=false
depth_image_positive=false
framebuffer_positive=false
err_after_resources=[]
cmd_positive=false
fence=0
err_after_submit=[]
copy_from_image=false
pixel_bytes=16384
px0=(0,0,0,0)
pxmid=(0,0,0,0)
pxlast=(0,0,0,0)
all_pixels_uniform=true
err_after_readback=[]
CLEAR-END
```

Every graphics handle is 0/false; `get_last_error()` is empty at all three
checkpoints. `all_pixels_uniform=true` is a trap worth naming: the readback
buffer is uniformly zero because it was never written, so a naive "is the image
uniform?" oracle passes on a completely dead pipeline.

## Root cause

`src/compiler_rust/compiler/src/interpreter_extern/vulkan.rs:39-43` states the
contract explicitly:

> Feature gating, checked rather than assumed: 84 of the 90 entry points carry
> both a `#[cfg(feature = "vulkan")]` real body and a
> `#[cfg(not(feature = "vulkan"))]` stub, and the remaining 6 are ungated. The
> symbols therefore exist on a default build … What changes with the `vulkan`
> feature is the *answer*, never the symbol's presence.

The deployed seed was built **without** that feature, so the linked bodies are
the stubs, e.g.
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_graphics.rs`:

- `:541-542` — `#[cfg(feature = "vulkan")] pub extern "C" fn rt_vulkan_create_image(_device, w, h, fmt, usage) -> i64` (real)
- `:584-585` — `#[cfg(not(feature = "vulkan"))] pub extern "C" fn rt_vulkan_create_image(_device, _w, _h, _fmt, _usage) -> i64` (stub, ignores every argument)

Feature declarations: `src/compiler_rust/runtime/Cargo.toml:29`
(`vulkan = ["ash", "gpu-allocator", "spirv-reflect", "ash-window", "winit", "raw-window-handle"]`)
and `src/compiler_rust/compiler/Cargo.toml:26-28`
(`vulkan`, `vulkan-validation`, `vulkan-graphics`).

Device enumeration survives because it is served by the `ash`-based handlers in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`, which are consulted
first via `EXTERN_DISPATCH` and are not gated the same way — hence the split
behaviour that makes this so easy to misdiagnose as a driver problem.

## Why a pixel-level SCCT is not constructible today

The Simple-side API surface is complete — there is no missing binding. All of
these are declared and importable from
`src/lib/nogc_sync_mut/io/vulkan_sffi.spl`:
`rt_vulkan_create_offscreen_render_pass` (:316), `rt_vulkan_create_image` (:336),
`rt_vulkan_copy_from_image` (:339), `rt_vulkan_create_framebuffer` (:348),
`rt_vulkan_begin_render_pass_gfx` (:364, taking `clear_r/g/b/a: f64`), plus
`rt_vulkan_submit_graphics_and_wait_fence`. An existing consumer,
`src/lib/nogc_sync_mut/engine/render/vulkan_backend3d.spl`, already implements
the full offscreen clear→submit→`_capture_last_color_rgba8()` sequence (:277,
:481, :530, :680).

A pure clear needs no shader, so nothing else is missing conceptually. The only
blocker is that the linked implementations return 0. Deploying a seed built with
`--features vulkan` should make the comparison live with **no source edit** to
the provider or spec written for this investigation.

## Unblock condition

Rebuild and deploy the seed with the runtime `vulkan` feature enabled, then
re-run:

```
setsid bin/simple test test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl --no-session-daemon --timeout 900
```

The spec's main scenario branches on `ProviderStatus`: it asserts exact pixel
equality once the graphics path executes, and asserts a fail-closed
`unavailable` naming the failing stage until then. It does not need to be
rewritten when the feature lands.

## Related defect encountered while probing

Any use of the struct-returning wrappers in `vulkan_sffi.spl` (e.g.
`vulkan_device_info`, which builds `VulkanDeviceInfo`) panics the JIT with
`missing runtime fn 'rt_struct_receiver_valid'`
(`compiler/src/codegen/instr/helpers.rs:308:28`), collapsing 74 function bodies
— including all of `DynLib.*` and `VulkanFfi.*` — to the interpreter:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: codegen: 74 function body/bodies failed to compile: [DynLib.sym, DynLib.call0, ..., VulkanFfi.device_count, ...]
```

Workaround used here: call the raw `rt_vulkan_*` externs and the plain-`text`
wrapper `vulkan_sffi_device_name`
(`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:619`) instead of any
struct-returning wrapper. This deserves its own record.

## Artifacts

- Provider: `src/lib/nogc_sync_mut/spec/evidence/counterpart/host_vulkan_lavapipe_provider.spl`
- Spec: `test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl`
- Spec verdict as of this record: `Results: 6 total, 6 passed, 0 failed`
  (sabotage control: `Results: 6 total, 5 passed, 1 failed`)
