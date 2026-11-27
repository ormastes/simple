# Stage 2 MIR: unresolved method calls and trait-object rejections in bootstrap run 13

- **Date:** 2026-11-07
- **Severity:** P1 (blocks the sanctioned bootstrap; Stage 2 `compiler_cli_build`)
- **Status:** fix-implemented
- **Found by:** bootstrap run 13 (`5fdf9fa`), shards 2-7, 293 of 500 MIR errors
  in the "unresolved method call" / native-trait-object cluster.

## Root causes

### 1. Method call on an optional class receiver (compiler)

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, unresolved-owner
branch of `lower_method_call`.

MIR has no flow typing. After `if self.ffi == nil: return false` the receiver
`self.ffi` is still `Optional(CudaFfi)`; `val cuda = self.cuda_backend.?` binds
`CudaBackend?` (the exists-check passes an optional through). The interpreter calls
the payload's method; MIR found no owner (`key=::is_available owner=`) and failed
closed. Sites: `engine2d/opencl_session.spl` (46), `engine2d/cuda_session.spl` (20),
`text_layout/font_renderer.spl` (~32), `ui/gui_renderer.spl` (5), `engine2d/engine.spl`.

Fix: `unwrap_optional_class_receiver_v1`. When the receiver's declared or remembered
type is `Optional(Named C)`, `C` is a **class**, and `C` declares the method, the
receiver goes through the existing Option `.unwrap()` lowering (`rt_is_some` test,
`rt_panic` on nil) and the call dispatches to `C.method`. Structs are excluded: their
payload is a copy, so a `me` write would be dropped. A class that does not declare
the method, and an optional primitive, are still rejected.

Spec: `test/01_unit/compiler/50.mir/optional_class_receiver_method_spec.spl`.
Before the fix: 5 passed, 5 failed. After the fix: 10 passed. Cases: field, exists-check,
alias, trait-impl method, panic path; negatives: undeclared method, optional
primitive, struct payload, Option API name. Option API names (`expect`, `and_then`,
`hash`, ...) stay Option-owned even when `C` declares them, and the unwrap is emitted
only when the owner dispatch will resolve the method.

### 2. Two `RenderBackend` traits (source)

`std.gpu.engine2d.backend` resolves to `lib.nogc_async_mut.gpu.engine2d.backend`,
which is a mirror trait with the same name. Eleven gc-tier backends imported that
spelling: cpu, opencl, opengl, intel, qualcomm, webgpu, virtio_gpu, baremetal,
cuda_ext, emu, and emu_adv. Their `impl RenderBackend` therefore registered under
the nogc owner, while `Engine2D.backend` uses the gc owner. That produced
"missing native trait implementation" for every `Engine2D(backend: cpu, ...)`, plus
the `backend_emu_adv.spl:85` "lacks object-safe method `read_pixels_region`" error.
The fix moves all eleven imports to `std.gc_async_mut.gpu.engine2d.backend`.

### 3. Trait or impl receiver-mutability drift (source)

The native trait-object checker demands exact `fn`/`me` equality, and it reports
only the first slot that does not match. Every slot was audited:

- In `RenderBackend`, `read_pixels` and `read_pixels_with_source` were `fn`, but
  the Vulkan and CUDA implementations mutate state (mirror refresh, completion
  quarantine). Both are now `me` in the trait, in the nogc mirror, and in all 14
  implementations.
- The `width` and `height` implementations in vulkan, software, and cpu were `me`
  but only read state. They are now `fn`, which matches the trait.
- In `FrameClock`, `now_micros` and `sleep_until` were `fn`, but every
  implementation (including `FixedStepClock`, which advances time) is `me`. The
  trait is now `me`.

### 4. `Optional` to non-optional trait store in engine.spl (source)

`self.backend = cuda` with `cuda: CudaBackend?` is an implicit Optional-to-`T`
conversion, and widening that is out of scope. The 44 `val cuda =
self.cuda_backend.?` bindings and the 10 nil-guarded `val x = active...` aliases now
call `.unwrap()` explicitly. Every one of them was already guarded.

### 5. Free functions and deleted methods called as methods (source)

- `self.obj_taker.take_object(...)` and `.take_with_types(...)` have no method
  form. The callers now use `objtaker_take_object` and `objtaker_take_with_types`,
  as `object_resolver.spl` already does.
- `self.smf_cache_mgr.ref_count_inc` and `ref_count_dec` now call the
  `smfcachemanager_ref_count_*` free functions.
- `FramebufferDriver.has_staging_buffer()` and
  `VirtioGpuDriver.framebuffer_sync_for_cpu()` were deleted by the transplant in
  `88aac2ffe28`, which left one caller of each behind.
  - fb_driver now inlines the deleted body, `back_buffer.len() > 0`.
  - The dangling virtio sync call was removed. The transplant removed the whole
    `_sync_allocation_for_*` machinery, so this leaves the current design as it
    is.
  - **Owner check:** confirm the DMA sync removal was intended.

## Not fixed here

These stay with their owners or with sibling lanes:

- **Receivers whose type is never resolved:** `sha1 w.get`, `hash.spl arr.hash()`,
  `parse_i64` on untyped text, `sqrt`, `round`, `min`, `keys`, `has` on untyped
  dicts, `hir_target_constraints eq.unwrap()`, and `sdn_codec to_text`.
- **Owned by the payload-shape lane:** the four compositor errors "native optional
  trait conversion requires a matching declared payload".
- **Not investigated:** `CompositorBackend` for `SharedMdiFramebufferBackend`.

## Verification (run-13 Stage 2 binary, per-module `compile --format=smf`)

The Stage 2 binary embeds the OLD MIR lowering, so it validates the source fixes
only; the compiler fix (cause 1) is proven by the spec and takes effect on the next
Stage 2. `engine.spl` closure: engine.spl itself 145 -> 1 MIR error; 0 trait-object
errors remain in the closure. The rest of the closure's errors (opencl_session 46,
font_renderer 23, cuda_session 20) are cause-1 optional receivers.

Remaining in engine.spl:
- (fixed) `cuda.draw_text_bg` -- the `Engine2DExtended for CudaBackend` impl lives in
  `backend_cuda_ext.spl`, which engine.spl never imported (import added).
- `vulkan.submit_batch_for_present()` -- `Engine2D.submit_batch_for_present` was added
  in 8a87db7d9eb but `VulkanBackend.submit_batch_for_present` never landed in this
  tree. Owner decision: implement the presenter-read receipt or delete the wrapper
  (only `engine_branch_coverage_spec` calls it).
