# Engine2D rounded gradients require a native backend primitive

Status: OPEN — rejected fallback removed
Date: 2026-07-25
Owners: Engine2D backend, Metal session, Vulkan session, CPU SIMD runtime

## Symptom

`draw_ir_adv.spl` receives both `background-image:
linear-gradient(<top>,<bottom>)` and `border-radius`, but routes the box through
`draw_gradient_rect`. The gradient therefore paints square corners even though
the same box's solid fill and border are rounded.

This is visible in the Aetheric glass window material generated from the Stitch
theme: the window background reaches the square bounding-box corners.

## Rejected approach

A proposed `draw_rounded_gradient_rect` emulation built a transparent
window-sized pixel array and called `draw_image_blend` once.

That approach is not production-safe and was removed in full:

- Metal and Vulkan image-composite fallbacks may read back and upload the full
  framebuffer when a native composite is unavailable or a mask is active.
- It allocates one `w * h` payload per themed window.
- It introduced a pixel-centre circle silhouette that was not byte-identical
  to the canonical `draw_rounded_rect` arc-replay mask for every size.
- It did not prove native x86 SSE2 or ARM NEON execution with operation-specific
  receipts.
- The Engine2D facade omitted the typed Vulkan receiver/reassignment needed to
  preserve mutated Vulkan state.

Do not restore this fallback, even as compatibility behavior.

## Frozen semantics

The new primitive is:

```text
draw_rounded_gradient_rect(
    x, y, width, height, radius, top_argb, bottom_argb
)
```

Its contract is:

1. `width <= 0 || height <= 0` is a no-op.
2. Radius clamping and pixel membership are exactly the mask produced by the
   current canonical filled `draw_rounded_rect` for the same dimensions and
   radius. Tests compare against that rendered mask; they must not duplicate a
   second mathematical oracle.
3. Each included row uses the exact signed integer channel interpolation from
   `emu_draw_gradient_rect`:
   `top + (bottom - top) * row / max(height - 1, 1)`.
4. Straight ARGB is source-over blended. Fully opaque stops remain exact.
5. Viewport bounds, active clip, and active mask are intersected. A mask byte of
   zero blocks the destination; out-of-range mask coordinates retain the
   existing backend convention.
6. Draw IR performs one backend call. Metal and Vulkan perform at most one
   compute dispatch and no framebuffer readback, full-frame upload, or
   per-window framebuffer-sized allocation.
7. The operation does not mutate or temporarily replace global clip/mask state.
8. No shadow ordering or legacy WM command stream changes belong to this work.

## Required implementation

### 1. Canonical API and facade

- Add the method to
  `src/lib/gc_async_mut/gpu/engine2d/backend.spl`.
- Implement it in all fourteen `RenderBackend` implementations.
- Add the Engine2D method in `engine.spl`.
- The facade must use explicit typed branches for VirtIO, baremetal, and
  Vulkan. The Vulkan branch must assign the mutated value back to both
  `self.vulkan_backend` and `self.backend`, matching `draw_gradient_rect_h` and
  other stateful Vulkan operations.
- Change `draw_ir_adv.spl` only after every backend implementation exists.

### 2. One shared silhouette contract

First freeze `draw_rounded_rect` membership with an executable mask fixture for:

- `w=2,h=2,r=1`;
- `w=2,h=7,r=1`;
- odd/even widths and heights;
- radius `0`, negative, half-size, and oversized;
- clipped and partially offscreen rectangles.

Metal's existing `kernel_draw_rounded_rect` replays the canonical body and arc
draws. Vulkan currently does not: `backend_vulkan.spl` explicitly avoids its
`pipe_rounded_rect` because the checked-in shader fills a plain rectangle.
Repair Vulkan filled-rounded-rect parity first. Rounded-gradient kernels must
then use the same reviewed membership helper/source fragment as their backend's
filled-rounded-rect kernel, not a new circle approximation.

### 3. Metal native path

Touch these owners together:

- `backend_metal_msl.spl`: add
  `kernel_draw_rounded_gradient_rect`.
- `backend_metal_helpers.spl`: add one versioned parameter pack containing
  geometry, radius, both colors, framebuffer size, clip, and mask metadata.
- Metal session/pipeline state: compile, retain, expose, and release
  `pipe_rounded_gradient_rect`.
- `backend_metal.spl`: upload/reuse a mask buffer when masking is active, bind
  framebuffer + mask + parameter bytes, and dispatch one 2-D grid.

The kernel must load destination pixels and perform integer source-over for
non-opaque gradient rows. A disabled mask is represented by metadata/binding,
not by clearing backend mask state. Pipeline failure must fail closed or use a
bounded CPU surface path that does not read/upload the full GPU framebuffer;
it must never call the rejected image fallback.

### 4. Vulkan native path

Touch these owners together:

- `backend_vulkan_glsl.spl`: add the reviewed rounded-gradient compute source.
- SPIR-V generation/blob owner: compile and check in the matching SPIR-V with
  a source hash/version assertion.
- `backend_vulkan_session.spl`: create, expose, and destroy
  `shader_rounded_gradient` and `pipe_rounded_gradient`.
- `backend_vulkan_helpers.spl`: add the versioned push-constant pack.
- `backend_vulkan.spl`: typed single-dispatch method and state reassignment in
  Engine2D.

Descriptor layout must bind framebuffer and mask storage. The shader intersects
viewport, clip, canonical rounded membership, and mask before loading/blending
the destination. No `_draw_image_*`, `read_pixels`, `vulkan_sffi_wait_idle`, or
whole-frame host upload is allowed on this hot path.

### 5. CPU x86/ARM SIMD path

Add one operation-specific runtime surface rather than generating a scalar
payload:

- Pure-Simple declaration/facade in
  `nogc_sync_mut/gpu/engine2d/simd_native_rows.spl` and `simd_kernels.spl`.
- Native implementation with explicit x86 SSE2 and ARM NEON branches in the
  Engine2D SIMD runtime owner.
- Interpreter bridge and runtime-symbol registration for test parity only;
  interpreter execution must not claim native SIMD.
- Separate `rounded_gradient_hits` counters and a typed receipt containing
  architecture, feature, rows/spans processed, alpha path, mask path, and
  before/after hit counts.

The kernel writes the destination buffer directly, uses the canonical
rounded-rect row spans, performs exact integer gradient lerp, and vectorizes
opaque fill and source-over chunks. Clip and mask are inputs. A scalar tail is
allowed; a wholly scalar operation must not advance the native receipt.

## Verification gates

All gates are required before Draw IR is switched:

1. Software/reference pixels equal `draw_rounded_rect` membership with
   non-equal gradient stops for the complete size/radius fixture matrix.
2. Degenerate, offscreen, clip, mask, opaque, translucent, and zero-alpha cases
   pass.
3. CPU scalar, x86 SSE2, and ARM NEON readbacks are byte-identical; native runs
   prove operation-specific hit deltas and receipts.
4. Metal and Vulkan source-contract tests prove shader entry, parameter layout,
   pipeline creation/destruction, mask binding, and exactly one dispatch.
5. Live Metal and Vulkan readback is byte-identical to the software reference.
6. Dispatch evidence proves zero per-row submissions and zero image-fallback
   calls.
7. Allocation/synchronization evidence proves no `w*h` transient payload, no
   full-frame readback/upload, and no wait-idle on the operation path.
8. Engine2D tests assert the typed Vulkan branch reassigns both Vulkan fields.
9. Existing solid rounded-rect, rectangular gradient, shadow, legacy WM stream,
   Draw IR, host WM, and QEMU tests remain green.

## Safe delivery order

1. Freeze canonical rounded-rect mask fixtures and repair Vulkan solid-rounded
   parity.
2. Land CPU scalar semantics plus native SSE2/NEON kernel and receipts.
3. Land Metal shader/session/mask pipeline and live parity.
4. Land Vulkan GLSL/SPIR-V/session/mask pipeline and live parity.
5. Add the trait/facade method to every backend in one ABI-complete change.
6. Switch Draw IR and run host WM evidence, then x86 and ARM QEMU evidence.

The merge owner must reject any intermediate change that exposes the public
operation while one backend silently performs row submissions, image fallback,
full-frame synchronization, or a different rounded silhouette.
