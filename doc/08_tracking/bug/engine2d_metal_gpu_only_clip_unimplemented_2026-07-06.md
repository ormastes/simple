# Bug: Engine2D Metal GPU-only-mode scissor clip evidence

- **Status:** implemented; current-source native Metal evidence pending
- **Severity:** P2 (implementation complete; deployment evidence remains)
- **Component:** `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`
  (`set_clip`, `clear_clip`, `_bind_metal_clip`)
- **Platform:** macOS only (real Metal GPU). Cannot be reproduced or verified on
  the Linux CI host (no Metal runtime).

## Original symptom

In GPU-only (fast) mode — `_gpu_only_mode()` true, the CPU mirror shrunk to 1x1
by `use_gpu_only()` — `MetalBackend.set_clip(x, y, w, h)` records the clip on the
1x1 mirror (which cannot enforce it) and the Metal compute-dispatch path does
**not** thread the clip rect into its kernels. Consequently a `set_clip(...)`
followed by a draw renders the FULL primitive on the GPU framebuffer, ignoring
the clip region. Clipping is silently a no-op on the fast Metal lane.

In mirror-backed (non-fast) mode this is NOT a problem: `set_clip` forwards to
the full-size CPU mirror, which enforces the clip, and `read_pixels()` returns
the mirror — so clipped output is correct there.

## Implemented fix (2026-07-17)

`MetalBackend` now owns the active clip state and binds a 20-byte `ClipParams`
record at Metal buffer index 4 for every compute dispatch. Every drawing kernel
rejects pixels outside that rectangle; `kernel_clear` deliberately ignores the
clip to retain the established full-surface clear contract. This reuses the
existing `metal_sffi_set_bytes` interface and does not change the runtime ABI.

The macOS-only readback regression switches the backend to GPU-only mode, draws
a full-surface rectangle through a small clip, clears the clip, and verifies
absolute inside/outside pixels plus a post-clear draw. The implementation is no
longer missing, but closure still requires this current source to be built and
the native Metal regression to pass; the stale deployed CLI cannot provide that
evidence while the tracked Stage-4 bootstrap blocker remains open.

## Original proposed approach

Thread the active clip rect into every Metal compute kernel dispatch as push
constants and reject out-of-clip pixels in each `.metal` kernel (the same clip
push-constant fields the Vulkan kernels already carry via `_pack_*_pc`), OR add a
Metal scissor/render-region stage. This requires:

1. New/edited MSL kernels in `backend_metal_msl.spl` with clip-rect push
   constants and a per-pixel in-clip test.
2. `_dispatch_metal_*` in `backend_metal.spl` to pass `clip_x/clip_y/clip_w/
   clip_h/clip_enabled` into the push-constant buffer.
3. `rt_metal_*` runtime support (`metal_graphics_runtime.rs`) if the push-constant
   layout changes. The implemented buffer-4 design avoided that ABI change.

## Verification requirement (when implemented, macOS)

Draw a primitive larger than a `set_clip` region on the fast Metal lane, read
back the full GPU framebuffer, and assert pixels outside the clip rect equal the
background (absolute-pixel oracle), and pixels inside equal the draw color.
