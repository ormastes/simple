# Bug: Engine2D Metal GPU-only-mode scissor clip is unimplemented (silent no-op)

- **Status:** open (honest — no dishonest claim; documented in code)
- **Severity:** P2 (correctness gap on the fast Metal lane; no false-green)
- **Component:** `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`
  (`set_clip` ~line 389, `clear_clip` ~line 400)
- **Platform:** macOS only (real Metal GPU). Cannot be reproduced or verified on
  the Linux CI host (no Metal runtime).

## Symptom

In GPU-only (fast) mode — `_gpu_only_mode()` true, the CPU mirror shrunk to 1x1
by `use_gpu_only()` — `MetalBackend.set_clip(x, y, w, h)` records the clip on the
1x1 mirror (which cannot enforce it) and the Metal compute-dispatch path does
**not** thread the clip rect into its kernels. Consequently a `set_clip(...)`
followed by a draw renders the FULL primitive on the GPU framebuffer, ignoring
the clip region. Clipping is silently a no-op on the fast Metal lane.

In mirror-backed (non-fast) mode this is NOT a problem: `set_clip` forwards to
the full-size CPU mirror, which enforces the clip, and `read_pixels()` returns
the mirror — so clipped output is correct there.

## Honesty status (why this is not a false-green)

The code does not pretend clip works on the GPU path. `set_clip` carries an
explicit comment: "the GPU dispatch path does not apply one either — a clip is a
no-op here." The related (now-closed) readback bug
`engine2d_fast_metal_clip_poisons_gpu_readback_2026-07-03.md` documents the
same fact but tracks only the readback-poisoning interaction, not the underlying
unimplemented-scissor gap — hence this dedicated open record.

## What is missing to wire it (real fix)

Thread the active clip rect into every Metal compute kernel dispatch as push
constants and reject out-of-clip pixels in each `.metal` kernel (the same clip
push-constant fields the Vulkan kernels already carry via `_pack_*_pc`), OR add a
Metal scissor/render-region stage. This requires:

1. New/edited MSL kernels in `backend_metal_msl.spl` with clip-rect push
   constants and a per-pixel in-clip test.
2. `_dispatch_metal_*` in `backend_metal.spl` to pass `clip_x/clip_y/clip_w/
   clip_h/clip_enabled` into the push-constant buffer.
3. `rt_metal_*` runtime support (`metal_graphics_runtime.rs`) if the push-constant
   layout changes.

This is NOT a contained pure-Simple change (needs kernel + runtime work) and
cannot be verified on a non-macOS host, so it is deliberately left unimplemented
and honestly marked rather than faked.

## Verification requirement (when implemented, macOS)

Draw a primitive larger than a `set_clip` region on the fast Metal lane, read
back the full GPU framebuffer, and assert pixels outside the clip rect equal the
background (absolute-pixel oracle), and pixels inside equal the draw color.
