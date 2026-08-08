# Host 2D Vulkan/SIMD spec reds found during primitive-rendering verification

**Filed:** 2026-08-08 · **Severity:** mixed (see per-item) · **Scope:** HOST
(Linux x86_64) only, found while verifying
`doc/09_report/host_2d_vulkan_simd_primitive_verification_2026-08-08.md`.
**Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`,
mtime 2026-08-08 03:38 UTC. Vulkan device: llvmpipe (lavapipe, software),
the only device the loader enumerates headlessly in this sandbox.

These four `it` cases are correct specs asserting real behaviour the
implementation does not currently have (or, for #3/#4, source-scan checks
that are stale against the current file layout). Left RED per
`.claude/rules/testing.md` — not weakened, not marked pending.

## 1. Vulkan `draw_rect_filled` writes a wrong interior colour — CLOSED 2026-08-08

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl:185,198`

**Root cause (two stacked issues, both resolved):**

1. **Real cross-backend blend-formula divergence (the actual defect).**
   `draw_rect_filled` routes any color whose top ARGB byte (alpha, per
   `color.spl`'s `0xAARRGGBB` layout) is `< 255` through
   `draw_image_blend` → `_draw_image_blend_native` → the hand-assembled
   `spirv_blit` SPIR-V kernel in `backend_vulkan_spirv_raster_blobs.spl`
   (compiled from the "src-over" branch of `_glsl_blit()` in
   `backend_vulkan_glsl.spl`). That kernel computed
   `out_r/out_g/out_b = (src*sa + dst*inv) / 255` — the *old*,
   pre-2026-XX-XX formula that `color.spl`'s CPU `blend()` explicitly
   documents as wrong and was fixed away from (it "treated dst's RGB as
   if dst were always opaque and never unpremultiplied the result"). The
   CPU `SoftwareBackend.draw_rect_filled` already uses the corrected
   Porter-Duff formula, `out = (src*sa + dst*dst_weight) / out_a` where
   `dst_weight = (dst_alpha*inv)/255` and `out_a = sa+dst_weight`. For an
   opaque destination (`dst_alpha=255`) the two formulas coincide, which
   is why this was invisible until a destination with `dst_alpha != 255`
   was exercised (as `0x111111FF` is, under ARGB: alpha byte `0x11`).
   **Fixed** by disassembling `spirv_blit` with `spirv-dis`, reordering
   the src-over block so `dst_weight`/`out_a` are computed before the
   per-channel divide and dividing by `out_a` instead of the `255`
   constant (matching `color.spl`'s `blend()` exactly), reassembling with
   `spirv-as --target-env vulkan1.1` (`spirv-val` clean, byte-identical
   size 4016), and updating the `[u8]` blob in
   `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv_raster_blobs.spl`
   (`spirv_blit()`). Verified: for `bg=0x111111FF`, `fg=0xAABBCCFF` the
   Vulkan and CPU backends now both produce `0xAFB6C6FF` (previously
   Vulkan produced `0xAF828DFF`, CPU produced `0xAFB6C6FF` — a real,
   reproducible divergence, confirmed via a standalone probe dumping the
   full 8×8 grid from each backend before any spec edit was made).

2. **Spec literal used a translucent color and asserted opaque-fill
   semantics.** Per `color.spl`'s documented ARGB layout, `0xAABBCCFF`
   decodes as alpha=`0xAA`(170), not 255 — so `draw_rect_filled`
   *correctly* took the alpha-blend path rather than a flat opaque
   store; a `[vk-order]` trace with `SIMPLE_VK_ORDER_TRACE=1` showed
   `image-composite … mode=1` (blend) instead of a `pipe_rect_filled`
   dispatch, confirming this before any implementation change. The
   filing's premise that "corners round-trip, only the interior pixel is
   wrong" was a spec-coverage artifact, not a real edge/interior split: a
   full-grid probe showed the **entire filled region** (`(2,2)`–`(5,5)`,
   not just `(4,4)`) got the wrong, uniformly-computed blended value —
   the spec just never asserted an edge pixel. Fixed by changing the
   test's `bg`/`fg` literals to `0xFF111111`/`0xFFAABBCC` (true ARGB
   opaque) so the assertion exercises the intended flat-fill path.

Both fixes are pure `.spl` (SPIR-V blob + one spec file). Verified:
`bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl`
→ `Results: 22 total, 22 passed, 0 failed` (previously 21/22). No
regression in `backend_vulkan_drawing_spec.spl` (30/30),
`bridge_drawing_compositor_spec.spl` (4/4), or
`engine2d_cpu_simd_parity_spec.spl` (5/5), all re-run after the blob
edit.

## 2. Metal-on-Vulkan / DirectX-on-Vulkan emulation do not match the Vulkan reference — medium

`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl:354,382`

Both `it` blocks assert the emulated backend's rendered buffer equals the
real-Vulkan reference buffer; both fail with `expected 2240 to equal 0`
(2240 mismatching values in the comparison, i.e. the buffers differ).

**Unblock condition:** diff the emulation-layer draw-call translation
(`backend_metal.spl` / `backend_directx.spl`) against the Vulkan reference
kernel invoked by `vulkan_compute_oracle_spec.spl`, isolate the first
divergent pixel.

## 3. `vulkan_engine2d_frame_batch_contract_spec.spl` fenced-submit dependency check — needs triage

`test/01_unit/check/vulkan_engine2d_frame_batch_contract_spec.spl:26`

`it "retains dependencies through the one fenced frame submit"` fails; not
triaged further in this pass (out of the fill/blend/blit/clear primitive
scope this report covers). Needs its own investigation pass.

## 4. `simd_kernels_spec.spl` MIR-source self-check is stale — low, not a rendering defect

`test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl:108`

`it "uses the cross-mode return-array span bridge for backend fills"` reads
`mir_source` from a `file_read()` of a specific compiler source path and
`expect(mir_source).to_contain(...)`. The file it currently reads back is
`src/compiler/50.mir/mir_lowering_expr.spl`, which no longer contains the
`rt_engine2d_simd_fill_span_u32` dispatch string — a MIR-lowering file split
moved that string elsewhere. This is a source-layout staleness check, not a
pixel-correctness or rendering defect; it was pre-existing before this
task's spec additions (44/45 before, 50/51 after — the delta is the 6 new
cases added by this task, all passing).

**Unblock condition:** update the spec's `file_read()` target(s) to the
current file(s) containing the MIR dispatch string for
`rt_engine2d_simd_fill_span_u32` / `rt_engine2d_simd_copy_span_u32`.
