# Host 2D Vulkan/SIMD spec reds found during primitive-rendering verification

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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

## 1. Vulkan `draw_rect_filled` writes a wrong interior colour — high

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl:185,198`

```
it "draw_rect_filled leaves corners untouched":
    ...
    expect(pixel_at_p(pixels, 4, 4, 8)).to_equal(fg)   # line 198, fails
```

8×8 buffer, `clear(0x111111FF)`, `draw_rect_filled(2, 2, 4, 4, 0xAABBCCFF)`.
Pixel `(4,4)` — strictly interior to the filled region, not an edge — reads
`0xAF828DFF` instead of `0xAABBCCFF`. The two corner assertions in the same
test (`(0,0)` and `(7,7)`, both expecting the background colour) pass (the
failure message names only the fg-vs-observed comparison, not the bg
value), so: the clear/background path round-trips exactly, the fill path
does not, and the corruption pattern (`0xAA`→`0xAF`, `0xBB`→`0x82`,
`0xCC`→`0x8D`) is not a uniform channel shift. Mechanism undiagnosed.

**Unblock condition:** trace `draw_rect_filled`'s SPIR-V/GLSL path
(`backend_vulkan_spirv*.spl`, `backend_vulkan_glsl.spl`) for the interior
fragment-shading or descriptor-write step and compare against the
`draw_rect` (outline) path, which is unaffected per the same spec file's
passing cases.

## 2. Metal-on-Vulkan / DirectX-on-Vulkan emulation do not match the Vulkan reference — CLOSED 2026-08-08

`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl:354,382`

Both `it` blocks assert the emulated backend's rendered buffer equals the
real-Vulkan reference buffer; both failed with `expected 2240 to equal 0`
(2240 mismatching values — for a 56×40 buffer, `56*40 == 2240`: literally
every pixel differed, not a partial divergence).

**Root cause: a real batching/readback ordering bug, not an emulation-layer
draw-call translation defect.** Both `"metal-on-vulkan"` and
`"directx-on-vulkan"` requests in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` construct a plain
`VulkanBackend` and call `vulkan.enable_frame_batching()` (same as the plain
`"vulkan"` request). With frame batching enabled, `clear()` /
`draw_rect_filled()` / `draw_circle_filled()` (via `emu_draw_circle`'s
`draw_rect_filled` calls) only *enqueue* SPIR-V compute dispatches into a
not-yet-submitted command buffer (`_dispatch_framebuffer_checked` →
`_enqueue_framebuffer_compute` in `backend_vulkan_helpers.spl`); only
`present()` and `submit_batch()` called `_flush_pending_compute()` to
actually submit that command buffer to the GPU queue and fence-wait. But
`VulkanBackend.read_pixels()` / `read_pixels_with_source()`
(`backend_vulkan.spl`) never flushed — it read `vulkan_sffi_read_buffer_bytes`
straight off the device buffer whenever `self.dirty` was true, which the
enqueue path also (correctly) sets, so the stale-vs-flushed distinction was
invisible to every other caller/receipt. The spec calls `eng.read_pixels()`
directly (no `present()`), so it read the device framebuffer before the
batched clear+rect+circle dispatches were ever submitted — i.e. it read
uninitialized/leftover device memory, diverging from the `SoftwareBackend`
reference at every pixel. The plain-`"vulkan"` and real-GPU-gradient specs in
this same file never called `enable_frame_batching()` directly (they use
`VulkanBackend.create()` + `vk.init()` with no batching), so they dispatched
immediately and never hit this path — which is why the bug was invisible
outside these two emulation-lane `it` blocks specifically.

**Fix:** `read_pixels_with_source()` now flushes pending batched compute
first, exactly mirroring what `present()` already does (same
`_flush_pending_compute()` call, same `completion_unknown` /
`VK_DISPATCH_COMPLETED_INELIGIBLE` handling), so pixel reads are correct
whether or not `present()` was ever called. One file, `.spl` only:
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
(`read_pixels_with_source()`).

Verified: `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
→ `Results: 8 total, 8 passed, 0 failed` (previously 6/8). No regression in
`backend_vulkan_processing_spec.spl` (22/22),
`backend_vulkan_drawing_spec.spl` (30/30),
`bridge_drawing_compositor_spec.spl` (4/4), or
`engine2d_cpu_simd_parity_spec.spl` (5/5), all re-run after the edit. Item 3
(`vulkan_engine2d_frame_batch_contract_spec.spl`) is unaffected by this fix —
its failure is a pre-existing, unrelated `Module count limit (800) exceeded`
load error under `test/01_unit/check/`, not a pixel-correctness assertion.

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
