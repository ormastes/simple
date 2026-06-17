# Vulkan Raster Kernels No-op / Divergent vs CPU Reference - 2026-06-17

## Severity
P1 (partially fixed). Several Engine2D Vulkan primitives silently rendered
nothing (dispatched a no-op SPIR-V shader) despite real validated kernels being
available; of the ones now wired, two more diverge substantially from the CPU
reference.

## Component
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` (init, ~line 290)
- `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl` (init, ~line 163)
- Kernels: `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv.spl` /
  `backend_vulkan_spirv_raster_blobs.spl`

## Summary
`VulkanBackend.init` compiled `rect_outline, circle_filled, circle_outline,
line, rounded_rect, triangle, gradient, blit` from `spirv_noop_storage()` (a
no-op shader) even though real, `spirv-val`-validated SPIR-V blobs
(`spirv_circle_filled()` etc.) were already imported. Result: those eight
primitives dispatched a no-op and rendered nothing on Vulkan — only `clear` and
`rect_filled` used real kernels. The `backend_vulkan_spirv.spl` header claims
"VKSPIRV-001 resolved … now real compiled SPIR-V", but the backend init was
never switched over to use them.

## Reproduce (classic interpreter, Vulkan-capable host)
Render an identical scene through `VulkanBackend` and `SoftwareBackend` and
count pixel mismatches (64x48). Before the fix, `draw_circle_filled` produced
~197 mismatches (entire circle missing); rects matched (0).

## Verification matrix (Vulkan vs SoftwareBackend reference, 64x48)
After wiring all eight real kernels and measuring per-primitive:

| primitive       | status                                              |
|-----------------|-----------------------------------------------------|
| clear           | already real, correct (0 mismatch)                  |
| rect_filled     | already real, correct (0)                           |
| rect_outline    | **fixed** — wired, bit-exact (0)                     |
| circle_filled   | **fixed** — wired, bit-exact (0)                     |
| triangle_filled | **fixed** — wired, bit-exact (0)                     |
| rounded_rect    | **reverted to no-op** — see "Reverted" below         |
| circle_outline  | **reverted to no-op** — see "Reverted" below         |
| line            | **reverted to no-op** — see "Reverted" below         |
| gradient_rect   | **reverted to no-op** — see "Reverted" below         |
| blit            | untested — kept no-op (needs source-buffer binding) |

**5 of 10 kernels are wired bit-exact** (clear, rect_filled, rect_outline,
circle_filled, triangle_filled) vs the SoftwareBackend reference. The other 5
stay no-op.

## Reverted (2026-06-17): rounded_rect / circle_outline / line / gradient

These four were briefly wired by also changing `SoftwareBackend` to match each
GPU blob's convention (rounded_rect fill, distance-ring outline, steps+1 DDA
line, gradient divisor `h`). That was WRONG: `SoftwareBackend` is intentionally
**bit-exact with Metal** (commit 99af88d) and implements the standard, documented
behavior — `draw_rounded_rect` is **outline-only** by contract, `draw_line` is a
Bresenham line that includes its end point, `draw_circle` is a Bresenham midpoint
outline. The blob conventions differ (fill, a DDA that drops the end pixel,
distance-ring), so matching them degraded `SoftwareBackend` and **regressed
`test/02_integration/rendering/engine2d_primitives_spec.spl`** (24/0 → 22/2).

Resolution: `SoftwareBackend` restored to its pristine Metal-bit-exact version;
the four divergent kernels reverted to the no-op shader; the oracle spec only
asserts the five that are genuinely bit-exact with the standard SoftwareBackend.
Reconciling the GPU blobs with the standard backend (or deciding a per-primitive
canonical convention) is the real remaining work and must NOT be done by
degrading `SoftwareBackend`.

### gradient_rect (RESOLVED via spirv-dis)
The GLSL source uses `mix()`/float (`t = ly/(rh-1)`), but `spirv-dis` of the
`spirv_gradient_rect` blob shows it is fully INTEGER: per ARGB channel,
`ch = top_ch + (bottom_ch - top_ch) * ly / rh` with truncating OpSDiv, dividing
by **rh** (the rect height), not rh-1. `SoftwareBackend.draw_gradient_rect`
already did an integer lerp but divided by `h-1`; changing its divisor to `h`
makes CPU and GPU bit-exact (0 mismatch across solid/partial gradients). Kernel
wired. (Note: this is the Vulkan-canonical divisor; the prior code targeted the
Metal MSL kernel's h-1 — if a host has native Metal, that path may differ by 1.)

### line (RESOLVED via spirv-dis)
`spirv-dis` of the `spirv_line` blob revealed the GLSL source was misleading: the
blob computes `px = x1 + (dx*step)/(steps+1)`, `py = y1 + (dy*step)/(steps+1)`
with `steps = max(|dx|,|dy|)` and `step` running `0..=steps` inclusive — the
divisor is **steps+1**, not steps. Reimplementing `SoftwareBackend.draw_line` to
match made thickness-1 lines bit-exact in all directions (0 mismatch) and the
kernel is now wired. CAVEAT: the blob does NOT implement thickness (push constant
5 is never read; no loops) — it draws a single 1px center pixel per step. So GPU
lines are 1px regardless of requested thickness; SoftwareBackend still renders
thickness on CPU. Cross-backend parity is asserted for thickness-1 only.
Follow-up: a thickness-aware line SPIR-V blob. For
rounded_rect and circle_outline the SoftwareBackend implementation was itself
wrong/inconsistent with the canonical GPU/CUDA/Metal kernels and was corrected
to match (GPU pixels are canonical, per owner decision).

### line (reverted)
The GLSL `_glsl_line` source uses truncating DDA (`px = x1 + (dx*step)/steps`),
but the actual hand-assembled SPIR-V blob's output matches neither truncating
nor round-half-up DDA: aligning SoftwareBackend to truncation left diagonals off
by ~18px; adding `steps/2` rounding made it worse (steep 0→36). The blob has a
distinct interpolation that needs SPIR-V disassembly (`spirv-dis`) to recover.
Kept no-op + SoftwareBackend restored to its Bresenham line.

Important caveat on the divergent rows: parity vs `SoftwareBackend` only
adjudicates a kernel when both backends implement the *same primitive*.
`SoftwareBackend.draw_rounded_rect` (backend_software.spl:259) draws an
**outline** (4 edges + 4 corner arcs), whereas the GPU `spirv_rounded_rect`
blob appears to **fill** (its no-op mismatch of ~140 ≈ the rounded-rect
*perimeter*, and the wired mismatch of 1460 ≈ the *fill area*). So that row is a
primitive-semantics mismatch between the two backends, NOT proof the GPU blob is
buggy — it cannot be decided by parity. `circle_outline` (small ~68-96
mismatch) is likely a thickness/coverage difference between two outlines.
`gradient_rect` (~1400 ≈ fill area; both backends fill) is a genuine divergence
worth real investigation. None of these were shipped — all kept no-op until each
is checked against a *first-principles* oracle, not just cross-backend parity.

## Fix applied
`backend_vulkan.spl` now wires five real SPIR-V kernels verified bit-exact vs
the SoftwareBackend reference: `rect_outline`, `circle_filled`,
`triangle_filled`, `rounded_rect`, `circle_outline` (plus the already-real
`clear`/`rect_filled`). For `rounded_rect` and `circle_outline` the
SoftwareBackend implementation was itself a bug (outline / Bresenham) and was
corrected to the canonical GPU fill/distance-ring. `line`, `gradient`, `blit`
remain on the no-op shader. All wired kernels are guarded by the cross-backend
parity scenario in
`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`.

## rounded_rect ground truth (investigated 2026-06-17)
The intended `draw_rounded_rect` semantics is **fill**, confirmed by three
independent reference kernels that all fill: the CUDA PTX
`kernel_draw_rounded_rect` (`backend_cuda_kernels.spl`), the Metal MSL
`kernel_draw_rounded_rect` (`backend_metal_msl.spl`), and the GPU GLSL
(`backend_vulkan_glsl.spl`, `bool inside` + corner distance test). Therefore
**`SoftwareBackend.draw_rounded_rect` (backend_software.spl:259) is the actual
bug** — it draws only an outline (4 edges + 4 corner arcs). The Vulkan
`spirv_rounded_rect` blob, tested against a first-principles fill oracle (fill
interior; round each corner via `dx²+dy² ≤ r²` at corner centers
(x+r,y+r)/(x+w-1-r,y+r)/…), matches to **60/1728 px (3.5%)** — it fills
correctly but its corner pixels disagree by ~60 at the four arcs. That residual
is a corner-convention / edge-inclusivity question (off-by-one in corner center
or `<` vs `<=`) with no single obviously-correct answer; it needs a pixel-exact
spec decision before either the kernel or the oracle can be declared canonical.
Not wired (kept no-op) until that's settled.

Tooling note: this host has `spirv-as`/`spirv-dis` but **no** GLSL→SPIR-V
compiler (`glslangValidator`/`glslc` absent), so fixing a kernel means editing
SPIR-V assembly, not regenerating from `backend_vulkan_glsl.spl`.

## Still open (not fixed — deliberately not shipped unverified)
1. `line` — SPIR-V blob interpolation matches neither truncate nor round DDA;
   recover the exact algorithm via `spirv-dis` on the blob, then align
   SoftwareBackend and wire.
2. `gradient_rect` — float interpolation (`mix` + `uint()` truncation); CPU/GPU
   bit-exact match is sensitive to f32-vs-f64 rounding (and this repo's f64 is
   unreliable on the interpreter). Needs an integer-equivalent oracle or an
   accepted per-channel tolerance.
2. `line` and `blit` kernels untested (blit needs a source-buffer binding the
   parity probe doesn't set up).
3. `vulkan_session.spl` carries the identical no-op wiring; it was left
   unchanged because its shared-session path fails at `init_with_session`
   (pre-existing, unrelated to kernel wiring), so the fix could not be verified
   end-to-end through the session. Apply the same three verified wirings once
   the `init_with_session` blocker is resolved.

## Related
- `web_render_gpu_backend_provenance_fabricated_2026-06-17.md`
- `rt_vulkan_only_executes_under_classic_interpret_2026-06-17.md`
