# Vulkan Raster Kernels No-op / Divergent vs CPU Reference - 2026-06-17

## Severity
P1 (partially fixed — 6 of 10 kernels wired and verified as of 2026-06-17).
Several Engine2D Vulkan primitives silently rendered nothing (dispatched a no-op
SPIR-V shader) despite real validated kernels being available. `gradient_rect`
has now been reconciled against a first-principles oracle and wired (see
"Reconciliation 2026-06-17"); `line`, `circle_outline`, `rounded_rect`, and
`blit` remain no-op for the documented algorithm-class / semantics reasons.

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

## Verification matrix (real GPU blob vs FIRST-PRINCIPLES oracle, 64x48)
Measured 2026-06-17 by temporarily wiring every real blob, dispatching it on a
live device (3 Vulkan devices present under the classic interpreter), reading the
framebuffer back, and comparing against an *independent* oracle (not the GPU
compared to itself, not cross-backend equality alone). Probe: a clean-room
Bresenham/DDA/distance-ring/integer-lerp oracle in pure Simple.

| primitive       | status                                                        |
|-----------------|---------------------------------------------------------------|
| clear           | wired, correct (0 mismatch)                                   |
| rect_filled     | wired, correct (0)                                            |
| rect_outline    | wired, bit-exact (0)                                          |
| circle_filled   | wired, bit-exact (0) — per-pixel distance disk == CPU disk    |
| triangle_filled | wired, bit-exact (0) — barycentric == CPU                     |
| **gradient_rect** | **RECONCILED + WIRED** — blob was integer-lerp ÷rh; SPIR-V divisor fixed to max(rh-1,1); now 0 vs the endpoint-exact oracle AND 0 vs SoftwareBackend (full/offset/h=1/h=2) |
| line            | no-op — blob is exactly truncating DDA ÷(steps+1) (bit-exact to that oracle across all 5 slopes); drops the end point and, even fixed to ÷steps, is DDA not the contract's Bresenham (vsBresenham=31 shallow, 17 steep) |
| circle_outline  | no-op — distance-ring, 96px off a nearest-int ring oracle; not the contract's Bresenham midpoint |
| rounded_rect    | no-op — a correct FILL (60px corner residual vs a quarter-disk fill oracle, fills 1504 px) but the API contract is outline-only |
| blit            | no-op — needs a source-buffer binding the parity probe does not set up |

**6 of 10 kernels are wired and verified** (clear, rect_filled, rect_outline,
circle_filled, triangle_filled, gradient_rect). The remaining 4 are
fundamentally algorithm-class divergent from the engine's SoftwareBackend
(Metal-bit-exact) contract and need a Bresenham-class SPIR-V rewrite or a
per-primitive semantics decision — NOT a SoftwareBackend change.

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

### gradient_rect (SUPERSEDED — see "Reconciliation 2026-06-17" above)
[Historical note, kept for the spirv-dis finding.] `spirv-dis` of the
`spirv_gradient_rect` blob showed it is fully INTEGER: per ARGB channel,
`ch = top_ch + (bottom_ch - top_ch) * ly / rh` with truncating OpSDiv, dividing
by **rh** (the rect height). The prior note proposed making the two backends match
by changing *SoftwareBackend's* divisor to `h` — that was REJECTED: it would
degrade the Metal-bit-exact CPU contract (endpoint-exact `/(h-1)`) and break
`engine2d_primitives_spec`. The correct fix (applied 2026-06-17) edits the GPU
blob's SPIR-V divisor from `rh` to `max(rh-1, 1)` so the GPU matches the
endpoint-exact CPU contract instead. SoftwareBackend is untouched.

### line (characterized — NOT wired; see "Still open" #1)
`spirv-dis` + the 2026-06-17 oracle probe confirm the `spirv_line` blob is exactly
truncating DDA: `px = x1 + (dx*step)/(steps+1)`, `py = y1 + (dy*step)/(steps+1)`
with `steps = max(|dx|,|dy|)` and `step` running `0..=steps` inclusive — divisor
**steps+1** (verified bit-exact to a `÷(steps+1)` DDA oracle across
horizontal/vertical/45°/shallow/steep). It drops the end point (should be ÷steps)
and the blob ignores thickness (push constant 5 unused). The earlier note here
claimed `SoftwareBackend.draw_line` was "reimplemented to match and wired" — that
was REVERTED: matching a truncating DDA degrades the Metal-bit-exact Bresenham CPU
contract. The blob stays no-op until it implements Bresenham (or a DDA-divergence
policy is adopted). SoftwareBackend is untouched.

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

## Fix applied (current)
`backend_vulkan.spl` wires six real SPIR-V kernels: `clear`, `rect_filled`,
`rect_outline`, `circle_filled`, `triangle_filled`, and `gradient_rect` (the last
reconciled 2026-06-17 by the SPIR-V divisor fix). `line`, `circle_outline`,
`rounded_rect`, and `blit` remain on the no-op shader. `SoftwareBackend` is
NOT modified (an earlier attempt that degraded it to match the divergent blobs was
reverted — it broke `engine2d_primitives_spec`). Wired kernels are guarded in
`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl` by an
independent first-principles oracle (and a SoftwareBackend cross-check where the
CPU implements the same algorithm).

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

## Reconciliation 2026-06-17 (first-principles oracle)
`gradient_rect` is fully reconciled and wired. The blob's only divergence was the
lerp divisor: it computed `ch = top + (bot-top)*ly/rh` (÷ rect height) so the
bottom row landed at `top + (bot-top)*(rh-1)/rh`, never the bottom color. The
fix edits the SPIR-V (spirv-as round-trip, spirv-val clean): inserts
`t = rh-1; t = max(t,1)` (`OpISub` + `OpSLessThan` + `OpSelect`) and redirects the
four channel `OpSDiv`s to `t`. Result: 0 mismatch vs the endpoint-exact
integer-lerp oracle and 0 vs SoftwareBackend across full/offset/h=1/h=2.
Guarded by a dedicated first-principles `it` in
`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
(asserts top row == top, bottom row == bottom, plus the per-pixel oracle and a
SoftwareBackend cross-check). `engine2d_primitives_spec` stays 24/0 (SoftwareBackend
untouched).

## Still open (not fixed — deliberately not shipped unverified)
1. `line` — blob is exactly truncating DDA ÷(steps+1) (verified bit-exact to that
   oracle across horizontal/vertical/45°/shallow/steep). Two issues: it drops the
   end point (÷(steps+1) instead of ÷steps), and DDA ≠ the engine's Bresenham
   contract even with the divisor fixed (matches only axis-aligned + 45°). To wire
   it, either author a Bresenham-midpoint closed-form line in SPIR-V, or adopt an
   explicit "Vulkan line is DDA, may differ from CPU Bresenham" divergence policy.
2. `circle_outline` — distance-ring blob, 96px off a nearest-int distance-ring
   oracle and not the Bresenham midpoint the CPU uses. Needs `spirv-dis` to pin its
   exact ring threshold, then either a Bresenham SPIR-V rewrite or a divergence
   policy.
3. `rounded_rect` — the blob is a correct FILL (60px corner-convention residual vs
   a quarter-disk fill oracle), but `SoftwareBackend.draw_rounded_rect` is an
   OUTLINE. This is a primitive-semantics decision (fill vs outline; CUDA/Metal/GLSL
   reference kernels all fill), not a bug fix — must be settled by the API owner
   before wiring either side.
4. `blit` — needs a source-buffer binding the parity probe does not set up; verify
   via `draw_image` with a bound source once a binding harness exists.
5. `vulkan_session.spl` carries the identical no-op wiring; it was left unchanged
   because its shared-session path fails at `init_with_session` (pre-existing,
   unrelated to kernel wiring). Apply the same verified gradient wiring once the
   `init_with_session` blocker is resolved.

## NO-OP symptom resolved via emu composition (2026-07-06)

The user-visible **NO-OP** half of this bug — `draw_line`, `draw_circle`
(outline), and `draw_rounded_rect` dispatching a validated *empty* SPIR-V shader
and writing ZERO pixels while still setting `dirty=true` — is fixed in
`backend_vulkan.spl`. Those three methods no longer dispatch their no-op
pipeline; they now render **real device pixels** by composing GPU
`draw_rect_filled` dispatches through the bit-exact `emu_draw_line` (Bresenham),
`emu_draw_circle` (midpoint outline), and `emu_draw_rounded_rect`
(`backend_emu.spl`). Those emu helpers implement exactly the standard
Metal-bit-exact algorithms `SoftwareBackend` uses, so the Vulkan output is now
bit-exact with the CPU reference — no `SoftwareBackend` change, no SPIR-V
authoring, no runtime/seed rebuild. The `pipe_line`/`pipe_circle_outline`/
`pipe_rounded_rect`/`pipe_blit` pipelines are still compiled/validated/destroyed
(uniform lifecycle) but are no longer dispatched.

This does NOT resolve "Still open" #1-3: reconciling the dedicated GPU SPIR-V
blobs (`spirv_line` truncating-DDA, `spirv_circle_outline` distance-ring,
`spirv_rounded_rect` fill-vs-outline) with the engine contract — a
Bresenham-class SPIR-V rewrite or a per-primitive semantics decision — remains
the open work if single-dispatch GPU raster (vs the current multi-dispatch emu
composition) is desired for these three primitives. #4 (`blit`) and #5
(`vulkan_session.spl`) are likewise unchanged.

## Related
- `web_render_gpu_backend_provenance_fabricated_2026-06-17.md`
- `rt_vulkan_only_executes_under_classic_interpret_2026-06-17.md`
