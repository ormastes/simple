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

| primitive       | mismatches | verdict                      |
|-----------------|-----------:|------------------------------|
| clear           | 0          | already real, correct        |
| rect_filled     | 0          | already real, correct        |
| rect_outline    | 0          | **fixed** (now wired, exact) |
| circle_filled   | 0          | **fixed** (now wired, exact) |
| triangle_filled | 0          | **fixed** (now wired, exact) |
| circle_outline  | 96/68      | divergent — kept no-op       |
| rounded_rect    | 1460       | divergent — kept no-op       |
| gradient_rect   | 1400       | divergent — kept no-op       |
| line            | untested   | kept no-op                   |
| blit            | untested   | kept no-op (needs src binding)|

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

## Fix applied (this change)
`backend_vulkan.spl` now wires the three verified-bit-exact kernels
(`rect_outline`, `circle_filled`, `triangle_filled`) to their real SPIR-V; the
remaining kernels stay on the no-op shader, explicitly commented, until each is
fixed and re-verified. Guarded by the cross-backend parity scenario in
`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`.

## Still open (not fixed — deliberately not shipped unverified)
1. `circle_outline`, `rounded_rect`, `gradient_rect` SPIR-V blobs diverge from
   `SoftwareBackend`. First decide the intended primitive semantics
   (`draw_rounded_rect` = fill or outline? — the two backends currently
   disagree) and build a first-principles oracle, then debug each kernel's
   GLSL→SPIR-V (`backend_vulkan_glsl.spl`) push-constant layout / predicate,
   wire, and verify. Do NOT use cross-backend parity alone where the backends
   implement different primitives.
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
