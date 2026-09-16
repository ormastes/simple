# TODO: [gpu][P2] Make the resident-slice readback counter a real measurement or delete it

Status: CLOSED 2026-09-16 — the either/or was resolved by removal plus a
generation-rotate path.

Evidence (2026-09-16): `Engine2dVulkanResidentSliceReport.readbacks` (and the
arena field, its init, the slice-report copy, and the `framebuffer_readbacks=`
summary key) is removed from `src/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl`,
and the spec assertion `expect(arena.readbacks).to_equal(0)` is removed from
`test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d_spec.spl` — an
invariant by construction can no longer masquerade as a measurement. The
second half landed too: `Engine2dVulkanResidentArena.rotate_arena()` advances
`arena_generation` and clears the retained scene snapshot, and a new spec
("rotates to a second live generation and refuses the superseded one") proves
the stale-generation negative control now exercises a genuinely retired
generation instead of only a never-issued one. Spec result: 12/12 passed
(device-free, interpreter mode).

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

`Engine2dVulkanResidentSliceReport.readbacks` has no increment path anywhere, because the
resident path performs no readback at all. Asserting `readbacks == 0` documents intent but
cannot fail — an invariant by construction, not a measurement. The same applies to
`arena_generation`, fixed at 1 with no rotate path, so the stale-generation negative control
only ever proves "not 1 is refused".

Closing evidence: either a real readback path that increments the counter (so the assertion
can fail when the resident loop regresses), or removal of the field and its assertion, plus a
generation-rotate path that lets the negative control exercise a second live generation.
