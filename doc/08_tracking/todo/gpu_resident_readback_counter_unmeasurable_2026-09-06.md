# TODO: [gpu][P2] Make the resident-slice readback counter a real measurement or delete it

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
