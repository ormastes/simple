# nogc Engine2D `backend_lane` lacks shared `helpers_availability` — font-offload backend priority diverges from gc mirror

## Status
Open.

## Severity
Low — routing correctness only for font-offload backend *selection*. Operation-lane
tier routing (which operations run on the drawing vs processing lane) is fully
reconciled between the mirrors; the residual divergence is limited to *which GPU
backend* is chosen for a font-offload candidate set that includes `qualcomm` or
`intel`.

## Summary
The gc mirror `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl` scores backend
candidates through the shared `std.gpu.engine2d.helpers_availability` module
(`backend_canonical_name` / `backend_canonical_priority` /
`backend_full_preference_order` / …). Its
`engine2d_backend_lane_preferred_font_offload_candidate` uses
`backend_canonical_priority`, which tiers `qualcomm` and `intel`.

The nogc copy `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl` has **no**
`helpers_availability` module in its tree. It reuses a local hardcoded
`engine2d_backend_lane_full_preference_order()`
(`["metal","cuda","rocm","vulkan","directx","opencl","opengl","webgpu","cpu_simd","software","cpu"]`)
which omits `qualcomm` and `intel`. Its
`engine2d_backend_lane_preferred_font_offload_candidate` delegates to the general
`engine2d_backend_lane_preferred_candidate(...)`, so a `qualcomm`/`intel` candidate
scores priority `99` and is dropped from font-offload selection.

Note `engine2d_font_offload_backend_order()` (which *does* list qualcomm/intel) is
identical in both copies but is not consulted by the nogc candidate picker.

## Reproduce
Call `engine2d_backend_lane_preferred_font_offload_candidate(["qualcomm"])`:
- gc: returns `"qualcomm"`.
- nogc: returns `""` (dropped).

## Fix options
1. Introduce a `helpers_availability` module under `nogc_async_mut/gpu/engine2d/`
   (or share the existing one across tiers) and route the nogc candidate picker
   through `backend_canonical_priority`, matching gc exactly. Preferred — removes
   the divergence and the hardcoded order.
2. Minimal: have the nogc font-offload candidate picker score via the local
   `engine2d_font_offload_backend_order()` (already qualcomm/intel-aware) instead
   of `full_preference_order`. Contained, but the priority *basis* still differs
   from gc's general canonical order, so it is not a true match.

## Context
Recorded during the nogc↔gc engine2d mirror reconciliation pass (2026-07-06).
Operation-lane tier routing (`vector_font`/`vector_glyph`/`glyph_raster`/
`glyph_blit`/`bitmap_*` → processing lane) was ported to nogc in the same pass;
this backend-priority coupling was left as an explicit divergence rather than
half-ported. Marked at the call site in
`src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl`.
