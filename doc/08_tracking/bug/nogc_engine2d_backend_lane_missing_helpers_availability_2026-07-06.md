# nogc Engine2D `backend_lane` lacks shared `helpers_availability` — font-offload backend priority diverges from gc mirror

## Status
**FIXED 2026-08-17.** Root cause was worse than this doc described — see
"Reproduction and fix (2026-08-17)" below.

## Reproduction and fix (2026-08-17)

The doc predicted `engine2d_backend_lane_preferred_font_offload_candidate(["qualcomm"])`
would return `""`. It does not — it does not return at all. A partial port had
already applied fix option 2 (the picker walks the qualcomm/intel-aware
`engine2d_font_offload_backend_order()`), but it copied the gc mirror's body
verbatim, including its call to `backend_canonical_name` — a function defined
**only** in `src/lib/gc_async_mut/gpu/engine2d/helpers_availability.spl`, a module
that has no nogc counterpart and is not imported by the nogc file. There are no
`use` statements in `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl` at all.

RED, `bin/simple run` calling the exported function:

```
error[E1002]: function `backend_canonical_name` not found
  = help: check the function name or import the module that defines it
```

So the entire nogc font-offload picker was unreachable, not merely mis-tiered.

**Root cause:** `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl:128`.

**Fix:** call the file's own `_engine2d_backend_canonical_name` (line 86) instead
of the gc-only `backend_canonical_name`. One line; no new module, per fix option 2.

GREEN, same probe:

```
qualcomm -> [qualcomm]
intel -> [intel]
nvidia -> []
```

`nvidia -> []` is correct and matches the gc mirror: gc's `backend_canonical_name`
does not map `nvidia` to `cuda` either, so it is absent from the font-offload
order and is dropped on both sides.

**Residual, deliberately not fixed (out of scope for this row):** the nogc
`_engine2d_backend_canonical_name` is a much smaller alias table than gc's — it
lacks `native`/`platform_native` -> `baremetal`, `virtio` -> `virtio_gpu`, the
`d3d11`/`dx11`/`dx12` spellings, `dxvk`/`vkd3d` -> `directx-on-vulkan`,
`simd_cpu` -> `cpu_simd`, and gc's `.trim().lower()` normalization. That is a
separate mirror divergence in *alias* handling, not in font-offload selection.

**Specs:**
- reproducing: `test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.spl`
- similar-bug detection: `test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_mirror_symbol_reachability_spec.spl`
  — calls *every* exported function of the nogc module, because a gc-only symbol
  smuggled in by a partial port is invisible until that one entry point is
  invoked; the module loads fine and every other export works.

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

## Triage 2026-08-17 (lane m7c_lib_async) — divergence still LIVE

`grep -c helpers_availability`:
`src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl` -> **0**;
`src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl` -> **1**.
The mirror divergence this doc records is unchanged. Left unfixed deliberately:
it is an enhancement (adding a backend-selection helper to the nogc lane), not a
silently-wrong-result defect, and closing it needs GPU backends this host does
not have to validate against.
