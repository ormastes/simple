# BUG: engine2d CPU↔Metal primitive rasterization diverges (line/circle/rounded_rect)

Status: resolved (2026-06-05)

- id: engine2d-cpu-metal-primitive-raster-divergence
- date: 2026-06-03
- area: rendering / engine2d
- severity: medium
- status: resolved (2026-06-05)

## Resolution (2026-06-05)

All four primitives are now bit-exact CPU↔Metal with genuine GPU readback
(`gpu_frame_complete=true`), verified by the extended parity harness
(`line/circle/rounded_rect/triangle: MATCH mismatches=0/1024`):

- line: the MSL `kernel_draw_line` now replays the CPU `sw_bresenham` error loop
  per step (instead of a DDA division), visiting the same pixel set.
- circle outline: `kernel_draw_circle` replays the CPU midpoint loop (1D dispatch,
  thread = iteration) and emits the 8 symmetric pixels — keeps the 8-connected
  ring (a per-pixel distance annulus gaps near the diagonals).
- circle filled: both backends use the per-pixel distance test `dx²+dy² ≤ r²`;
  the CPU emits it as `isqrt(r²-dy²)` spans so it stays a fast hline fill.
- rounded_rect outline: `kernel_draw_rounded_rect` was a filled interior test
  (shape mismatch vs the CPU outline); it now draws the outline — straight edges
  plus midpoint corner arcs replayed to match `sw_corner_arc`.
- triangle: GPU dispatch enabled (`_dispatch_metal_triangle`); both backends use
  the same integer barycentric (edge-function) fill, so it is no longer a mirror
  tautology.

The parity gate (`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`)
and harness (`test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`)
now assert all of these scenes.

Because the harness clears-then-draws and both backends now share the new
formula for `circle_filled`/`triangle`, an all-black-vs-all-black buffer would
also report MATCH. An out-of-band absolute probe was run to rule that out:
filled-circle center == fill color and triangle centroid == fill color on BOTH
CpuBackend and MetalBackend (`gpu_frame_complete=true`), with the far corner ==
background. So MATCH is correct-vs-correct, not empty-vs-empty.

### Follow-up (out of scope here: CUDA, NVIDIA-host-only)

This change moved the CPU reference for `circle_filled` (now the `dx²+dy²≤r²`
distance test) and `triangle` (now integer barycentric). The CUDA PTX kernels:
- `kernel_draw_circle_filled` already uses the same distance test → now matches.
- triangle has no CUDA kernel → CUDA falls back to the (new) CPU mirror → matches.
- `kernel_draw_circle` (annulus) and `kernel_draw_rounded_rect` (filled interior)
  remain as they were and still differ from the CPU midpoint/outline — but this
  is a *pre-existing* CUDA-vs-CPU semantic mismatch (cuda_strict even asserts
  rounded_rect as a fill), not introduced by this fix. Aligning the CUDA kernels
  is tracked as separate follow-up work.

**Status (2026-06-12):** The two mismatched kernels are now formally annotated
with KNOWN PARITY NOTEs in `backend_cuda.spl` (`draw_circle` and
`draw_rounded_rect` methods). The ROCm backend has also received the equivalent
init-guard hardening (`last_probe` field, per-method `initialized` guards,
`read_pixels`/`present` null-pointer guard). PTX kernel realignment
(`kernel_draw_circle` → sw_midpoint, `kernel_draw_rounded_rect` → outline) is
the remaining open item and requires NVIDIA hardware to verify.

## Summary

The CPU (software) backend and the Metal GPU backend produce bit-identical
output for `clear`, `draw_rect_filled`, `draw_rect` (outline), and (after the
integer-lerp fix) `draw_gradient_rect`. The primitive-rasterization ops diverge
because the two backends use different algorithms.

Measured on a 32×32 scene with genuine GPU readback (`gpu_frame_complete=true`):

| op                   | mismatches | cause |
|----------------------|------------|-------|
| draw_line            | 24/1024    | CPU Bresenham vs Metal per-pixel line kernel |
| draw_circle (+filled)| 92/1024    | CPU midpoint vs Metal distance-field check |
| draw_rounded_rect    | 532/1024   | different corner rasterization |

`draw_triangle_filled` is not GPU-dispatched on Metal at all
(`backend_metal.spl` sets `gpu_frame_complete = false`), so it reads back the
CPU mirror and any "match" is a tautology — it must not be added to the parity
gate until a real GPU triangle kernel exists.

## Fix direction

Pick one canonical rasterization per primitive and make both backends follow it,
the same way `draw_gradient_rect` was canonicalized to the MSL integer lerp:

- line: match the MSL `kernel_draw_line` stepping to the CPU Bresenham (or vice
  versa) so both visit the same pixel set.
- circle: align the inclusion test (CPU midpoint vs MSL distance `<= r`).
- rounded_rect: align the corner inclusion test.
- triangle: add a GPU dispatch path (MSL `kernel_draw_triangle_filled` exists)
  so the comparison stops being a mirror tautology, then align the barycentric
  fill rule.

## Reproduce

```
src/compiler_rust/target/gui/debug/simple run build/metalcmp/moreops.spl   # ad-hoc
```

The shipped gate (`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`) only
asserts the bit-exact ops above; extend it per primitive as each is aligned.
