# BUG: engine2d CPU↔Metal primitive rasterization diverges (line/circle/rounded_rect)

- id: engine2d-cpu-metal-primitive-raster-divergence
- date: 2026-06-03
- area: rendering / engine2d
- severity: medium
- status: open

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
