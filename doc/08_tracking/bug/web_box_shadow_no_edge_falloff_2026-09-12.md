# box-shadow produced a hard band with no edge falloff (2026-09-12)

**Status:** FIXED.
**Component:** Engine2D software/emulation backend.

## Defect

`src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl:231-240`
(`emu_draw_shadow_rect`) filled an **opaque** rect expanded by `blur_r` with
`draw_rect_filled`, then called `emu_draw_blur_rect` on that same, already-filled
area. Blurring a uniformly filled region returns the same uniform region, so the
result had zero edge gradient by construction. Chrome ramps 234→233→229→223
outside a card edge; Simple emitted a hard uniform band (216,221,235).

The blur radius was plumbed correctly end to end (`paint_layout:1952` →
`draw_ir_box_effects.spl:158,219,249` → `:542-574` `draw_shadow_rect` →
`backend_emu_adv.spl:231`), so this was a rasterizer defect, not a parse defect.

## Fix

Rasterize the shadow as an **alpha coverage field**, blur the coverage, then
composite the shadow colour through it — the standard approach.

A box blur of an axis-aligned rect is exactly **separable**, so the 2D coverage
is the outer product of two 1D profiles and no 2D mask is ever materialized: the
cost is O(w + h) profile work plus one composite pass over the padded region.
Three box passes of radius `blur_r/2` approximate a gaussian with
σ = blur_r/2, which is the CSS definition (a box-shadow blur radius is 2σ).
The region is padded by `2*blur_r` so the whole falloff (half-support ≈ 1.5·blur_r)
fits.

## Deviation from the requested oracle — read this

The task brief asked for "a pixel at blur_r outside the rect edge has alpha ≈
0.5·shadow alpha". That is **not** the CSS/Chrome definition, and implementing it
would displace every shadow halo by `blur_r` relative to Chrome — the opposite of
the goal. CSS puts the 50 % coverage crossing **on the un-expanded rect edge**.
The implementation and the spec follow CSS. The brief's other two oracles are
kept verbatim (centre == shadow colour; 3·blur_r outside == background).

Measured on the spec fixture (120x60 box, blur 20, black shadow, white page):
centre `(1,1,1)`, one pixel outside the top edge `133` (= 0.52·255), 60 px
outside `255`.

## Specs

`test/unit/browser_engine/box_shadow_falloff_spec.spl` (mirrored into
`test/01_unit/browser_engine/`), 4 examples, all absolute pixel oracles:

- **Reproducing** — AC-4 "coverage decreases monotonically away from the edge (no
  hard band)": three samples at 4, 8 and 15 px outside must strictly increase
  toward the background. The old uniform band made all three equal.
- **Generalization** — AC-1 centre == shadow colour (through a `background:transparent`
  box), AC-2 the 50 % crossing sits on the edge, AC-3 three blur radii out is pure
  background.

## Blast radius

`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` is
unchanged by this fix — measured on the committed tree (shadow fix present,
corner fix reverted): `40 executed, 39 passed, 1 failed`, the single failure
being the pre-existing `draw_line (thick)` row, identical to the baseline run on
unmodified files. So are `backend_software_primitives_spec.spl`,
`cpu_sw_primitive_readback_spec.spl` and `engine2d_primitives_spec.spl` (all green).

## Not done

Outer shadows are not clipped to the outside of the border box, as CSS requires;
a transparent box therefore shows the shadow through its interior (this is what
AC-1's fixture exploits). Inset shadows are untouched.
