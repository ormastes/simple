# Skia CPU backend records canvas transforms but never applies them at rasterization

Status: open, 2026-10-05. Lane: `work/rendering-skia-harden-20261005`
(worktree `wt/render-harden-20261005`).

## Finding

`SkCanvas.translate/scale/rotate/concat/set_matrix`
(`src/lib/skia/entity/canvas.spl:78-148`) all record `SetMatrix` ops and the
CPU backend replay faithfully tracks them into `CanvasState.transform`
(`src/lib/skia/backend/cpu/backend.spl:225-246`) -- but no draw op applies
that transform:

- `DrawRect` fills `op.rect` untransformed (`backend.spl:255-261`)
- `DrawRRect` fills `op.rect` untransformed (`backend.spl:263-269`)
- `DrawPath` rasterizes the raw path (`backend/spl:271-277`)
- `DrawImage` blits at integer `op.x/op.y` only (`backend.spl:279-295`)

So on the CPU backend every canvas transform is a silent end-to-end no-op:
record -> state -> discard. This is the rendering-side root of the Lane C
web-renderer finding "CSS transforms (`rotate(7deg)`) ignored"
(`doc/09_report/rendering_showcase_buffer_comparison_2026-10-03.md`).

## Secondary record-time loss

`concat()` and `set_matrix()` pack only (tx, ty, sx, sy) into the SetMatrix
`rect` slots and drop rotation/shear (`canvas.spl:96-143`, documented
"Lossy encoding" TODOs at lines 97-99 and 122-123). `rotate()` packs the
degree into `op.rx` (`canvas.spl:93`) but the replay never reads `rx` for
SetMatrix (`backend.spl:232-240` decodes only the rect slots), so even the
existing rotation carrier is dead on arrival.

## Impact

Any SkPicture using transforms renders identically to the untransformed
picture on the CPU backend. Chrome/Skia ground-truth comparisons that
include transforms fail by construction; showcase/web lanes that rely on
transformed draws cannot reach parity.

## Suggested directions

1. Apply `CanvasState.transform` at rasterization for DrawRect/DrawRRect
   (transformed quad fill), DrawPath (transform path vertices once, then
   existing AA fill/stroke), and DrawImage (inverse-map sampling).
2. Extend `SkPictureOp` with a full 3x3 (or tx/ty/sx/sy/rot/skew) matrix
   encoding so `concat`/`set_matrix` stop dropping components; keep the
   rect-slot encoding as the legacy decode path.
3. Honour `op.rx` rotation in the SetMatrix replay as an intermediate step
   so `canvas.rotate()` stops being a silent no-op before (1) lands.
4. Acceptance: the existing `transform_tree` scene in
   `test/03_system/gui/reftest/parity/reftest_spec.spl` should assert
   pixels, and a chrome-live-bitmap ground-truth case should cover a
   rotated rect.

## Implementation design (2026-10-05 continuation lane)

`Matrix3x3` (`src/lib/common/drawing/vector.spl:181-270`) is a full 3x3 f64
matrix with `mul` and `is_identity`, but no point mapping and no inverse;
`tx/ty/scale_x/scale_y` accessors are explicitly lossy (rotation/shear not
recoverable from four scalars).

Minimal-loss plan, in order:
1. Add `map_point(x, y)` (affine: m20=m21=0, m22=1 for all constructors) and
   `invert() -> Option` (2x2 determinant + translation back-substitution;
   singular -> None -> draw skipped) to `Matrix3x3`.
2. CPU replay (`backend/cpu/backend.spl:248-312`): per draw op, branch on
   `cur.transform.is_identity()` and keep today's fast path unchanged.
   Non-identity: DrawRect -> transform corners -> convex-quad scanline fill;
   DrawPath -> map path vertices once, then existing fill_path_aa/stroke_path;
   DrawImage -> inverse-map destination pixel centers to source UV
   (nearest first; bilateral sample_image_bilinear already exists).
   Clip stays device-space: intersect device-space quad bounds with
   `cur.clip` before scanning.
3. Record-time intermediate: honour `op.rx` as rotation degrees in the
   SetMatrix replay (today `rotate()` packs it and replay drops it), and add
   a `rotation_degrees()` accessor (atan2(m10, m00)) so `concat`/`set_matrix`
   stop dropping rotation until SkPictureOp grows a full-matrix encoding.
