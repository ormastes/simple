# Engine2D Straight-Alpha Blend on Transparent Destinations

Status: fixed (pure-Simple, C native SIMD, and hosted Rust paths)

`std.gpu.engine2d.color.blend` computes RGB as if the destination were opaque
while separately computing src-over alpha. For 50% straight-alpha white over
transparent black it returns approximately `0x80808080`; straight-alpha
src-over requires `0x80FFFFFF`. A later composite multiplies coverage again,
darkening antialiased vector-font fringes and any other translucent image drawn
over a transparent framebuffer.

Opaque destinations retain the established result, so current font scenarios
with an opaque clear do not discriminate this bug. Fix the shared blend owner,
then update CPU/GPU parity anchors and add an absolute transparent-destination
oracle before claiming transparent-surface font correctness.

## Resolution (2026-07-17)

Root cause: `std.gpu.engine2d.color.blend()` (src/lib/gc_async_mut/gpu/engine2d/color.spl)
computed `out_rgb = (src_rgb*sa + dst_rgb*(255-sa)) / 255` unconditionally —
i.e. it treated `dst_rgb` as if `dst` were always opaque (implicitly assuming
`da=255`) and never unpremultiplied the result by the true output alpha. For
50% straight-alpha white over transparent black (`dst=0x00000000`) this gave
`0x80808080` instead of the correct `0x80FFFFFF`.

Fix: composite in premultiplied space and unpremultiply by the resulting
output alpha:
```
inv_a       = 255 - sa
dst_weight  = (da * inv_a) / 255       # dst's premultiplied contribution
out_a       = sa + dst_weight
out_rgb     = (src_rgb*sa + dst_rgb*dst_weight) / out_a
```
When `da=255` (opaque dst) this reduces exactly to the old/established
formula, so opaque-destination behavior is unchanged (verified byte-identical
in tests). When `da=0` (transparent dst) it reduces to `out_a=sa`,
`out_rgb=src_rgb` per the doc's expected math.

Files changed:
- `src/lib/gc_async_mut/gpu/engine2d/color.spl` — fixed `blend()`, the shared owner.
- `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl` — fixed the pure-Simple
  scalar reference path `_scalar_blend_row()` identically. The C native SIMD
  row kernel and hosted Rust runtime/interpreter paths now use the same formula,
  including transparent and translucent destinations.
- `test/01_unit/lib/gpu/engine2d/engine2d_color_spec.spl` (+ duplicate at
  `test/unit/lib/gpu/engine2d/engine2d_color_spec.spl`) — added a `blend`
  context: opaque-over-opaque, transparent-over-any, semi-over-opaque
  (established case unchanged), any-over-transparent (bug repro, asserts
  `0x80FFFFFF` exactly), semi-over-semi.
- `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` — verifies exact
  transparent/translucent results and native/scalar row parity.
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` —
  updated the stale CPU/GPU parity anchor from `0x101F2F3F` (the old buggy
  value for `0x01020304` src-over `0x10203040` dst, da=0x10) to the correct
  `0x101E2D3C`.

Verification: the strict pure-Simple native `simd_kernels_spec.spl` executable
passes 27 examples with 0 failures. The focused hosted Rust runtime and
interpreter suites pass 5 and 1 tests respectively, and the C SIMD kernel,
span, tagged-blend, and row-scheduling checker passes.
