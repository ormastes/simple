# kernel_draw_rounded_rect (Metal) drew a stale OUTLINE — CPU-vs-Metal parity DIVERGE

## Status
Fixed (2026-07-07).

## Severity
High — CPU-vs-Metal bit-exactness regression. Any filled rounded-rect GUI
element (buttons, cards, pills, panels) rendered through the Metal backend
painted only the border + thin corner rings instead of a solid shape, while
the CPU/software backend painted a correct fill — a visible content
divergence between the two render paths, not just a perf/architecture
difference.

## Summary
`kernel_draw_rounded_rect` (`src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl`)
was written (design W-phase, GPU offload work) to be "bit-exact with the CPU
reference" — but the CPU reference it was matched against was the
*pre-2026-07-06* `SoftwareBackend.draw_rounded_rect`, which itself had a bug:
it drew only the four straight edges + four midpoint corner-arc RINGS (an
OUTLINE), not a FILL. See
`doc/08_tracking/bug/engine2d_software_rounded_rect_draws_outline_not_fill_2026-07-06.md`.

When that CPU-side bug was fixed on 2026-07-06 (`SoftwareBackend.draw_rounded_rect`
now delegates to `emu_draw_rounded_rect`, a genuine fill: middle band + two
side bands + four FILLED corner arcs), the Metal kernel was never updated —
it kept replaying the old outline algorithm (1D dispatch, thread `k` covers
edge pixel `k` plus a replayed corner-arc-ring iteration `k`). This turned a
previously-passing "both sides draw the same (buggy) outline" parity check
into a real content divergence: CPU now fills, Metal still outlines.

## Evidence
`SIMPLE_BIN=bin/simple sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`
on a 32x32 fixture, before this fix:

```
rounded_rect: DIVERGE mismatches=512/1024 gpu_ok=true first_idx=100 cpu=4278190080 metal=4294967295
```

(cpu=`0xFF000000` background, metal=`0xFFFFFFFF` fill color at that index —
exactly the outline-vs-fill divergence class, same as the CPU-side bug's
604/2304-pixel mismatch on its own fixture.)

## Root cause
`kernel_draw_rounded_rect`'s doc comment and body were never revisited when
the CPU oracle it targets changed shape (outline -> fill) on 2026-07-06. The
kernel is data — MSL source embedded as a Simple string literal
(`_engine2d_msl()`) — so nothing in the type system flags "the CPU function
this kernel was written to match has since changed."

## Fix
Rebuilt `kernel_draw_rounded_rect` (2D dispatch over the `[0,w) x [0,h)`
bounding box, matching `kernel_draw_rounded_rect_outline`'s dispatch shape)
to replay `emu_draw_rounded_rect`'s exact FILL algorithm:
- Middle vertical band (`lx` in `[r, w-r)`, any row) — one `blend_src_over`.
- Left/right side bands (`ly` in `[r, h-r)`, near columns) — one `blend_src_over`.
- Four corner arcs — a new `_rr_corner_arc_blend` helper that replays
  `_emu_corner_arc`'s exact midpoint-circle recurrence (decision boundary
  `d < 0`, matching `backend_emu.spl`, which is a *different* boundary than
  the `d <= 0` the outline path's `_rr_ring_hit`/`sw_corner_arc` use — the
  fill and outline corner-arc algorithms are independent) and blends `color`
  over the destination once per per-iteration span hit.

**Non-obvious correctness requirement (alpha blending):** an initial version
tried a per-region-exclusive kernel — classify each pixel into exactly one
of {middle band, side band, corner arc}, blend once. That version matched
CPU on every opaque-color case but DIVERGED on semi-transparent fills
(confirmed via an independent Simple-formula replica in
`engine2d_shared_raster_parity_spec.spl`, 72/600 then 52/600 mismatches
across two attempted region models). Root cause: CPU's `emu_draw_rounded_rect`
issues **seven** `core.draw_rect_filled` calls (3 band rects + 4 corner
arcs), and their pixel footprints **overlap at the seams** — e.g. a corner
arc's first midpoint iteration (`py=0`) draws its span at the arc-center
row, which is the adjoining side band's own first row, so that row gets
blended by BOTH the band rect and the corner arc. For an opaque color this
is a harmless redundant overwrite (raw-store semantics collapse repeats);
for `alpha<255` each blend re-composites over the prior result, which is
NOT idempotent. The final fix replays all seven primitives in CPU's exact
order per pixel (`kernel_draw_rounded_rect`'s body), blending every hit —
the only model proven bit-exact against the CPU oracle, including alpha.

Also registered `draw_rounded_rect` in `backend_capability.spl`
(`OP_DRAW_ROUNDED_RECT`) and wired it into `MetalBackend.capability()`
(gated on `pipe_rounded_rect != 0`, same "device present AND pipeline
actually compiled" honesty signal as `draw_gradient_rect`), so
`capability().is_accelerated("draw_rounded_rect")` reports the real GPU
dispatch state instead of leaving the op unrepresented.

## Verification
- `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`: `rounded_rect`
  now `MATCH mismatches=0/1024 gpu_ok=true` (was `DIVERGE mismatches=512/1024`).
- `scripts/check/check-engine2d-gpu-offload-evidence.shs`: new `rounded_rect`
  row, `MATCH pixels=3072 source=device_readback`, real Metal checksums
  `cpu_checksum=1614395301 metal_checksum=1614395301` (equal), covering a
  radius-clamp ("stadium") corner, an off-framebuffer-edge clip, and an
  alpha-blended fill (`0x80FFFFFF`) — full gate: `pass (cpu-metal-bitexact-device-readback)`.
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`:
  new context "Rounded-rect FILL parity fix (2026-07-07)" — 5 new `it`
  blocks (original bug-doc fixture, radius==min(w,h)/2 clamp, narrow-strip
  clamp-on-h, semi-transparent alpha blend, radius=0 plain-rect) pin an
  independent Simple-level replica of `kernel_draw_rounded_rect`'s formula
  against `SoftwareBackend.draw_rounded_rect`. All 36 examples in the file
  pass (was 35 passed + this suite not yet present).
- `scripts/check/check-ui-backend-isolation.shs` and
  `scripts/check/check-cpu-hotloop-idiom.shs`: no new violations introduced
  by this change (hotloop: 393 baseline == 393 current, 0 new; isolation:
  the one flagged new-vs-baseline entry, `src/app/cli/bootstrap_main.spl`,
  reproduces identically on the unmodified base commit — pre-existing,
  unrelated to this fix).
