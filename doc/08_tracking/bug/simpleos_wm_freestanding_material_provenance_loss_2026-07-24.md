# BUG: freestanding WM loses realized glass fallback provenance

**Status:** source fix implemented; fresh QEMU verification pending
**Severity:** high
**Component:** Simple Web layout → Engine2D cache → shared WM frame
**Found:** 2026-07-24

## Symptom

The SimpleOS guest renders the Aetheric package through Engine2D, but the
post-render frame reports:

`fallback=none material= theme=aetheric_dark`

The strict evidence gate therefore rejects the frame before presentation.
Guest evidence is retained in:

- `doc/09_report/wm_glass_theme_qemu_provenance_v2_2026-07-24.md`
- `doc/09_report/wm_glass_theme_qemu_provenance_v3_2026-07-24.md`

Both runs reached the validated 3840×2160 ARGB scanout and registered the
pinned Noto Sans Mono font before failing closed on provenance.

## Root cause

Commit `e87aa6430e` moved fallback derivation from authoritative parsed
nodes/computed styles to a second scan over
`DrawIrCommand.computed_style`, which was replaced with direct computed-style
derivation.

The remaining failure was real CSS state, not lost provenance transport.
`apply_decls` retained `bg_layers_raw_v` from an earlier multilayer
`background:` shorthand even when the later WM override specified
`background-image:none`. Scalar gradients were cleared, but the radial/raw
layer list survived. The renderer therefore correctly refused to claim that
the solid material had been realized.

Disassembly of the v3 freestanding ELF confirms that the provenance class is
preserved at every layout, execution, cache, and artifact boundary; the prior
nested-class-loss diagnosis was incorrect.

## Source fix

- Layout/software results derive fallback from authoritative nodes/styles
  before DrawIR lowering.
- `background-image:none` now clears both scalar gradients and retained raw
  multilayer background state.
- No adapter-side pixel heuristic manufactures provenance; the computed CSS
  must prove the opaque named material with no remaining image layers.
- A focused radial/multilayer cascade regression checks software and Engine2D
  results plus the material hash.
- An empty `System Console` regression covers the first-window QEMU shape.

No declaration-only fallback is accepted: if matching realized pixels are
absent, the downstream provenance gate still rejects the frame.

## Verification state

- Host entry compile: 254 compiled, 0 failed.
- MCP and LSP native packages: built and returned valid `initialize` replies.
- QEMU runtime: retry cap was reached before the CSS-state fix could be
  exercised. A fresh session must run the canonical evidence wrapper once.
