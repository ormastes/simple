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
`DrawIrCommand.computed_style`. Freestanding preserves the primary DrawIR
fields and pixels but loses this optional nested metadata through the wide
struct-in-array round trip, so the rescan returns zero materials.

Restoring pre-lowering derivation alone was insufficient: the resulting nested
provenance class is still lost later in the
layout → execution → cache → artifact chain.

## Source fix

- Layout/software results derive fallback from authoritative nodes/styles
  before DrawIR lowering.
- The WM adapter performs a final fail-closed recovery only when its own
  injected contract is present, the visible pixel count exactly matches the
  viewport, and the package's declared opaque fallback ARGB covers at least
  half of that viewport.
- The recovered SHA-256 covers the exact resolved background/foreground
  material tuple.
- An empty `System Console` regression covers the first-window QEMU shape.

No declaration-only fallback is accepted: if matching realized pixels are
absent, the downstream provenance gate still rejects the frame.

## Verification state

- Host entry compile: 254 compiled, 0 failed.
- MCP and LSP native packages: built and returned valid `initialize` replies.
- QEMU runtime: retry cap reached before the pixel-validated adapter fix could
  be exercised. A fresh session must run the canonical evidence wrapper once.
