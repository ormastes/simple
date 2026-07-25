# Web HTML render: paint-budget expiry under interpreter yields uniform frame (compiled-lane gate confirmed)

- **Date:** 2026-07-25
- **Lane:** web showcase, interpreted (`bin/simple run`)
- **Status:** root-caused; detection honest; fix = compiled lane (perf), not budget inflation

## Symptom
`web_standards_showcase` headless: `status=fail reason=blank-or-uniform pixels=172800
nonzero=172800` — every pixel painted, zero content (canvas background only).

## Root cause (two layers)
1. **Crash (fixed):** `font_registry.spl:507` used `blob as [i64]` — an element-wise
   `[u8]`→`[i64]` array cast the self-hosted interpreter rejects; aborted every
   interpreter-mode HTML render before output. Fixed by explicit loop
   (`_u8_blob_to_i64_array`), commit `c6469f6c74`.
2. **Uniform fill:** `simple_web_html_layout_renderer.spl` enforces a wall-clock paint
   budget (`WEB_RENDER_BUDGET_MS` = 10000, effective ≈10.8s at 480x360).
   `_web_budget_expired()` breaks the paint loops once the deadline passes; the
   canvas-background command is prepended before content, so an expired budget leaves a
   fully-painted, fully-uniform frame. Interpreted parse/style/layout of the HTML engine
   is orders of magnitude slower than the budget: with
   `SIMPLE_WEB_RENDER_BUDGET_MS=600000` the render was still inside layout after 15 min
   (480x360), so no practical budget completes interpreted.

## Correction 2026-07-25 — "no fake-pass" was WRONG for the host-WM composite lane

The claim below that evidence checks "already catch this honestly" holds only for the
standalone web lane, where the measured frame *is* the web frame. It does **not** hold
for `web x host-WM` (`examples/06_io/ui/wm_web_standards_showcase_gui.spl`), which
scored a clean `status=pass reason=ok pixels=510656 nonzero=505175
checksum=1480567703` while rendering **nothing**.

Cause: `blank-or-uniform` was computed on `present_pixels` — the composite *after*
`blit_child_frame_pixels`, which already carries WM chrome (titlebar, borders,
taskbar, desktop). The chrome alone satisfies `varied` and `nonzero`, so the gate can
never see a blank child. Measured on the produced PPM:

| frame | size | distinct colours |
|---|---|---|
| child (the actual web render) | 480x270 | **1** — fully uniform |
| composite (what the gate measured) | 808x632 | 10 — all WM chrome |

For contrast, the widget cell's child frame has 13 distinct colours, so that cell's
PASS is real; this masking only turned a *blank* child into a green cell.

Fixed by gating the child frame separately (`reason=child-frame-uniform`) in the web
wrapper. **`wm_widget_showcase_gui.spl` and `wm_graphics_2d_showcase_gui.spl` still
have the unguarded composite-only check** and would mask the same way the moment their
child goes blank — they pass today on content, not on gate strength.

## Resolution
- Standalone web lane catches this honestly (`blank-or-uniform`); the host-WM
  composite lane did NOT — see the correction above.
- `SIMPLE_WEB_RENDER_BUDGET_MS` is the explicit override lane for debugging; default
  stays 10s (sized for compiled execution) — do not inflate it to mask the perf gap.
- Web showcase matrix cell remains **compiled-lane-gated**; interpreted web evidence is
  not achievable until the compiled lane (or a major interpreter perf fix) lands.
