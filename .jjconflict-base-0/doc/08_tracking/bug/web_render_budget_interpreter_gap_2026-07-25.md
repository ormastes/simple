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

## Resolution
- Evidence checks already catch this honestly (`blank-or-uniform`), no fake-pass.
- `SIMPLE_WEB_RENDER_BUDGET_MS` is the explicit override lane for debugging; default
  stays 10s (sized for compiled execution) — do not inflate it to mask the perf gap.
- Web showcase matrix cell remains **compiled-lane-gated**; interpreted web evidence is
  not achievable until the compiled lane (or a major interpreter perf fix) lands.
