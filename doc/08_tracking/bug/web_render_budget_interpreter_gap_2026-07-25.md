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

## Triage 2026-11-25 — state confirmed unchanged; remains compiled-lane-gated

Verified on `release/1.0.0` (7998d6ba40d) by code inspection:

- Crash fix present: `_u8_blob_to_i64_array` in
  `src/lib/common/encoding/font_registry.spl`.
- Budget mechanism as documented: `WEB_RENDER_BUDGET_MS` default consumed by
  `_web_budget_begin` (`simple_web_html_layout_renderer.spl:89`) with the
  `SIMPLE_WEB_RENDER_BUDGET_MS` env override in
  `simple_web_html_layout_renderer_foundation.spl:225`; default not inflated.

Classification: SKIP. The recorded resolution is a policy ("fix = compiled
lane, not budget inflation"), and closing the interpreted-perf gap is a
compiler-performance program, not a bounded bugfix. An interpreted
web-showcase render was not attempted on this host (the doc's own evidence is
that even a 600 s budget does not finish 480x360 interpreted, and this
host's only runtime is the pinned Rust seed). Status line remains accurate.
