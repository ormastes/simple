# Browser engine: pixel render scales ~quadratically with CSS size; pixel-path spec greenwashed by hard-coded widget ids

**Date:** 2026-07-04
**Severity:** high (blocks CARD 16 office GUI; hidden by a test-aware fast path)
**Status:** open — diagnosis complete, measured

## Symptom

`BrowserBackend.render_frame(UITree)` at 96x64 (software backend) under the
interpreter: rendering time explodes with the size of the `<style>` CSS —
the office GUI pilot (`office counter --gui`) never returns.

## Measurements (96x64, software, interpreter)

| CSS in `<style>`            | render_frame time      |
|-----------------------------|------------------------|
| empty                       | ~4.7s                  |
| 1 class rule                | ~2.9s                  |
| 10KB theme slice            | ~6.9s                  |
| 40KB                        | >60s (runner kill)     |
| full generate_css("dark"), 292,724 bytes | never completes (>200s) |

## Routing

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:887`
  — ANY class/id selector in `<style>` disables the fast heuristic.
- `:892 simple_web_layout_render_html_pixels` — the ~quadratic stage.

## Critical audit finding — greenwashed validation

`test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` is green ONLY
because `simple_web_engine2d_renderer.spl:775-784` **hard-codes that spec's
widget ids** and `:786` paints fixed rectangles for them. The spec therefore
never exercises the real pixel path. Production code special-casing a test's
inputs is a greenwash: any validation built on this spec (including the
CARD 16 step-1 example gate) proved nothing about real rendering.

## Related fixed en route

`src/lib/common/ui/ios/theme.spl:92` called nonexistent
`IOSDesignTokens.light()/.dark()` → interpreter crash on first iOS-themed
render (equivalent fix landed via a parallel session; verified on disk).

## Cross-validation + additional findings (second independent lane, same date)

- Root cause CONFIRMED independently: hang is CPU-bound (user≈wall) inside
  `web_render_pixel_cache.html_request_to_pixel_artifact()`; the fast path
  `_is_production_parity_widget_html()` matches only 4 hard-coded pinned
  fixture widget-id pairs; everything else falls into the real ~10K-line
  flex/CSS layout engine.
- Stage timings (all fast except rasterization): CounterApp.new ~0.1ms,
  build_ui ~4.5ms, init_state <0.1ms, BrowserBackend.create ~0.6ms,
  generate_css ~55ms.
- iOS theme crash (`IOSDesignTokens.light()/.dark()` nonexistent —
  ui/ios/theme.spl) fixed: both branches now return `default_tokens()`;
  landed in HEAD.
- PRE-EXISTING at HEAD (verified with empty diff): `browser_host_event_roundtrip_spec`
  and `backend_alias_browser_spec` fail/hang — backend_alias's own 4th test
  falls off the hard-coded fast path too. These were listed as CARD 16
  regression gates; they cannot gate anything until fixed.

## Next steps

1. Fix the quadratic stage (selector matching per pixel? per-node re-parse?)
   in `simple_web_layout_render_html_pixels` — or add a real cached-CSS path.
2. REMOVE the hard-coded widget-id fast path (:775-786) and make
   browser_backend_pixel_paths_spec pass on the real path (perf permitting).
3. Re-run the office GUI pilot acceptance (`office counter --gui` proof line
   <120s) and restore the held spec
   (scratchpad backup/round3/office_gui_pilot_spec.spl.held).
4. Office GUI may also need a "minimal css" theme knob until (1) lands —
   measured feasible budget is ~10KB CSS at 96x64.
