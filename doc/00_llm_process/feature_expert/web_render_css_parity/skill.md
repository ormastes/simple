# Web Render CSS Parity Feature Expert

## Role

Own feature-specific process knowledge for pushing the pure-Simple Web software
layout/paint engine toward pixel parity with real Chromium/Electron on the
themed widget shells (glass-vibrancy WM CSS from `generate_css`). The active
target is the cross-engine widget-shell gate:
`scripts/check/check-widget-shells-crossengine-evidence.shs`, whose pass bar is
Simple-vs-real non-text agreement >= 80% (per-channel tol 8, glyph pixels
excluded via the Chrome DOM text mask). This is a *visual-fidelity* feature area
distinct from the WM-drawing regression gate (`wm_gui_window_drawing`), which is
a consumer of the same renderer.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Renderer (owned by the browser_engine layer, consumed here):
  [src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl](../../../../src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl)
  — `parse_html` -> `extract_css`/`compute_styles` (CSS cascade) -> `layout`
  (block/flex) -> `paint` (boxes+gradients+borders+shadow+text) ->
  `simple_web_layout_render_html_software_pixels`.
- Layer expert: [doc/00_llm_process/layer_expert/browser_engine/skill.md](../../layer_expert/browser_engine/skill.md)
- CSS under test (the exact glass tokens the fixtures embed):
  `generate_css(theme)` in [src/app/ui.web/html.spl](../../../../src/app/ui.web/html.spl)
  (light theme: bg `#ffffff`, panel `#f5f5f5`, accent `#0066cc`; `.widget-panel`
  = translucent linear-gradient over `#f5f5f5` + 6-layer soft box-shadow +
  `backdrop-filter: blur(20px) saturate(180%) brightness(1.1)`; `body` =
  3 radial-gradients + a linear-gradient; taskbar-root pill = `.widget-panel`
  with 20px radius).
- Fixture builder: [src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl](../../../../src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl)
  — `gui_window_widget_html()` (320x200: column[title label, panel[status,
  Run, Save]]) and `taskbar_shell_widget_html()` (480x64: root pill ->
  panel-content -> {pinned, running, tray} nested `.widget-panel`s -> buttons).
- Gate script: [scripts/check/check-widget-shells-crossengine-evidence.shs](../../../../scripts/check/check-widget-shells-crossengine-evidence.shs)
- Comparator (OFF-LIMITS for weakening): [scripts/check/compare-widget-crossengine.js](../../../../scripts/check/compare-widget-crossengine.js)
  — loads 3 ARGB-u32 JSONs + Chrome DOM geometry, builds the text mask, and
  emits non-text agreement %, theme color counts, and pixel-derived panel band
  top/bottom. Only emits metrics; the `.shs` applies thresholds.
- Inner-loop artifacts: `build/widget_shells_crossengine/` — saved
  `chrome_*`/`electron_*` captures + `*-argb.json`, plus
  `simple_widget_crossengine_driver.spl` (renders both Simple lanes) and
  `simple_taskbar_only_driver.spl` (taskbar only, faster).
- Bug/residual tracker: [doc/08_tracking/bug/simple_web_widget_css_divergence_vs_chromium_2026-07-03.md](../../../../doc/08_tracking/bug/simple_web_widget_css_divergence_vs_chromium_2026-07-03.md)

## Measured Residual Analysis (2026-07-03, per-region, tol 8)

Current gate: window Simple/Chrome = **62.40%**, taskbar = **30.37%** (need >= 80%).
Chrome<->Electron ~99.9% (the HTML/CSS is valid; the gap is Simple's paint).
Per-pixel disagreement was mapped by masking the Chrome DOM text rects and
histogramming Simple-vs-Chrome mismatches by row band and color:

- **Window (320x200), 12214/32486 non-text px disagree.** Dominant bands:
  - Top body band y0-13 (~4100 px, full-width): Simple paints a symmetric
    dark-in-middle ramp (~218-240) that is ~10 units too dark and NEUTRAL;
    Chrome is brighter (230-247) with a BLUE tint on the top-right (accent
    radial-gradient). Missing: radial-gradient body tint (residual #2).
  - Internal band y62-71 (~2500 px): Simple ~11 too dark + no blue tint (nested
    panel / divider region).
  - Nested content interior y~100: Simple pure white 255 vs Chrome 246 (diff 9,
    just over tol) — the translucent-gradient + backdrop-filter panel tint
    (residual #1) is not applied to this nested box.
  - Bottom y168-171: 4px panel-band offset (Simple stretches panel to y167,
    Chrome content-sizes to y171) + a SPURIOUS wide light-blue (106,164,223)
    bar at y169 where Chrome is gray 239 (accent overpaint mis-placement).
  - Window is already near its measured flat ceiling (~63%); further gains need
    the soft/gradient/backdrop tones.
- **Taskbar (480x64), 11535/16565 non-text px disagree (the anomaly).** Bands:
  - Top body band y0-13 (~6000 px = 36% of non-text): same as window — Simple
    ramp ~10-15 too dark + neutral; Chrome bright + blue top-right. THIS is the
    single biggest lever; fixing the body tint could roughly halve the taskbar
    gap.
  - Pill-top y16-30: Simple grays ~12 too dark.
  - Button pills y46-63: Simple accent (106,164,223) is far too light; Chrome
    (41,126,212). The white gradient-over-accent composites ~2x too much white
    (accent count Simple 556 vs Chrome 72 on the taskbar). A localized,
    high-value fidelity fix.

## Constraints / Gotchas (READ before editing)

- **Render cost is stylesheet-bound, not pixel-bound.** The fixtures embed the
  entire `generate_css` sheet (~290 KB HTML, 40+ rule blocks). Under the
  interpreter (`SIMPLE_EXECUTION_MODE=interpret`, `gui/debug/simple`), a single
  480x64 taskbar render measured **~25-30 minutes** on a contended machine
  (cost is CSS parse/cascade, confirmed by the wm_gui_window_drawing skill).
  Budget accordingly; a "small canvas" is NOT fast here. Iterating on renderer
  changes is expensive — batch edits, minimize verification renders.
- **HARD compat: node bitmap lane must stay bit-exact.** After every renderer
  edit run `JS_RENDER_RUNTIME=node sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`
  (`mismatch_count=0`). The pinned node scenes use NO backdrop-filter and NO
  radial-gradient, so any NEW paint path gated on `background contains
  "radial-gradient("` or on a `backdrop-filter` declaration is safe BY
  CONSTRUCTION — it never executes for the pinned scenes. Prefer such gated
  additive paths over touching shared gradient/shadow compositing (which the
  pinned scenes DO exercise and would regress).
- Also run `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` and
  `scripts/check/check-engine2d-nomirror-fast-render-evidence.shs` at the end.
- **Inner loop:** render just the Simple lane and run the comparator directly
  against the saved `chrome/electron` captures in
  `build/widget_shells_crossengine/`; only run the full gate for final
  confirmation. Env: `SIMPLE_EXECUTION_MODE=interpret SIMPLE_EXECUTION_LIMIT=0
  OSTYPE=darwin SIMPLE_ONE_CALL_READBACK=1`; driver binary
  `src/compiler_rust/target/gui/debug/simple`.
- **Concurrent-session clobbering is real.** The renderer file is edited by
  multiple agent sessions; back up every edit and re-verify content survived
  (a mid-session reconcile silently reverted `parse_font_shorthand_size_px`
  once during this work). Never leave the file mid-edit before a render.
- **Body background is skipped when a widget-panel is present.** In `paint`,
  `skip_widget_page_bg = has_widget_panel and (tag==html or body)`, so the
  `<body>`'s radial+linear gradient is NOT painted for these fixtures. Any
  radial-gradient body-tint fix must account for this (paint the tint on the
  page/root fill, or lift the skip for the top/bottom body bands) or it will
  have no effect.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh the
links and residual metrics here BEFORE committing, so the next agent starts from
the current measured state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
