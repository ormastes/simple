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

**Mobile consumer:** the Tauri 2 iOS/Android lanes render through this same
`render_html_tree`/`generate_css` pipeline — see
`doc/05_design/platform/mobile/tauri2_mobile_production_design.md` (production design)
and `doc/03_plan/platform/mobile/tauri2_mobile_production_plan.md` (plan).

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

- **Render cost: the O(n^2) CSS-parse blocker is FIXED (2026-07-03).** A window
  320x200 render dropped from ~40 min to **~85 s** on `gui/debug/simple` (28x);
  see the browser_engine layer skill for the root cause (`char_at`/`substring`
  are O(n) in the interpreter, so `find_from`/`css_matching_close` and the nested
  `count_css_rules`/`extract_css` scan were O(n^2), traversing the ~290 KB sheet
  ~85x). Fix = native `index_of`-based `find_from` + a one-time `css.bytes()`
  array scanned by a SINGLE brace-depth pass. Node bitmap lane stayed bit-exact.
  Inner loop is now practical on the seed. NOTE: the FULL gate uses self-hosted
  `bin/simple`, where extract_css is ~3x the seed (~168 s/render); a full
  window+taskbar gate run is ~355 s isolated (< the 600 s per-render timeout) but
  will TIME OUT if another agent is saturating the host (seen once). Run the gate
  when the box is quiet, or profile via the seed for the inner loop.
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

## Session update 2026-07-20 (not affected by the interaction/hit-test campaign — confirm engine boundary before assuming otherwise)

- The 2026-07-20 hardening campaign changed hit-test bounds semantics
  (`ea2e187c394`, inclusive → half-open `[l,r)x[t,b)`) in
  `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`. **That file belongs
  to a SEPARATE "Be*"-prefixed browser engine** (`BeDomNode`, `BeLayoutBox`,
  `hit_test`, consumed by `browser_renderer.spl` /
  `os/compositor/browser_backend.spl` / `os/apps/browser_sample/` /
  `app/ui.chromium/engine_merge.spl`) that happens to live in the same
  directory as this gate's renderer
  (`simple_web_html_layout_renderer.spl`) but shares no code path with it
  — `simple_web_html_layout_renderer.spl` has no `BeDomNode`/`BeLayoutBox`
  reference. **No paint/CSS pixels changed; this gate's residual metrics
  and thresholds are unaffected.** See the
  [browser_engine](../../layer_expert/browser_engine/skill.md) layer
  expert's 2026-07-20 note for the two-engines-in-one-directory landmine
  in full, and the new
  [interaction_input_routing](../interaction_input_routing/skill.md)
  feature expert for the broader half-open-bounds standardization (which
  this renderer has not adopted — it still uses its own paint-order/hit
  logic, untouched by this campaign).
- None of the other 9 commits in the 2026-07-20 hardening campaign touched
  `simple_web_html_layout_renderer.spl`, `generate_css`, or the
  cross-engine widget-shell gate — this entry's prior residuals/gate state
  (window 97.17%, taskbar 92.37%) stand unchanged.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh the
links and residual metrics here BEFORE committing, so the next agent starts from
the current measured state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`

## 2026-07-05: window fixture 97.11% — the ceiling was a byte/char slice bug

- **Always suspect infrastructure before compositing math.** The documented
  54-58% "flat ceiling" was an artifact: one multi-byte char (`content: '✓'`)
  shifted every char-indexed `substring` slice after it in `extract_css`'s
  byte-offset scanner, killing ~1400/1595 rules (all WM chrome + every @media
  block). Byte scanners in this renderer must mirror byte positions with char
  positions (continuation bytes 128..191 don't advance the char counter); see
  `_cb_chars_between` and the chp mirror in `extract_css_vw`.
- `extract_css_vw(html, viewport_w)` evaluates @media (min/max-width; unknown
  feature terms fail closed, matching Chrome headless). The mobile
  `@media (max-width: 599px)` block is load-bearing for 320px fixtures.
- Interaction pseudo-classes (`:hover`, `:disabled`, ...) must never match in
  a static render — `_is_interaction_state_pseudo` in `simple_match`.
- Soft shadows: `fb_soft_box_shadow` uses per-axis gaussian CDF (`_phi256`,
  sigma=blur/2) — the exact separable model for a gaussian-blurred rect.
- Body radial tints: `Style.bg_layers_raw` + `fb_background_radial_stack_clip`.
- Iteration loop: seed `gui/debug/simple` + traced entry
  (`simple_web_layout_render_html_software_pixels_traced` prints per-stage ms)
  + PPM dump (JSON pixel dumps via interpreted StringBuilder are O(n^2)-slow);
  compare against saved Chrome ARGB with scratchpad an3.js. Full loop ~2.5 min.
- Minimal-doc bisect beats full-sheet debugging — but slice whole top-level
  blocks; truncated CSS chunks swallow appended probe rules (depth desync)
  and produce false positives.

## 2026-07-05 (final): GATE GREEN — window 97.17%, taskbar 92.37%
`check-widget-shells-crossengine-evidence.shs` passes end-to-end (exit 0,
comparator and thresholds untouched, metal backend both fixtures, panel bands
within 1px of Chrome). Closing fixes after the UTF-8/media/pseudo/shadow set:
flex min-content floor (min-width:auto), explicit CSS min-width floor on all
flex sizing branches (sections' min-width:180px overflow the row like
Chromium), and per-row gradient painting that carries the full rect geometry
so border-radius corners on gradient backgrounds render round (square accent
corners were the last panel-band-bottom miss). Remaining residuals are glyph
metrics (bitmap vs Inter), excluded by design via the Chrome DOM text mask.

## 2026-07-07: backend-isolation Gap B landed — `--web-engine` facade selector

`BrowserBackend.create(w, h, backend, web_engine = "pure_simple")` and
`cli_browser` now accept `--web-engine <name>` / `--web-engine=<name>`
(space and equals forms both parsed), threading engine selection through
`web_render_backend(name, w, h)` — the shared facade this parity work
already exercises via `simple_web_render_html_to_pixels_with_engine2d_backend`.
Default (`pure_simple`) keeps the cache-first `WebRenderPixelArtifactCache`
path byte-identical (perf anchor unaffected); `chromium` tags provenance as
`compatibility_renderer`/`chromium` and never silently substitutes
`pure_simple` pixels; unknown names loud-fail (`Err`) at construction.

**Caveat (interpret mode):** the `chromium` lane's first render call crashes
with `error[E1002] function 'web_backend_env_get' not found` under
`SIMPLE_EXECUTION_MODE=interpret` — a pre-existing interpreter module-alias
resolution gap (`mod_stub -> env_ops` re-export chain), reproduced
facade-only with zero browser code. Chromium rendering is native/compiled-
mode only until that alias-resolution gap is fixed. See
`doc/08_tracking/bug/web_backend_env_get_alias_unresolved_interpret_2026-07-07.md`
and the honest-contract pin at
`test/03_system/gui/ui_browser/backend_isolation_chromium_env_get_gap_b_spec.spl`.

## 2026-07-07: `parse_html` rewritten to a linear native-split event scanner (24x @3000)

`parse_html` no longer drives per-position `text.substring(pos, ...)` (O(offset) runtime cost →
quadratic parse, see `doc/08_tracking/bug/text_substring_o_offset_parse_html_quadratic_2026-07-07.md`);
it now builds one event stream via a single native `html.split("<")` (`_html_scan_events`) and
consumes it in a two-pass `parse_html`. 27.3s→1.1s at N=3000 (~24x), confirmed linear
(2.02–2.03x per doubling) to N=6000, 23/23 semantic fixtures byte-identical (opus-reviewed).
**Idiom lesson:** a byte-array (`[i64]`/`[u8]`) rewrite of the same function was measured **~10x
worse** under the interpreter — per-element array-index reads dominate there. Prefer one native
`split()`/`find()` call over short segments, not a byte-array walk, for interpreted hot loops in
this codebase (see also the now-dead `css_bytes_*` helpers,
`doc/08_tracking/bug/css_bytes_helpers_dead_code_2026-07-07.md`, which embody the losing idiom).
`compute_styles`'s own residual superlinearity is unrelated and still open (selector-match chain,
not parse-side).
