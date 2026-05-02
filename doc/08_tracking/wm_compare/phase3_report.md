# Phase 3 — Wire Stitch/Glass Theme Into Web WM

Status: Complete

## Files Modified

| File | Lines (approx) | Change |
|---|---|---|
| `src/app/ui.web/html.spl` | 1-30 (imports + traffic-light constants) | Added imports of `glass_dark`, `glass_light`, `glass_obsidian_dark` factories and `GlassColorTokens`. Defined six WM traffic-light constants (`WM_TRAFFIC_CLOSE`, `WM_TRAFFIC_MIN`, `WM_TRAFFIC_MAX` and their `_HOVER` variants) referenced from `doc/05_design/stitch_design_system.md`. |
| `src/app/ui.web/html.spl` | `generate_css()` ~115-180 | Replaced the three hardcoded `glass_dark` / `glass_light` literal-hex blocks with calls to the glass_theme factories. Added a new `glass_obsidian_dark` branch that previously did not exist. Each branch now reads `bg/fg/border_color/accent/panel_bg/hover_bg/success/error/warning` from `glass_*().colors` and `dim_fg`/`surface_bg` from `GlassColorTokens.{light,dark,obsidian_dark}().{text_tertiary,surface_secondary}`. Updated `is_dark` to include `glass_obsidian_dark`. Switched `is_glass` to call `is_glass_theme(theme)`. |
| `src/app/ui.web/html.spl` | WM section (`.wm-btn-*`) | Replaced six hardcoded traffic-light hex literals with the `WM_TRAFFIC_*` constants via string concatenation. Added `.wm-app-container`, `.wm-app-titlebar`, `.wm-app-content` class definitions backed by the theme tokens (`{accent}` / `{fg}` / `{border_color}` placeholders). |
| `src/app/ui.web/html.spl` | Glass touch-up block (~ line 442) | Replaced three hardcoded traffic-light hex literals in the `.widget-menubar::before` radial-gradient with `WM_TRAFFIC_*` constants. |
| `src/app/ui.web/ws_handler.spl` | `_build_wm_app_html()` (was 122-129) | Removed all inline `style=` attributes (gradients, fonts, colors). Now emits three CSS classes: `wm-app-container`, `wm-app-titlebar`, `wm-app-content` whose styling lives in `generate_css()`. Function signature unchanged. |

## Glass Token Functions Consumed

- `common.ui.glass_theme.glass_dark()` -> UITheme (provides `colors.{background,foreground,border,accent,panel_bg,hover_bg,success,error,warning}`)
- `common.ui.glass_theme.glass_light()` -> UITheme
- `common.ui.glass_theme.glass_obsidian_dark()` -> UITheme (newly wired in Web WM)
- `common.ui.glass_theme.is_glass_theme(name)`
- `common.ui.glass_tokens.GlassColorTokens.dark()`/`.light()`/`.obsidian_dark()` (for `text_tertiary` -> `dim_fg`, `surface_secondary` -> `surface_bg` since `ThemeColors` lacks these fields)
- The pre-existing `common.ui.glass_css.generate_glass_css(theme)` call at the end of `generate_css()` continues to append the full token-backed CSS-custom-property block on top.

## Verification

### Type-check
- `bin/simple check src/app/ui.web/html.spl` -> OK
- `bin/simple check src/app/ui.web/ws_handler.spl` -> OK

### Phase 0 harness (B / four_windows / 320x240)
Captured `B_pre_stitch.ppm` BEFORE the change (saved at `test/baselines/wm_compare/four_windows/B_pre_stitch.ppm`), then re-ran with `--update-baseline` AFTER the change.

`cmp B.ppm B_pre_stitch.ppm` -> exit 0 (byte-identical).

This is **expected** and the task brief flagged it: `src/app/wm_compare/main.spl` currently uses `_render_minimal_scene()`, a placeholder that ignores the active theme entirely. The harness therefore cannot show a visible diff regardless of how the CSS pipeline changes. The honest verification path is the live Web WM (below) and the unit-style CSS check.

### CSS unit verification
A standalone harness (`/tmp/css_check.spl`) imported `app.ui.web.html.{generate_css}` and asserted on the generated string:

```
dark contains accent #0A84FF: true   (sourced from glass_dark().colors.accent)
dark contains bg #0A0A0F: true       (sourced from glass_dark().colors.background)
dark contains close #FF5F57: true    (sourced from WM_TRAFFIC_CLOSE constant)
light contains accent #007AFF: true  (sourced from glass_light().colors.accent)
light contains bg #F0F0F5: true      (sourced from glass_light().colors.background)
obsidian contains bg #060612: true   (NEW branch, sourced from glass_obsidian_dark())
obsidian contains accent #C6C6C8: true
css contains .wm-app-titlebar: true  (NEW class consumed by ws_handler)
css contains .wm-app-content: true
```

A grep over `html.spl` for the hex strings that previously lived in the per-theme branches now finds only `WM_TRAFFIC_MAX_HOVER = "#30D158"` (intentional constant). A grep over `ws_handler.spl` for `style=` and any glass hex literal returns zero matches.

### Live Web WM screenshot
Attempted to launch `bin/simple run examples/ui/web_wm.spl` to grab a live screenshot via `play_wm_screenshot`, but the example self-times out at 10s in the harness ("error: example timed out after 10s"), so an interactive capture session is not viable from inside this agent. The CSS unit verification above confirms the same code path the live server uses (`generate_css(theme)` -> embedded into `<style>` by `generate_wm_html_page`).

## Remaining Hardcoded Values (and Why)

1. **Traffic-light constants** (`WM_TRAFFIC_CLOSE` = `#FF5F57`, etc.) — `GlassColorTokens` does not define close/minimize/maximize colors because they are window-chrome controls, not surface tokens. Centralized into six named constants at the top of `html.spl` with a comment pointing back to `doc/05_design/stitch_design_system.md`. Acceptable per the task brief.
2. **Non-glass theme branches** (`is_dark`, `else`) — left untouched per the task scope ("Keep existing non-glass themes as-is — don't over-scope").
3. **The default `light` theme dropdown / accent / etc.** — also untouched, same reason.
4. **Misc rgba-overlay literals** in panel shadows / gradients (e.g. `rgba(255,255,255,0.20)` for highlight glints) — these are intentional glass-effect overlays unrelated to theme colors. Replacing them belongs in a `glass_overlay_tokens` design refresh, not Phase 3.

## Does `four_windows` visibly match the Stitch design intent?

The Phase 0 harness still emits a placeholder bitmap, so the harness PPM cannot answer this. The CSS pipeline now provably uses the Stitch-designed glass palette (verified by the unit script above) — so once Phase 1's render path replaces `_render_minimal_scene()` with the real backend (already flagged as an open Phase 1 caveat), `four_windows` will render with `#0A84FF` accents from `glass_dark()`, panel/border colors from the same source, and the WM app body styled by `.wm-app-titlebar`/`.wm-app-content` classes — exactly as the Stitch reference specifies.
