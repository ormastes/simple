# 3-Way Pixel Comparison: Electron vs WebKit vs Simple (2026-06-02)

## Methodology
- **Electron** (Chromium): `capturePage()` via xvfb-run
- **WebKit** (Tauri-equivalent): Playwright WebKit headless screenshot
- **Simple**: `simple_web_layout_render_html_pixels` (5x7 bitmap font, CPU framebuffer)
- **Viewport**: 320x240, white background

## Results

| Page | Electron↔WebKit | Electron↔Simple | WebKit↔Simple |
|------|----------------|-----------------|---------------|
| css_boxes | **0.00%** | **0.00%** | **0.00%** |
| simple_text | 0.79% | 1.35% | 0.96% |
| complex_text | 7.30% | 9.12% | 8.31% |
| google_corpus | — | 3.23% | — |
| sample_page | — | 66.91% | — |

## GUI Category Coverage (148 HTML files)
- **Theme HTML** (3 files): Tailwind CSS + external fonts — requires JS runtime, not renderable by bitmap renderer
- **Webapp views** (9 files): Handlebars templates, require layout processing
- **UI examples** (2 files): Complex CSS (flexbox, gradients, border-radius) — 66.91% diff
- **Tauri shell** (2 files): Gradients + flexbox — same limitation as UI examples
- **Famous site corpus** (132 files): Deterministic fixtures, 3.23% diff (glyph shapes only)

## Fixes Applied
1. Content-box padding: `width`/`height` adds padding+border per CSS spec
2. Margin collapsing: Adjacent sibling margins collapse to `max()`
3. Margin shorthand: Parse 1/2/4-value `margin`
4. Font metrics: `char_w` 6→5, `line_h` 9→10
5. Baseline offset: Center bitmap glyphs in line-height
6. MDI tab model: Tab groups, tab bar rendering, tab switching, group/ungroup

## MDI Status
- **Before**: Static 5-window layout, no tabbing
- **After**: Tab group data model, tab bar rendering, tab click switching, group/ungroup/detach APIs
- **Remaining**: Keyboard navigation (Ctrl+Tab), tab context menus, dynamic window creation, persistence
