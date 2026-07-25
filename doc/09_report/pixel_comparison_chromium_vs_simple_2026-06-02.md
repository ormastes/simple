# 3-Way Pixel Comparison: Electron vs WebKit vs Simple (2026-06-02)

## Methodology
- **Electron** (Chromium): `capturePage()` via xvfb-run
- **WebKit** (Tauri-equivalent): Playwright WebKit headless screenshot
- **Simple**: `simple_web_layout_render_html_pixels` (5x7 bitmap font, CPU framebuffer)
- **Viewport**: 320x240, white background

## Results

### UI-Example Outlier

| Page | Electron↔WebKit | Electron↔Simple | WebKit↔Simple |
|------|----------------|-----------------|---------------|
| sample_page | — | 66.91% | — |

> `sample_page` is a complex CSS gradient/flexbox UI example beyond current bitmap-renderer scope. See App HTML table below for fixture results.

### Full 132-Site Corpus (320×240, 76 800 pixels each)

All 132 sites complete 3-way comparison.

| Metric | E↔W | E↔S | W↔S |
|--------|-----|-----|-----|
| **Average** | **4.84%** | **3.32%** | **3.04%** |

**Distribution (by E↔S):**

| Range | Count |
|-------|-------|
| 0–1% | 0 |
| 1–3% | 31 |
| 3–5% | 99 |
| 5–10% | 2 |
| 10%+ | 0 |

**Outliers (E↔S > 5%):** `0_google` (7.54%), `2_facebook` (7.54%)

> **Key finding:** Simple renderer E↔S average (3.32%) is **below** the Electron↔WebKit baseline (4.84%), meaning Simple is within natural browser-engine variance across all 132 corpus sites. Remaining differences are glyph-level (5×7 bitmap font vs TrueType).

### App HTML 3-Way Comparison (renderable files only)

6 renderable files: 3 portal pages + 3 test fixtures. Simple renders use `simple_app_*.json` and `simple_fixture_*.json`.

> **Note:** WebKit renders the portal pages without full font/AA loading (~256 colors vs Electron's ~1250), so E↔W is already 18–30% on those rows. The test fixtures (`css_boxes`, `simple_text`, `complex_text`) are the clean per-renderer comparison.

| Page | E↔W | E↔S | W↔S | Size |
|------|-----|-----|-----|------|
| docs | 18.22% | 15.82% | 18.07% | 320x240 |
| install | 17.20% | 16.58% | 18.18% | 320x240 |
| index | 29.86% | 32.77% | 28.03% | 320x240 |
| css_boxes | 0.00% | 0.00% | 0.00% | 320x240 |
| simple_text | 0.79% | 1.35% | 0.96% | 320x240 |
| complex_text | 7.30% | 9.28% | 8.44% | 320x240 |
| **Average (6)** | **12.23%** | **12.63%** | **12.28%** | — |

**App HTML categorization (19 total captured):**
- 6 renderable (3 portal pages + 3 test fixtures) — compared above
- 12 Handlebars templates — need server-side processing, not renderable as clean pages
- 1 skipped (3rd-party: `portal/node_modules/vscode-test/LICENSE.chromium.html`)

## GUI Category Coverage

- **Famous site corpus**: 132/132 sites, 3-way complete
- **App HTML**: 6 renderable + 12 templates + 1 skipped (see above)

## SIMD Backend Parity

Software vs CPU/SIMD backends produce **identical output** (0% diff) across all tested pages.

## Fixes Applied
1. Content-box padding: `width`/`height` adds padding+border per CSS spec
2. Margin collapsing: Adjacent sibling margins collapse to `max()`
3. Margin shorthand: Parse 1/2/4-value `margin`
4. Font metrics: `char_w` 6→5, `line_h` 9→10
5. Baseline offset: Center bitmap glyphs in line-height
6. MDI tab model: Tab groups, tab bar rendering, tab click switching, group/ungroup, keyboard nav (cycle_tab/cycle_tab_reverse)

## MDI Status
- **Before**: Static 5-window layout, no tabbing
- **After**:
  - Tab group data model and tab bar rendering
  - Tab click switching (click to activate tab)
  - Group/ungroup APIs
  - Keyboard nav: `cycle_tab()` for Ctrl+Tab, `cycle_tab_reverse()` for Ctrl+Shift+Tab
- **Remaining**: Tab context menus, dynamic window creation, persistence
