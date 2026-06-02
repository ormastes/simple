# Pixel Comparison: Chromium vs Simple Web Renderer (2026-06-02)

## Methodology
- **Chromium reference**: Electron `capturePage()` via xvfb-run, BGRA→ARGB conversion
- **Simple renderer**: `simple_web_layout_render_html_pixels` (5x7 bitmap font, CPU framebuffer)
- **Viewport**: 320x240, white background
- **Metric**: per-pixel ARGB diff; structural = channel delta sum > 30

## Results by Page Category

### Test Fixtures (pixel_compare/)
| Page | Diff Pixels | % | Structural | Notes |
|------|------------|---|-----------|-------|
| simple_text.html | 1,036 | 1.35% | 1,003 | Bitmap vs vector glyph shapes |
| complex_text.html | 7,001 | 9.12% | 6,509 | More text = more glyph diff |
| css_boxes.html | 0 | **0.00%** | 0 | **Pixel-perfect** match |

### Famous Site Corpus (132 deterministic fixtures)
| Page | Diff Pixels | % | Structural | Notes |
|------|------------|---|-----------|-------|
| site_0_google.html | 2,477 | 3.23% | 2,096 | Text glyph shapes only |

### Production UI (examples/ui/)
| Page | Diff Pixels | % | Structural | Notes |
|------|------------|---|-----------|-------|
| sample_page.html | 51,389 | 66.91% | 47,909 | Flexbox, gradients, border-radius unsupported |

## CSS Feature Support Matrix

| Feature | Supported | Notes |
|---------|-----------|-------|
| Block flow layout | Yes | Full |
| Margin (1/2/4-value) | Yes | Fixed this session |
| Margin collapsing | Yes | Fixed this session |
| Padding | Yes | |
| Content-box width/height | Yes | Fixed this session |
| Border (solid) | Yes | Upstream |
| Background color | Yes | |
| Font size / line-height | Yes | Bitmap only |
| Text color | Yes | |
| Display none/block/inline | Yes | |
| Flexbox | No | Major gap for production UI |
| Border-radius | No | |
| Box-shadow | No | |
| Gradients | No | |
| CSS Grid | No | |
| Web fonts | No | Bitmap 5x7 only |

## Fixes Applied This Session
1. **Content-box padding**: `width`/`height` now correctly adds padding+border per CSS spec
2. **Margin collapsing**: Adjacent sibling block margins collapse to `max(bottom, top)`
3. **Margin shorthand**: Parse 1/2/4-value `margin` (e.g. `margin: 4px 8px`)
4. **Font metrics**: `char_w` 6→5, `line_h` 9→10 for closer Chrome match
5. **Baseline offset**: Center bitmap glyphs in line-height for Y-alignment
6. **Merge conflict resolution**: Resolved broken auto-merge (css_width/css_height field references)

## Existing Test Impact
- Browser engine specs: 131 passed / 87 failed (baseline was 130/88 — improved by 1)
- 3 renderer specs: 45/45 passed (2+10+33)

## Tauri/WebKitGTK Comparison
Environment-blocked on this system:
- `python3-gi-cairo` not installed (no sudo)
- Playwright WebKit host requirements unmet
- `wkhtmltoimage` not available
- Tauri CLI not installed, no pre-built binary

## MDI Assessment
Static 5-window layout exists (`shared_mdi_*` files). Missing: tabbed interface, window grouping, dynamic creation, tab strips, keyboard navigation. Estimated 40-60h for core implementation.

## Remaining Gaps
- Text fidelity: Bitmap 5x7 font cannot match vector TrueType rendering (needs `stb_truetype.h` integration)
- Flexbox: Required for production theme/UI pages
- Tauri capture: Needs system package installation
- MDI: Implementation scope TBD
