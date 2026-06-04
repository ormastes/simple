# Pixel-Level Rendering Comparison Guide

Compares real Chromium/WebView rendering against the Simple web renderer's 2D CPU/SIMD backend output at the pixel level.

## Architecture

All three shell backends (Electron, Tauri, Pure Simple) share the same Simple web rendering API. The Pure Simple web renderer uses a 2D CPU/SIMD backend for rasterization. The comparison reference is real Chromium (via Electron `capturePage()`).

```
Reference path:  HTML → Electron/Chromium → capturePage() → BGRA → ARGB pixels
Test path:       HTML → Simple web renderer → 2D CPU backend → ARGB pixels
Diff:            Per-pixel ARGB comparison + structural/fringe classification
```

## Tools

| Tool | Purpose |
|------|---------|
| `tools/electron-live-bitmap/capture_html_argb.js` | Capture HTML through real Chromium → ARGB JSON |
| `tools/pixel_compare/diff_ppm.js` | Compare two PPM images with classification |
| `tools/pixel_compare/diff_argb.js` | Compare two ARGB JSON captures |
| `tools/pixel_compare/argb_json_to_ppm.js` | Convert ARGB JSON to PPM for viewing |
| `tools/pixel_compare/render_and_save_simple.spl` | Render HTML through Simple → JSON + PPM |

## Running a Comparison

### 1. Capture through Chromium

```bash
ELECTRON_CAPTURE_HTML=test/fixtures/pixel_compare/simple_text.html \
ELECTRON_CAPTURE_WIDTH=320 ELECTRON_CAPTURE_HEIGHT=240 \
ELECTRON_CAPTURE_OUTPUT=build/pixel_compare/electron_out.json \
xvfb-run --auto-servernum --server-args="-screen 0 1280x720x24" \
npx --prefix tools/electron-shell electron --no-sandbox --disable-gpu \
tools/electron-live-bitmap/capture_html_argb.js
```

### 2. Render through Simple

```bash
SIMPLE_LIB=src PIXEL_HTML=test/fixtures/pixel_compare/simple_text.html \
PIXEL_W=320 PIXEL_H=240 \
PIXEL_OUT_JSON=build/pixel_compare/simple_out.json \
PIXEL_OUT_PPM=build/pixel_compare/simple_out.ppm \
src/compiler_rust/target/release/simple run tools/pixel_compare/render_and_save_simple.spl
```

### 3. Compare

```bash
node tools/pixel_compare/diff_argb.js build/pixel_compare/electron_out.json build/pixel_compare/simple_out.json
# Or for PPM files:
node tools/pixel_compare/diff_ppm.js reference.ppm test.ppm diff_output.ppm
```

## Diff Classification

- **STRUCTURAL**: `large_delta(>30) > small_delta(<=30)` — fundamental layout or color differences
- **FRINGE**: small deltas dominate — anti-aliasing edge differences

## Current Status (2026-06-02)

| Fixture | Differing Pixels | Type | Root Cause |
|---------|-----------------|------|------------|
| Simple text (16px mono) | 1018/76800 (1.3%) | STRUCTURAL | Bitmap 5x7 font vs Chrome vector font |
| CSS boxes (margin+width) | 1584/76800 (2.1%) | STRUCTURAL | Content-box padding interaction |
| Complex text (h1+p) | 7425/76800 (9.7%) | STRUCTURAL | Font metrics + tag selector margin |
| Famous site corpus (site_0_google) | 2649/19200 (13.8%) | FRINGE | Text rendering + AA differences |

## Rendering Paths

The Simple web renderer has two code paths:

1. **Layout renderer** (`simple_web_html_layout_renderer.spl`) — Real HTML parser + CSS cascade + block layout + 5x7 bitmap font paint. Used for generic HTML.
2. **Heuristic renderer** (`simple_web_engine2d_renderer.spl`) — Pattern-matching substring heuristic for known HTML structures (famous site corpus, WM scenes). Falls through to layout renderer for unrecognized HTML.

## Known Limitations

- **Bitmap font**: 5x7 glyph grid scaled by `glyph_scale(font_size)` cannot match Chrome's vector font rendering. Needs TTF rasterizer integration (stb_truetype available in `src/runtime/stb_truetype.h`).
- **No anti-aliasing**: Binary black/white pixels vs Chrome's subpixel AA.
- **Tauri real capture**: No real WebView capture path exists yet. Chromium-via-Electron is the primary reference.
- **Interpreter binary (v0.4.0)**: Cannot load `gc_async_mut.gpu.*` modules due to `Gpu` keyword parse error. Use native binary `src/compiler_rust/target/release/simple` (v1.0.0-beta).

## Test Fixtures

Located in `test/fixtures/pixel_compare/`:
- `simple_text.html` — "Hello World" in monospace, white background
- `complex_text.html` — h1 + styled paragraphs with mixed fonts/sizes/colors
- `css_boxes.html` — colored div boxes with margin/padding/width/height
