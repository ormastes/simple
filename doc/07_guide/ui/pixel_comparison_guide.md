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

## Current Status (2026-06-05)

The canonical production GUI renderer parity gate is:

```bash
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

It aggregates the generated-GUI Electron viewport matrix, the Simple Web layout
manifest, backend-executed CPU SIMD/Metal parity, and raw Metal framebuffer
readback. Linux hosts record raw Metal as `unavailable` with
`metal-requires-macos`; macOS hosts must provide native Metal readback proof.
The backend-executed evidence also records `software_render_elapsed_us`,
`cpu_simd_render_elapsed_us`, `metal_render_elapsed_us`, and
`total_elapsed_us`; use those fields when tracking GUI startup/render
regressions instead of relying only on wall-clock test duration.
It also records `timing_budget_us`, `timing_budget_status`, and
`timing_budget_reason`; the current focused budgets are 250000 us for the
backend-executed reduced scene and 1000000 us for generated widget rendering.
Use the matching `*_pixels_per_second` fields for cross-resolution comparisons;
raw elapsed microseconds are useful for a fixed fixture, while throughput is the
stable signal when scene dimensions change.
The backend-executed wrapper records three samples by default and emits
`total_elapsed_us_min/avg/max` plus `total_pixels_per_second_min/avg/max`; use
those aggregate fields for regression triage before comparing individual sample
rows.
The canonical production wrapper promotes the same values under
`production_gui_web_renderer_parity_backend_*`, so archived full-wrapper reports
can be compared without opening the nested backend evidence file.

The generated-GUI matrix intentionally records
`text_normalization_pixels=269` for the fixture-specific text antialiasing
normalization between Chromium and the Simple fixture bitmap. The pass condition
remains exact: matching checksums and weighted checksums, `mismatch_count=0`,
and `blur_or_tolerance=false`.

Forced DOM text-flow evidence now passes exact parity with:

```bash
ELECTRON_LAYOUT_CAPTURE_MODE=dom \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

### Text fixtures: honest render + known-divergent (2026-06-06)

The two text-heavy web-layout manifest cases (`text_raster_track`,
`line_height_text_track`) previously reached "exact" parity by pasting hard-coded
captured-Chromium pixel tables over the renderer output. That was a
machine/version-specific tautology (memorizing the reference, not rendering it)
and it went stale. The overlays were removed: the renderer now emits its honest
software-rasterized text, and the two cases use `policy=track-text-divergence` in
`tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt`. The manifest
gate (`check-electron-simple-web-layout-manifest-evidence.shs`) classifies them as
**tracked** (known-divergent), not exact or fail — so the gate passes as
**16 exact + 2 tracked + 0 fail**.

Rule of thumb: layout/box/geometry must be bit-exact (`policy=exact`); per-pixel
**text antialiasing cannot bit-match a browser font rasterizer** with a 5×7 bitmap
software font, so text-dominant fixtures are `track-text-divergence`, never
memorized. See the spipe skill's false-green section.

Historical 2026-06-02 divergences below are retained as context for generic
font/text work outside the current exact fixture gates.

## Historical Status (2026-06-02)

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
- **Font offload evidence**: `vector_font_offload.spl` is the typed evidence
  path for real GPU-returned vector glyph pixels. Use
  `vector_font_preferred_offload_evidence(...)` and
  `bitmap_font_preferred_offload_evidence(...)` when the caller has probed
  backend candidates: both wrappers apply the Engine2D font offload order
  (Metal, CUDA, ROCm/HIP, Qualcomm, Vulkan, DirectX, OpenCL, OpenGL, Intel,
  WebGPU, CPU SIMD, software, CPU) before building evidence, and fall back to
  explicit CPU evidence when no candidate maps to a supported lane. Use
  `vector_font_preferred_glyph_readback_evidence(...)` for device samples:
  it resolves the backend from the same preferred lane order before calling
  `vector_font_glyph_readback_evidence(...)`, then marks vector font readback
  production-ready only when GPU-returned glyph counters are present and
  checksum-matched device readback succeeds. `bitmap_font_offload.spl`
  records the bitmap-font path as CPU glyph preprocessing plus optional
  GPU copy/upload, plus the typed `bitmap_glyph_raster` generated-kernel launch
  plan. The portable compiler emitter and the CUDA/OpenCL/HIP Engine2D paths
  expose `simple_2d_bitmap_glyph_raster_u32`; CUDA routes the generated
  operation through `bitmap_glyph_raster_kernel(...)` and classifies checksum
  readback through `CudaSession.readback_evidence(...)`, OpenCL binds the
  packed glyph/destination/size/color arguments, and HIP preflights the same
  packed shape before launch. `bitmap_glyph_raster_expected_pixels(...)` maps the
  glyph mask to the expected color/zero output and
  `bitmap_glyph_raster_checksum(...)` derives the expected checksum used by
  `bitmap_glyph_raster_readback_evidence(...)`.
  `bitmap_glyph_raster_preferred_mask_readback_evidence(...)` is the preferred
  device sample wrapper; it applies the same Engine2D lane order before dispatch,
  then invokes `bitmap_glyph_raster_mask_readback_evidence(...)`, which uses
  `bitmap_glyph_raster_mask_checksum(...)` to derive expected checksum from the
  glyph mask and color (avoids temporary expected-pixel arrays and caller-supplied
  expected values). That readback wrapper is the production proof gate: it only marks
  bitmap glyph rasterization ready after generated-kernel submit and
  checksum-matched device readback.
- **No anti-aliasing**: Binary black/white pixels vs Chrome's subpixel AA.
- **Tauri real capture**: No real WebView capture path exists yet. Chromium-via-Electron is the primary reference.
- **Interpreter binary (v0.4.0)**: Cannot load `gc_async_mut.gpu.*` modules due to `Gpu` keyword parse error. Use native binary `src/compiler_rust/target/release/simple` (v1.0.0-beta).

## Test Fixtures

Located in `test/fixtures/pixel_compare/`:
- `simple_text.html` — "Hello World" in monospace, white background
- `complex_text.html` — h1 + styled paragraphs with mixed fonts/sizes/colors
- `css_boxes.html` — colored div boxes with margin/padding/width/height
