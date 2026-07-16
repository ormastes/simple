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
SIMPLE_NO_STUB_FALLBACK=1 bin/simple run tools/pixel_compare/render_and_save_simple.spl
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

## Current Status (2026-06-11)

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
The wrapper keeps collecting independent backend, font offload/readback, and
raw Metal readback evidence after an earlier matrix or layout failure. Treat
the top-level `production_gui_web_renderer_parity_reason` as the first failing
gate, then read the promoted nested fields to see which later gates are already
proven, unavailable, or failing.
If the Simple Web layout manifest times out after writing per-case rows, the
wrapper still derives and promotes partial case/pass/tracked/fail counts while
leaving `production_gui_web_renderer_parity_layout_manifest_status=timeout`.
Production parity runs the Simple Web layout manifest fresh by default so stale
per-case evidence cannot satisfy the top-level gate. For an explicitly bounded
diagnostic rerun, set `PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_MANIFEST_RESUME=1`;
the wrapper forwards that as `ELECTRON_LAYOUT_MANIFEST_RESUME=1`. Manifest
policies named `track-*` are counted as tracked when they emit divergent or pass
evidence with `blur_or_tolerance=false`; exact rows still require checksum and
pixel-count equality.
If every manifest row reports the same host dependency failure, such as
`missing-electron-dependency` or `missing-simple-bin`, the manifest wrapper now
emits `electron_simple_web_layout_manifest_status=unavailable` instead of a
renderer mismatch failure. Read
`electron_simple_web_layout_manifest_dependency_status`,
`electron_simple_web_layout_manifest_dependency_reason`, and
`electron_simple_web_layout_manifest_dependency_missing_count` before debugging
Simple Web layout code.
The same production wrapper now treats Electron event routing as both an
interaction and browser-loop proof. A pass must promote focus/move/maximize,
title-command, text-input, pointer-down/up, `performance.now()`, two
`requestAnimationFrame` ticks, a CSS animation probe, and no blur/tolerance
under `production_gui_web_renderer_parity_event_routing_*`.

The canonical production GUI font offload/readback evidence gate is:

```bash
sh scripts/check/check-production-gui-font-offload-evidence.shs
```

It exercises the preferred vector and bitmap font offload/readback wrappers
together and emits `production_gui_font_offload_*` env rows plus a Markdown
report. Missing hardware, runtime, queue, submit, or readback capability must
remain explicit: examples include `cuda-runtime-unavailable`,
`opencl-runtime-or-queue-unavailable`, `vector-font-glyph-not-submitted`,
`vector-font-glyph-return-missing`, and `gpu-glyph-raster-not-submitted`.
The canonical production GUI renderer parity wrapper also runs this font gate
and promotes its typed rows under
`production_gui_web_renderer_parity_font_offload_*`, including vector and bitmap
backend, offload status, readback status, reason, and production-ready fields.
Chrome live bitmap capture is bounded by `CHROME_LAYOUT_TIMEOUT_SECS` and
`CHROME_LAYOUT_KILL_SECS` in
`scripts/check/check-chrome-simple-web-layout-bitmap-evidence.shs`; a stuck
DevTools capture must surface as `chrome-live-capture-timeout` rather than
hanging the production parity wrapper.

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

Mixed-axis overflow exact parity is covered by the focused scene:

```bash
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple \
ELECTRON_BITMAP_SCENE=simple-web-layout-overflow-axis-matrix \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

This row depends on Chromium's computed overflow rule where
`overflow-x:hidden; overflow-y:visible` becomes vertical auto overflow, including
the native-width scrollbar paint. Evidence:
`doc/09_report/electron_simple_web_layout_overflow_axis_after_scrollbar_paint_2026-06-23.md`.

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
The Tauri/Chrome surface manifest follows the same policy: exact text-free rows
must remain bit-exact, while `policy=track-text-divergence` rows are counted in
separate `*_tracked_count` / `*_tracked_mismatch_count` fields and still require
`blur_or_tolerance=false`.

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

The canonical path is HTML/Web semantic layout → `DrawIrComposition` →
Engine2D. Resolved selected-vector text carries stable font identity and ordered
advances in Draw IR; Engine2D alone prepares transient
`FontRenderBatch`/atlas material through the shared `FontRenderer`. The older
5×7 layout painter and heuristic renderer are compatibility/diagnostic paths,
not production completion evidence.

## Known Limitations

- **Compatibility bitmap font**: the 5×7 painter cannot bit-match browser text.
  The selected vector-font path already uses the shared TTF/font renderer;
  remaining acceptance is native device/readback and fixed-oracle evidence, not
  another rasterizer integration.
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
- **Antialiasing differs**: the compatibility 5×7 painter is binary, while the
  selected vector path uses coverage8/grayscale alpha; neither is assumed to
  bit-match browser subpixel text without a fixed oracle.
- **Tauri real capture**: No real WebView capture path exists yet. Chromium-via-Electron is the primary reference.
- **Runtime**: use an admitted self-hosted `bin/simple`; bootstrap-stage and Rust
  seed binaries are not pixel or font acceptance evidence. If admission fails,
  record the compiler blocker instead of falling back.

## Test Fixtures

### Shared font comparisons

Before comparing resolved selected-vector font pixels, assert that layout and
Draw IR carry the same pinned `font-identity`, ordered advances, and direction.
When shaping is selected, also assert identical shaped glyph
IDs/positions/clusters. Language and script remain producer/shaper evidence;
they are not serialized in `DrawIrGlyphRunPayload`. Use exact RGBA8 for the
integer alpha oracle; broader native antialiasing requires
the fixture's fixed absolute edge/coverage limits. Nonblank pixels, equal
checksums, upload, or emitted GPU source do not prove native execution; record
the backend, submitted payload hash, completed fence, and readback origin.

Located in `test/fixtures/pixel_compare/`:
- `simple_text.html` — "Hello World" in monospace, white background
- `complex_text.html` — h1 + styled paragraphs with mixed fonts/sizes/colors
- `css_boxes.html` — colored div boxes with margin/padding/width/height
