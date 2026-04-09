# SStack State: wm-pixel-consistency

## User Request
> intensively check windows manager variations. first electron backed windows manager on host. let it base them. than compare simple browser engine base windows manager pixcel level equvalent. use image comaparison tool to check i. so ultimately electron base wm and qemu simple os wm magager to have bit and color level consistency through whole backend. check how make other tools do that. intensively research web.

## Task Type
feature

## Refined Goal
> Build a pixel-level visual consistency verification pipeline that renders the same WM/compositor scene in both the Electron-backed host renderer and the Simple browser engine running in QEMU, then compares the output at bit/color level to ensure rendering equivalence across backends.

## Acceptance Criteria
- [ ] AC-1: Research report covering how industry tools (Chromium pixel tests, Playwright, Percy, BackstopJS, etc.) achieve cross-backend pixel consistency, with actionable findings for Simple's architecture
- [ ] AC-2: Electron host backend captures a reference screenshot of a standard WM scene (window decorations, glassmorphism, text, desktop chrome) as raw ARGB pixel buffer
- [ ] AC-3: QEMU Simple OS backend captures the same WM scene as raw ARGB pixel buffer via existing screenshot_compare.spl infrastructure
- [ ] AC-4: Image comparison pipeline compares the two captures at channel level (R, G, B, A) with configurable tolerance thresholds, reporting match percentage, max channel diff, and diff region map
- [ ] AC-5: A "golden test" spec validates that a reference scene renders with >=99% pixel match (within tolerance) across both backends
- [ ] AC-6: Diff visualization — when mismatches exceed threshold, produce a diff image highlighting divergent pixels
- [ ] AC-7: Documentation of rendering divergence root causes and normalization strategies (font rasterization, anti-aliasing, color space)

## Cooperative Providers
- Codex: available
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-09
- [x] 2-research (Analyst) — 2026-04-09
- [x] 3-arch (Architect) — 2026-04-09
- [x] 4-spec (QA Lead) — 2026-04-09
- [x] 5-implement (Engineer) — 2026-04-09
- [x] 6-refactor (Tech Lead) — 2026-04-09
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task Type:** feature
**Slug:** wm-pixel-consistency

**Key existing code identified:**
- `src/os/compositor/screenshot_compare.spl` — pixel comparison engine (ARGB buffers, match %, channel diff)
- `src/os/compositor/` — full compositor with multiple backends (fb, browser, hosted)
- `src/lib/gc_async_mut/gpu/browser_engine/` — DOM/CSS/Layout/Paint pipeline
- `src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl` — glass visual comparison
- `src/lib/gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl` — screenshot capture
- `tools/electron-shell/` — Electron app with screenshot.js, export_snapshot.js
- `src/app/ui.electron/backend.spl` — Electron UI backend
- `src/os/compositor/browser_backend.spl` — browser rendering backend
- `src/os/compositor/browser_compositor_backend.spl` — software pixel buffer for browser engine
- `src/app/test_daemon/qemu_broker.spl` — QEMU test broker
- `src/os/qemu_runner.spl` — OS QEMU runner

**Approach:** Electron renders via Chromium (HTML/CSS), Simple OS renders via software compositor/browser engine. The pixel-level comparison must account for expected divergences (font hinting, subpixel AA) and provide tolerance-based matching.

### 2-research

## Research Summary

### Existing Code

**Core Pixel Comparison Engine:**
- `src/os/compositor/screenshot_compare.spl:1-474` — Full-featured pixel comparison engine operating on ARGB u32 buffers. Provides:
  - `compare_pixel_buffers()` (L34-99): Per-channel threshold comparison, returns ComparisonResult with match_percentage (0-10000 scale), max_channel_diff, total_channel_diff
  - `compare_exact()` (L101-103): Exact match wrapper (threshold=0)
  - `compare_with_tolerance()` (L199-212): Boolean convenience — pass/fail with min_pct threshold
  - `compare_per_channel()` (L279-339): Independent R/G/B/A channel comparison at bit-field level
  - `generate_diff_image()` (L109-158): Visual diff — green=match, red=diff (brightness = magnitude)
  - `generate_channel_diff_image()` (L437-473): Single-channel grayscale diff image
  - `find_diff_regions()` (L353-431): Scanline-based diff region detection, returns DiffRegion bounding boxes
  - `print_multi_backend_report()` (L225-247): Cross-backend comparison table with PASS/FAIL status
  - Structs: ComparisonResult, DiffRegion, ChannelDiffResult, BackendCompareEntry

**Glass Pipeline Comparison (Dual-Pipeline):**
- `src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl:1-148` — Renders same SDN demo through two paths:
  - Path A (Web HTML): SDN -> UITree -> HTML/CSS -> browser engine html_to_dom -> render_dom_to_pixels -> [u32]
  - Path B (Engine): SDN -> UITree -> widget_to_dom -> render_dom_to_pixels -> [u32]
  - `render_both_pipelines()` (L40-91): Returns PipelineOutput with web_pixels, engine_pixels, web_html
  - `render_web_pipeline_only()` / `render_engine_pipeline_only()` — single-path variants

**Backend Screenshot Capture:**
- `src/lib/gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl:1-183` — Multi-backend pixel capture:
  - `capture_with_backend()` (L37-72): Renders HTML through a named Engine2D backend (cuda, vulkan, metal, software, cpu)
  - `capture_software()` (L74-108): Legacy software rasterizer path
  - `capture_all_available()` (L110-131): Discovers and renders through all available Engine2D backends
  - `capture_with_effect_engine()` (L133-183): Swaps int/float effect engines for comparison
  - Struct: BackendCapture (backend_name, pixels, width, height, success, error)

**Glass Comparison Runner (Full Suite):**
- `src/lib/gc_async_mut/gpu/browser_engine/glass_comparison_runner.spl:1-294` — Orchestrates full comparison suite:
  - `run_glass_comparison()` (L46-127): Runs compare_pixel_buffers + compare_per_channel + find_diff_regions for each demo
  - `identify_missing_features()` (L143-168): Scans HTML for unsupported CSS features (backdrop-filter, box-shadow, gradients, transforms)
  - `glass_report_to_markdown()` (L218-294): Full markdown report with CSS feature gap analysis, per-demo results, diff region summary
  - Structs: GlassComparisonResult (overall, channels, diff_regions, missing_features), GlassComparisonReport
  - Constants: DEFAULT_WIDTH=800, DEFAULT_HEIGHT=600, DEFAULT_THRESHOLD=4

**Browser Rendering Backends:**
- `src/os/compositor/browser_backend.spl:1-364` — BrowserBackend class implementing RenderBackend trait. Full pipeline: UITree -> DOM -> themed DOM -> CSS layout -> paint -> RenderScene -> pixels. Supports Engine2D attachment (GPU/framebuffer) or software rasterizer fallback. Theme constants (ARGB u32), ARGB-to-CSS-hex conversion.
- `src/os/compositor/browser_compositor_backend.spl:1-286` — BrowserCompositorBackend: pure Simple in-memory [u32] pixel buffer. All drawing operations (fill_rect, draw_text, blend_rect, blur_region, gradient_v) write to Simple-side array. `get_pixel_buffer()` returns buffer for direct comparison. 5-pass HVHVH box blur for glass effects.

**Electron Infrastructure:**
- `tools/electron-shell/screenshot.js:1-85` — Headless Electron page capture. Uses offscreen BrowserWindow, disables hardware acceleration, captures via `webContents.capturePage()`, exports PNG. Accepts HTML file or inline HTML, configurable width/height.
- `tools/electron-shell/export_snapshot.js:1-396` — Full snapshot pipeline: spawns `bin/simple ui electron`, captures first IPC render payload (HTML), writes standalone HTML file. Fallback to `export_snapshot.spl` HTML generator. Optional PNG capture via screenshot.js. Configurable width (default 1360), height (default 840), timeout.
- `src/app/ui.electron/backend.spl:1-110` — ElectronBackend: wraps Web backend HTML generation + IPC for native features. Outputs full HTML page via `generate_html_page()`, reads events from stdin IPC. Default viewport: 1280x720.

**QEMU Infrastructure:**
- `src/app/test_daemon/qemu_broker.spl:1-179` — Session pooling for QEMU tests. QemuBroker manages pool of QemuSessionEntry with acquire/release/cleanup. Supports golden snapshot flag per session.
- `src/app/test_daemon/qemu_broker_snapshot.spl:1-58` — QMP-dependent snapshot operations: `acquire_with_snapshot()` creates golden snapshot on first use, `snapshot_save()`/`snapshot_restore()` for named snapshots via QMP.
- `src/lib/nogc_sync_mut/qemu/qmp_client.spl:1-80` — QMP client over Unix socket via socat. Supports savevm/loadvm, query-status, system_reset. NOTE: No screendump command implemented yet — this is a gap that needs to be filled for QEMU screenshot capture.
- `src/os/qemu_runner.spl:1-712` — Full QEMU runner with all 6 architectures. Defines QemuScenario configs including `scenario_x64_gpu_2d()` with virtio-gpu and `scenario_x64_gui()` with BGA framebuffer. `build_qemu_command()` constructs QEMU CLI, `build_scenario_command()` for named scenarios.

**Existing Pixel Comparison Tests:**
- `test/integration/rendering/backend_screenshot_compare_spec.spl:1-147` — Backend comparison tests using SSpec. Verifies software vs CPU (exact), software vs CUDA (GPU tolerance=2, min match 99.90%), all-available-backends cross-comparison. Diff image generation tests.
- `test/system/gui/glass_pixel_compare_spec.spl:1-185` — Glass pipeline comparison spec. Tests dual-pipeline rendering, per-channel bit-field diff, diff image generation, CSS feature gap detection, core demo suite (3 demos x 2 themes), light vs dark theme diff, full suite.
- `test/integration/rendering/pixel_verify_full.spl:1-209` — Full pipeline pixel verification. Tests scene executor (red/green fill, gradient, rounded rect, determinism) and HTML pipeline (pixel output, deterministic rendering, viewport sizes).

**Chrome vs Electron Comparison Infrastructure:**
- `examples/browser/test/compat/chrome_vs_electron.spl:1-142` — ChromeVsElectron driver. Compares Chrome and Electron screenshots via PPM, reports MATCH (>=99%), CLOSE (>=95%), DIVERGED (<95%). Uses ComparisonMetrics with RMSE.
- `examples/browser/test/compat/pixel_suite.spl:1-242` — Full pixel comparison test runner with PixelSuite class. TestManifest discovery, per-category pass rates, worst-N tests. Configurable threshold (default 85.0%).
- `examples/browser/test/compat/image_export.spl:1-458` — PPM/BMP image I/O. ComparisonMetrics with match_percentage, RMSE, avg_channel_diff. Diff image generator (green=match, red=mismatch). PPM P3/P6 reader/writer, BMP reader (24-bit/32-bit).
- `examples/browser/test/compat/compare_render_pair.spl:1-34` — CLI tool for comparing two rendered images, outputs metrics file + diff PPM.
- `examples/browser/test/reftest/pixel_compare.spl:1-170` — CSS reftest pixel comparator. compare_exact() and compare_fuzzy() with per-channel tolerance. CompareResult with passed/mismatched_pixels/max_channel_delta.
- `examples/browser/test/reftest/reftest_runner.spl:1-80+` — WPT-style reftest runner. RefTestCase with "==" or "!=" comparison, per-channel tolerance.

**SSpec Screenshot Infrastructure:**
- `src/compiler_rust/lib/std/src/spec/screenshot.spl:1-718` — Full screenshot capture module for SSpec. CaptureMode (Before/After/Both/OnChange), ImageFormat (PNG/JPEG/ANSI). Supports Vulkan framebuffer, TUI buffer, PTY buffer capture. FFI functions for screenshot enable/disable/capture.

### Reusable Modules

- `os.compositor.screenshot_compare` — **Primary reuse target.** Complete ARGB pixel comparison with threshold, per-channel, diff regions, diff images, multi-backend reports. All functions needed for AC-4 and AC-6.
- `std.gc_async_mut.gpu.browser_engine.glass_pipeline_compare` — Dual-pipeline rendering (Web HTML path vs Engine path). Reusable pattern for rendering same scene through different backends.
- `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture` — Multi-backend capture facility. Pattern for capture_with_backend() can be adapted for Electron vs QEMU capture.
- `std.gc_async_mut.gpu.browser_engine.glass_comparison_runner` — Full comparison suite orchestration with markdown reports and CSS feature gap analysis. Architecture pattern for the golden test pipeline.
- `examples.browser.test.compat.image_export` — PPM/BMP I/O, ComparisonMetrics with RMSE, diff image generation. Useful for image file format support.
- `examples.browser.test.compat.chrome_vs_electron` — Cross-renderer comparison driver pattern (ChromeVsElectron). Directly relevant architecture for Electron vs QEMU comparison.
- `examples.browser.test.reftest.pixel_compare` — Fuzzy comparison with per-channel tolerance. compare_fuzzy() pattern.
- `std.qemu.qmp_client` — QMP protocol client for QEMU control. Needs extension with `screendump` command for QEMU screenshot capture.
- `app.test_daemon.qemu_broker` + `qemu_broker_snapshot` — Session pooling and snapshot management for QEMU. Reusable for test session lifecycle.
- `os.qemu_runner` — QEMU scenario definitions (x64-gui, x64-gpu-2d). Reusable for setting up the right QEMU configuration for GUI rendering.

### Domain Notes

**1. Chromium Pixel Tests (web_tests infrastructure)**
- Chromium's web tests (formerly layout tests) render pages in content_shell and compare output against expected results stored per-platform in `src/third_party/blink/web_tests/platform/`.
- Platform-specific baselines: each OS gets its own expected output directory. No fuzzy matching at the test level — differences are handled by rebaselining.
- Linux rendering tries to match Windows font metrics exactly. macOS overrides Color Profile and Appearance settings during tests to ensure deterministic output.
- WPT reftests support a `fuzzy()` annotation: `<meta name=fuzzy content="maxDifference=10-15;totalPixels=200-300">` — specifying max per-channel color difference and total pixel count ranges. This is the primary tolerance mechanism.
- Key insight: Chromium prioritizes *environmental control* (locking down fonts, color profiles, system settings) over algorithmic tolerance.

**2. Playwright Visual Comparison**
- Uses pixelmatch library internally for pixel-level diffing.
- Three tolerance controls: `threshold` (YIQ perceptual color difference, default 0.2, range 0-1), `maxDiffPixels` (absolute count), `maxDiffPixelRatio` (percentage 0-1).
- Platform normalization: separate baseline snapshots per browser+platform combination. Snapshot names auto-include browser name and platform.
- Acknowledges that screenshots differ between browsers and platforms due to rendering, fonts, and more.
- Key insight: Playwright does NOT normalize rendering — it maintains separate golden images per platform. Tolerance handles minor rendering jitter within a single platform.

**3. Percy.io Architecture**
- DOM snapshot approach (not image-based): captures DOM + assets, re-renders server-side in real browsers.
- Cross-browser: same DOM is rendered in Chrome, Firefox, Edge, Safari in Percy's infrastructure.
- Rendering stabilization: freezes animations, handles dynamic data, deterministic font rendering.
- Ignores 1px diffs caused by nondeterministic rendering by default.
- Horizontal scaling: all rendering/diffing is server-side, no impact on test speed.
- Key insight: Percy's DOM-snapshot approach eliminates many host-side rendering variables. For Simple, the equivalent would be capturing the UITree/SDN scene definition and rendering it through both backends in controlled environments.

**4. BackstopJS**
- Uses Puppeteer (headless Chrome) + ResembleJS (diff library).
- Configurable mismatch threshold (default 0.1% = catches extremely nuanced differences).
- Generates visual reports with comparison side-by-side and diff overlay.
- Multi-viewport testing for responsive layouts.
- Key insight: BackstopJS operates within a single rendering engine (Chrome). Cross-engine comparison is out of scope for it.

**5. Pixelmatch Algorithm**
- ~150 lines, zero dependencies, operates on raw typed arrays.
- Uses YIQ NTSC color space for perceptual color difference (Kotsarenko & Ramos 2010).
- Anti-aliasing detection based on "Anti-aliased Pixel and Intensity Slope Detector" (Vyšniauskas 2009). Auto-detects AA pixels and can exclude them from diff count (`includeAA` option).
- Threshold 0-1 (default 0.1): controls YIQ color distance sensitivity.
- Returns count of mismatched pixels.
- Key insight: The YIQ perceptual comparison and AA detection are directly applicable to Simple's use case. The existing `screenshot_compare.spl` uses straight RGB channel difference — upgrading to YIQ would reduce false positives from anti-aliasing and subpixel differences.

**6. Font Rasterization Differences**
- Three main engines: DirectWrite (Windows), CoreText (macOS), FreeType (Linux/everywhere else).
- Fundamental philosophical difference: Windows prioritizes grid-fitting/crispness, macOS prioritizes typeface fidelity, FreeType is configurable.
- Chrome ships FreeType on all platforms for color fonts and variable fonts, but system-level text still uses platform-native engine.
- FreeType can approximate Windows-style rendering.
- For Simple's case: the browser engine (software renderer) uses its own text rasterizer (likely based on `src/lib/common/text_layout/font_renderer.spl`), while Electron uses Chromium's Skia + platform font backend. These WILL differ at pixel level for text. Mitigation: (a) use higher tolerance around text regions, (b) use identical font rasterizer in both paths, or (c) exclude text regions from strict comparison.

**7. Subpixel Anti-Aliasing**
- iOS, Android, Windows Metro all use standard grayscale AA (no subpixel). macOS uses subpixel AA only under specific conditions (non-rotated display, LCD smoothing enabled, composited text).
- Chrome mixes grayscale and subpixel AA depending on compositing layer (non-root layers get grayscale).
- High-DPI displays eliminate the need for subpixel AA entirely.
- For Simple's case: the software renderer in QEMU uses grayscale AA (no subpixel knowledge). Electron/Chromium may use subpixel AA on the host. Mitigation: force Electron to use `--disable-lcd-text` flag or render at 2x DPI where subpixel AA is disabled.

**8. Color Space Handling**
- Default web color space: sRGB. CSS and SVG assume sRGB.
- Display P3 is ~25% larger gamut than sRGB. Safari supported it since 2016, Chrome added support, Firefox historically sRGB-only.
- Color management differences: some programs ignore profiles and interpret as sRGB, others apply ICC profiles.
- For Simple's case: both backends should operate in sRGB. The software renderer in `browser_compositor_backend.spl` uses raw ARGB u32 without color management (effectively sRGB). Electron renders in whatever the host display profile is. Mitigation: force Electron to sRGB mode, ensure both paths clamp to 8-bit sRGB.

**9. Chromium/Blink vs Software Renderer Divergences**
- Sub-pixel geometry snapping: Blink aligns drawings to screen pixels, may round differently than a software renderer.
- GPU rasterization: Blink rasters display lists in a separate Viz process, potentially on GPU. Software renderer does direct pixel writes.
- Compositing: Blink's layer-based compositing can produce different blending results than a single-pass software compositor.
- Anti-aliasing quality: Skia (used by Blink) has sophisticated AA; Simple's software renderer has simpler box/gaussian blur approximations.
- For Simple's case: expected divergence areas are (a) text rendering, (b) anti-aliasing edges, (c) glass blur quality (5-pass box blur vs Gaussian), (d) gradient precision (integer vs float interpolation).

**10. SSIM vs Pixel-Level Comparison**
- SSIM evaluates structural, luminance, and contrast similarity — aligns better with human perception. Score range -1 to 1 (>0.8 = good quality).
- Pixel-level (PSNR/direct): treats all differences uniformly, simple and fast, but poor correlation with perceived quality.
- SSIM is better for: compression artifacts, perceptual quality assessment, AI-enhanced images.
- Pixel-level is better for: exact rendering verification, automated training, computational efficiency.
- For Simple's case: use pixel-level comparison as the primary metric (AC-4 requires channel-level precision), but add SSIM as a secondary "perceptual quality" metric for the research report (AC-1) and for tolerance calibration around text/AA regions.

**11. QEMU Screenshot Capture**
- QEMU QMP `screendump` command captures framebuffer to PPM or PNG file.
- QMP syntax: `{"execute": "screendump", "arguments": {"filename": "/tmp/image", "format": "png"}}`
- The existing `qmp_client.spl` does NOT implement screendump — needs a new `qmp_screendump()` function.
- Alternative: for the SimpleOS software compositor, the pixel buffer is directly accessible via `BrowserCompositorBackend.get_pixel_buffer()` — no need for QMP screendump if the test runs in-process. QMP screendump is needed only when capturing from a running QEMU VM externally.

### Open Questions
- NONE (all resolved through codebase + web research)

## Requirements

- REQ-1 (from AC-1): Produce a research report covering industry visual consistency approaches (Chromium fuzzy(), Playwright/pixelmatch, Percy DOM snapshots, BackstopJS/ResembleJS, SSIM) with actionable mappings to Simple's dual-backend architecture. — area: doc/ (report output), references `src/os/compositor/screenshot_compare.spl`
- REQ-2 (from AC-2): Electron host backend must capture reference screenshot as raw ARGB [u32] pixel buffer. Extend `tools/electron-shell/screenshot.js` to export raw ARGB buffer (not just PNG), or add a raw-buffer capture mode to `ElectronBackend`. The `generate_html_page()` in `src/app/ui.electron/backend.spl` provides the HTML; `tools/electron-shell/export_snapshot.js` provides the capture pipeline. — area: `tools/electron-shell/`, `src/app/ui.electron/`
- REQ-3 (from AC-3): QEMU Simple OS backend must capture same scene as raw ARGB [u32]. Two paths: (a) in-process via `BrowserCompositorBackend.get_pixel_buffer()` from `src/os/compositor/browser_compositor_backend.spl`, or (b) external via QMP screendump (needs new `qmp_screendump()` in `src/lib/nogc_sync_mut/qemu/qmp_client.spl`). Use `os.qemu_runner` scenarios (x64-gui or x64-gpu-2d) for QEMU configuration. — area: `src/os/compositor/`, `src/lib/nogc_sync_mut/qemu/`, `src/os/qemu_runner.spl`
- REQ-4 (from AC-4): Image comparison pipeline with configurable per-channel threshold, match percentage, max channel diff, and diff region map. Already implemented in `src/os/compositor/screenshot_compare.spl` — `compare_pixel_buffers()`, `compare_per_channel()`, `find_diff_regions()`. May need addition of YIQ perceptual distance (from pixelmatch research) and configurable tolerance profiles (strict for solid regions, relaxed for text/AA). — area: `src/os/compositor/screenshot_compare.spl`
- REQ-5 (from AC-5): Golden test spec validating >=99% pixel match across both backends. Pattern exists in `test/integration/rendering/backend_screenshot_compare_spec.spl` (MIN_GPU=9990 = 99.90%). New spec should render a standard WM scene (window decorations, glassmorphism, text, desktop chrome) through both Electron and QEMU paths, then use `compare_with_tolerance()`. — area: `test/system/gui/` (new spec alongside `glass_pixel_compare_spec.spl`)
- REQ-6 (from AC-6): Diff visualization when mismatches exceed threshold. Already implemented: `generate_diff_image()` and `generate_channel_diff_image()` in `screenshot_compare.spl`. Need to wire into test pipeline to auto-export diff PPM/PNG on failure. `examples/browser/test/compat/image_export.spl` has `export_ppm()` for file output. — area: `src/os/compositor/screenshot_compare.spl`, `examples/browser/test/compat/image_export.spl`
- REQ-7 (from AC-7): Documentation of rendering divergence root causes and normalization strategies. Root causes identified: font rasterization (FreeType vs Skia/platform), subpixel AA (grayscale vs LCD), color space (sRGB assumption vs host profile), blur quality (box vs Gaussian), gradient interpolation (int vs float), sub-pixel geometry snapping. Normalization strategies: force `--disable-lcd-text` in Electron, render at 2x DPI, use FreeType in both paths, clamp to sRGB, tolerance profiles per region type. — area: doc/ (documentation output)

### 3-arch

## Architecture

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| **perceptual_compare** | `src/os/compositor/perceptual_compare.spl` | YIQ perceptual distance comparison, anti-aliasing detection, tolerance profiles | New |
| **screenshot_compare** | `src/os/compositor/screenshot_compare.spl` | Add `compare_with_profile()` entry point that delegates to perceptual_compare for region-aware thresholds; add diff export wiring | Modified |
| **wm_scene** | `src/os/compositor/wm_scene.spl` | Standard WM scene definition — builds a reference scene (window decorations, glassmorphism panel, text label, desktop chrome gradient) on a `BrowserCompositorBackend` pixel buffer | New |
| **electron_capture** | `src/os/compositor/electron_capture.spl` | Captures Electron reference screenshot: generates HTML via `ElectronBackend.generate_full_page()`, invokes `tools/electron-shell/screenshot.js` for PNG, decodes PNG to raw ARGB `[u32]` | New |
| **qemu_capture** | `src/os/compositor/qemu_capture.spl` | Captures QEMU screenshot via two paths: (a) in-process `BrowserCompositorBackend.get_pixel_buffer()` for unit-level tests, (b) QMP screendump for full-VM tests. Returns ARGB `[u32]` | New |
| **qmp_client** | `src/lib/nogc_sync_mut/qemu/qmp_client.spl` | Add `qmp_screendump()` function for framebuffer capture to PPM/PNG file | Modified |
| **wm_consistency_runner** | `src/os/compositor/wm_consistency_runner.spl` | Orchestrates the full pipeline: render scene through both backends, compare, produce report. Analogous to `glass_comparison_runner.spl` | New |
| **diff_export** | `src/os/compositor/diff_export.spl` | Exports diff visualization artifacts: diff image as PPM, per-channel diffs, annotated region overlay. Wires `generate_diff_image()` + `export_ppm()` | New |
| **tolerance_profile** | `src/os/compositor/tolerance_profile.spl` | Tolerance profile system: per-region-type thresholds (strict for solid fills, relaxed for text/AA/blur regions), profile presets | New |
| **png_decode** | `src/lib/common/image/png_decode.spl` | Minimal PNG decode to ARGB `[u32]` — needed to convert Electron PNG screenshots to raw pixel buffers for comparison | New |
| **golden_test_spec** | `test/system/gui/wm_pixel_consistency_spec.spl` | Golden test: renders standard WM scene through Electron and QEMU paths, asserts >=99% match with tolerance profile | New |
| **divergence_doc** | `doc/09_report/rendering_divergence_normalization.spl` | Research report on rendering divergence root causes and normalization strategies (generated by `wm_consistency_runner` markdown output) | New |

### Dependency Map

```
wm_consistency_runner
  -> wm_scene                    (builds the reference scene)
  -> electron_capture             (captures Electron rendering)
  -> qemu_capture                 (captures QEMU rendering)
  -> screenshot_compare           (core pixel comparison)
  -> perceptual_compare           (YIQ distance, AA detection)
  -> tolerance_profile            (per-region thresholds)
  -> diff_export                  (diff artifact output)

electron_capture
  -> app.ui.electron.backend      (generate_full_page HTML)
  -> std.io                       (shell — invoke electron screenshot.js)
  -> png_decode                   (PNG -> ARGB [u32])

qemu_capture
  -> os.compositor.browser_compositor_backend  (in-process get_pixel_buffer)
  -> std.qemu.qmp_client          (QMP screendump for full-VM path)
  -> os.qemu_runner                (scenario config)
  -> png_decode                    (PPM/PNG -> ARGB [u32])

perceptual_compare
  -> (no project deps — pure math: YIQ conversion, AA heuristic)

tolerance_profile
  -> (no project deps — data structs + presets)

diff_export
  -> os.compositor.screenshot_compare  (generate_diff_image, generate_channel_diff_image)
  -> examples.browser.test.compat.image_export  (export_ppm)

wm_scene
  -> os.compositor.browser_compositor_backend   (pixel buffer backend)
  -> os.compositor.glass_effects                (glassmorphism rendering)
  -> os.compositor.decorations                  (window decoration rendering)
  -> os.compositor.desktop_chrome               (desktop chrome rendering)
  -> os.compositor.text_render                  (text label rendering)

screenshot_compare (modified)
  -> perceptual_compare            (new: YIQ comparison mode)
  -> tolerance_profile             (new: profile-based threshold)

qmp_client (modified)
  -> std.io                        (shell — socat QMP)

png_decode
  -> (no project deps — pure byte parsing)

golden_test_spec
  -> std.spec.*                    (SSpec framework)
  -> wm_consistency_runner         (orchestration)
  -> wm_scene                     (scene definition)
  -> tolerance_profile             (threshold config)

No circular dependencies: verified
```

### Decisions

- **D-1: Extend screenshot_compare.spl rather than replace it** — The existing module has 474 lines of proven pixel comparison logic covering all of AC-4 and AC-6. Adding a `compare_with_profile()` bridge function and importing `perceptual_compare` keeps backward compatibility with the 3 existing test suites that depend on it, while enabling the new YIQ perceptual mode.

- **D-2: YIQ perceptual distance in a separate `perceptual_compare.spl` module** — YIQ color space conversion and anti-aliasing detection are algorithmically distinct from the existing RGB channel-diff logic. Keeping them in a separate module (a) allows the existing `compare_pixel_buffers()` to remain untouched for callers that want pure RGB thresholds, (b) enables independent testing of the YIQ math, (c) follows the pixelmatch algorithm structure (Kotsarenko & Ramos 2010) cleanly.

- **D-3: In-process `BrowserCompositorBackend.get_pixel_buffer()` as primary QEMU capture path, QMP screendump as secondary** — The in-process path avoids the complexity of running a full QEMU VM for every test iteration. It uses the same software compositor that runs inside Simple OS. The QMP screendump path is the true end-to-end validation (captures the actual VM framebuffer) but requires a running QEMU instance. Both paths return the same `CaptureResult` type so the runner treats them uniformly.

- **D-4: Electron capture via existing `screenshot.js` + PNG decode** — Rather than building a new raw ARGB export path in Electron (which would require modifying the JS tool and Electron's NativeImage API), we reuse the existing `screenshot.js` that already captures to PNG, then decode the PNG to ARGB in Simple. This keeps the Electron toolchain unchanged and adds only a simple PNG decoder. The PNG decoder is also reusable for other image comparison workflows.

- **D-5: Tolerance profiles as composable data, not class hierarchy** — Because Simple has NO inheritance, tolerance profiles are plain structs with factory functions (`profile_strict()`, `profile_text_tolerant()`, `profile_glass_blur()`, `profile_wm_default()`). Region-type thresholds are stored as a list of `RegionTolerance` entries that the comparison engine scans. Composition via `merge_profiles()` allows combining multiple presets.

- **D-6: Standard WM scene built programmatically on `BrowserCompositorBackend`** — The reference scene is not loaded from an SDN file but built programmatically by calling compositor drawing operations (fill_rect, blend_rect, blur_region, gradient_v, draw_text). This ensures both the Electron HTML path and the QEMU compositor path render the exact same logical scene. The `wm_scene.spl` module defines `build_reference_scene()` which returns a `WmSceneSpec` describing the scene, and `render_scene_to_backend()` which executes it on any `CompositorBackend`.

- **D-7: Diff visualization as separate export module** — Diff artifacts (diff images, channel heat maps, region overlays) are generated only on comparison failure or explicit request, not on every run. Keeping export logic in `diff_export.spl` separates the comparison hot path from I/O-heavy file writing. The runner calls `export_diff_artifacts()` only when `match_percentage < min_required`.

### Public API

**`src/os/compositor/perceptual_compare.spl`**
- `fn yiq_distance(pixel_a: u32, pixel_b: u32) -> f64` — YIQ perceptual color distance between two ARGB pixels
- `fn is_antialiased(pixels: [u32], x: i32, y: i32, width: i32, height: i32) -> bool` — detect if pixel is AA based on neighbor analysis (Vyshniauskas 2009)
- `fn compare_perceptual(a: [u32], b: [u32], width: i32, height: i32, yiq_threshold: f64, include_aa: bool) -> PerceptualResult` — full perceptual comparison
- `struct PerceptualResult` — mismatched_pixels: i64, total_pixels: i64, match_percentage: i64, aa_pixels: i64

**`src/os/compositor/tolerance_profile.spl`**
- `struct ToleranceProfile` — name: text, default_threshold: i32, default_yiq_threshold: f64, regions: [RegionTolerance]
- `struct RegionTolerance` — region_type: text, threshold: i32, yiq_threshold: f64, min_match_pct: i64
- `fn profile_strict() -> ToleranceProfile` — threshold=0, yiq=0.0, 100% match
- `fn profile_text_tolerant() -> ToleranceProfile` — threshold=8, yiq=0.3 for text regions
- `fn profile_glass_blur() -> ToleranceProfile` — threshold=12, yiq=0.4 for blur regions
- `fn profile_wm_default() -> ToleranceProfile` — composite: strict for fills, tolerant for text/blur
- `fn merge_profiles(base: ToleranceProfile, overlay: ToleranceProfile) -> ToleranceProfile`

**`src/os/compositor/wm_scene.spl`**
- `struct WmSceneSpec` — name: text, width: i32, height: i32, elements: [SceneElement]
- `struct SceneElement` — kind: text, x: i32, y: i32, w: i32, h: i32, properties: [text]
- `fn standard_wm_scene(width: i32, height: i32) -> WmSceneSpec` — builds the reference scene with decorations, glass panel, text, desktop chrome
- `fn render_scene_to_backend(scene: WmSceneSpec, backend: BrowserCompositorBackend) -> [u32]` — renders scene and returns pixel buffer
- `fn scene_to_html(scene: WmSceneSpec) -> text` — converts scene to equivalent HTML for Electron rendering

**`src/os/compositor/electron_capture.spl`**
- `struct CaptureResult` — pixels: [u32], width: i32, height: i32, backend_name: text, success: bool, error: text
- `fn capture_electron(html: text, width: i32, height: i32) -> CaptureResult` — invoke screenshot.js, decode PNG, return ARGB buffer
- `fn capture_electron_scene(scene: WmSceneSpec) -> CaptureResult` — render scene to HTML, capture

**`src/os/compositor/qemu_capture.spl`**
- `fn capture_qemu_inprocess(scene: WmSceneSpec) -> CaptureResult` — render scene on BrowserCompositorBackend, return get_pixel_buffer()
- `fn capture_qemu_vm(qmp_socket: text, output_path: text) -> CaptureResult` — QMP screendump, decode file, return ARGB buffer

**`src/lib/nogc_sync_mut/qemu/qmp_client.spl` (additions)**
- `fn qmp_screendump(client: QmpClient, filename: text, format: text) -> bool` — capture QEMU framebuffer to file

**`src/os/compositor/wm_consistency_runner.spl`**
- `struct ConsistencyReport` — electron_capture: CaptureResult, qemu_capture: CaptureResult, overall: ComparisonResult, perceptual: PerceptualResult, channels: [ChannelDiffResult], diff_regions: [DiffRegion], profile: ToleranceProfile, passed: bool
- `fn run_consistency_check(scene: WmSceneSpec, profile: ToleranceProfile) -> ConsistencyReport` — full pipeline
- `fn consistency_report_to_markdown(report: ConsistencyReport) -> text` — markdown output

**`src/os/compositor/diff_export.spl`**
- `fn export_diff_artifacts(report: ConsistencyReport, output_dir: text) -> bool` — writes diff PPM, channel diffs, region overlay
- `fn export_comparison_ppm(pixels: [u32], width: i32, height: i32, path: text) -> bool` — single image export

**`src/lib/common/image/png_decode.spl`**
- `fn decode_png_to_argb(data: [u8]) -> Result<PngImage, text>` — decode PNG bytes to ARGB pixel buffer
- `struct PngImage` — pixels: [u32], width: i32, height: i32

**`src/os/compositor/screenshot_compare.spl` (additions)**
- `fn compare_with_profile(a: [u32], b: [u32], width: i32, height: i32, profile: ToleranceProfile) -> ComparisonResult` — profile-aware comparison that uses per-region thresholds

### Requirement Coverage

- **REQ-1** (research report) -> `wm_consistency_runner.consistency_report_to_markdown()` generates the report; `doc/09_report/rendering_divergence_normalization.spl` is the output target. The report includes industry comparison methodology (YIQ/pixelmatch, Chromium fuzzy, SSIM notes) and per-divergence-category analysis.
- **REQ-2** (Electron ARGB capture) -> `electron_capture.capture_electron()` + `png_decode.decode_png_to_argb()` + `wm_scene.scene_to_html()`
- **REQ-3** (QEMU ARGB capture) -> `qemu_capture.capture_qemu_inprocess()` (primary) + `qemu_capture.capture_qemu_vm()` (secondary, uses `qmp_client.qmp_screendump()`)
- **REQ-4** (comparison pipeline) -> `screenshot_compare.compare_with_profile()` + `perceptual_compare.compare_perceptual()` + `tolerance_profile` presets
- **REQ-5** (golden test spec) -> `test/system/gui/wm_pixel_consistency_spec.spl` using `wm_consistency_runner.run_consistency_check()` with `profile_wm_default()` and 9900 (99.00%) min match
- **REQ-6** (diff visualization) -> `diff_export.export_diff_artifacts()` wiring `screenshot_compare.generate_diff_image()` + `generate_channel_diff_image()` + PPM export
- **REQ-7** (divergence documentation) -> `doc/09_report/rendering_divergence_normalization.spl` generated from `consistency_report_to_markdown()` + hardcoded normalization strategy sections (font rasterization, subpixel AA, color space, blur quality, gradient interpolation, geometry snapping)

### 4-spec

## Specs

### Spec Files
- `test/unit/os/compositor/perceptual_compare_spec.spl` — 17 specs covering AC-4 (YIQ distance, AA detection, perceptual comparison, threshold sensitivity, AA exclusion)
- `test/unit/os/compositor/tolerance_profile_spec.spl` — 19 specs covering AC-4 (preset profiles, region tolerances, profile merging)
- `test/unit/os/compositor/wm_scene_spec.spl` — 15 specs covering AC-2, AC-3 (scene construction, element types, rendering, HTML conversion)
- `test/unit/os/compositor/electron_capture_spec.spl` — 6 specs covering AC-2 (capture result structure, pixel buffer, scene-level capture)
- `test/unit/os/compositor/qemu_capture_spec.spl` — 9 specs covering AC-3 (in-process capture, VM capture, result uniformity)
- `test/unit/os/compositor/wm_consistency_runner_spec.spl` — 15 specs covering AC-1, AC-4, AC-5, AC-7 (pipeline execution, pass/fail, profile integration, markdown report, divergence docs)
- `test/unit/os/compositor/diff_export_spec.spl` — 5 specs covering AC-6 (single image export, full artifact export)
- `test/unit/lib/common/png_decode_spec.spl` — 8 specs covering AC-2 (signature validation, PngImage structure, pixel output)
- `test/unit/os/compositor/screenshot_compare_profile_spec.spl` — 8 specs covering AC-4 (profile comparison, leniency ordering, result structure)
- `test/qemu/qmp_screendump_spec.spl` — 5 specs covering AC-3 (invalid connection, format parameter, output path)
- `test/system/gui/wm_pixel_consistency_spec.spl` — 19 specs covering AC-1, AC-2, AC-3, AC-4, AC-5, AC-6, AC-7 (golden test, scene rendering, comparison details, diff visualization, report)

**Total: 11 spec files, 126 `it` blocks, 100% AC coverage**

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-1: markdown report is non-empty" | Failing (no impl) |
| AC-1 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-1: markdown report contains match percentage" | Failing (no impl) |
| AC-1 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-1: consistency report produces markdown documentation" | Failing (no impl) |
| AC-1 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-1: markdown includes industry comparison methodology" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: standard scene has correct dimensions" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: scene contains a desktop chrome element" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: scene contains a window decoration element" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: scene contains a glass panel element" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: scene contains a text label element" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: HTML contains doctype or html tag" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-2: HTML contains style information for glass panel" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/electron_capture_spec.spl` | "AC-2: capture_electron returns a CaptureResult with backend_name" | Failing (no impl) |
| AC-2 | `test/unit/os/compositor/electron_capture_spec.spl` | "AC-2: captured result has correct width and height" | Failing (no impl) |
| AC-2 | `test/unit/lib/common/png_decode_spec.spl` | "AC-2: empty bytes returns error" | Failing (no impl) |
| AC-2 | `test/unit/lib/common/png_decode_spec.spl` | "AC-2: non-PNG bytes returns error" | Failing (no impl) |
| AC-2 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-2: Electron captures non-empty pixel buffer for WM scene" | Failing (no impl) |
| AC-2 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-2: Electron capture produces correct-sized buffer" | Failing (no impl) |
| AC-3 | `test/unit/os/compositor/wm_scene_spec.spl` | "AC-3: scene element positions are within bounds" | Failing (no impl) |
| AC-3 | `test/unit/os/compositor/qemu_capture_spec.spl` | "AC-3: in-process capture returns CaptureResult with backend_name" | Failing (no impl) |
| AC-3 | `test/unit/os/compositor/qemu_capture_spec.spl` | "AC-3: in-process capture returns non-empty pixel buffer" | Failing (no impl) |
| AC-3 | `test/unit/os/compositor/qemu_capture_spec.spl` | "AC-3: in-process capture pixel buffer has correct size" | Failing (no impl) |
| AC-3 | `test/unit/os/compositor/qemu_capture_spec.spl` | "AC-3: VM capture with invalid socket returns error" | Failing (no impl) |
| AC-3 | `test/qemu/qmp_screendump_spec.spl` | "AC-3: screendump with non-existent socket returns false" | Failing (no impl) |
| AC-3 | `test/qemu/qmp_screendump_spec.spl` | "AC-3: screendump accepts 'png' format" | Failing (no impl) |
| AC-3 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-3: QEMU in-process captures non-empty pixel buffer" | Failing (no impl) |
| AC-3 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-3: QEMU in-process produces correct-sized buffer" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/perceptual_compare_spec.spl` | "AC-4: returns zero distance for identical black pixels" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/perceptual_compare_spec.spl` | "AC-4: returns large distance for black vs white" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/perceptual_compare_spec.spl` | "AC-4: pixel in uniform solid block is not antialiased" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/perceptual_compare_spec.spl` | "AC-4: identical buffers yield 100% match and zero mismatches" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/perceptual_compare_spec.spl` | "AC-4: zero threshold makes any difference a mismatch" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/perceptual_compare_spec.spl` | "AC-4: include_aa=false excludes AA pixels from mismatch count" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/tolerance_profile_spec.spl` | "AC-4: strict profile has zero default threshold" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/tolerance_profile_spec.spl` | "AC-4: wm default profile has multiple region tolerances" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/tolerance_profile_spec.spl` | "AC-4: merged profile takes overlay name" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/screenshot_compare_profile_spec.spl` | "AC-4: identical buffers with strict profile return 100% match" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/screenshot_compare_profile_spec.spl` | "AC-4: text_tolerant profile is more lenient than strict for same diff" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/screenshot_compare_profile_spec.spl` | "AC-4: result has max_channel_diff field" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-4: report has overall comparison result with match_percentage" | Failing (no impl) |
| AC-4 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-4: report has per-channel diff results" | Failing (no impl) |
| AC-4 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-4: comparison reports max channel diff" | Failing (no impl) |
| AC-4 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-4: perceptual result reports AA pixel count" | Failing (no impl) |
| AC-5 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-5: run_consistency_check returns a ConsistencyReport" | Failing (no impl) |
| AC-5 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-5: report has passed boolean field" | Failing (no impl) |
| AC-5 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-5: pixel match percentage is >= 99% with wm_default profile" | Failing (no impl) |
| AC-5 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-5: golden test passes with tolerance profile" | Failing (no impl) |
| AC-5 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-5: strict profile comparison provides baseline metrics" | Failing (no impl) |
| AC-6 | `test/unit/os/compositor/diff_export_spec.spl` | "AC-6: export_comparison_ppm returns true for valid buffer" | Failing (no impl) |
| AC-6 | `test/unit/os/compositor/diff_export_spec.spl` | "AC-6: export_comparison_ppm with empty pixels returns false" | Failing (no impl) |
| AC-6 | `test/unit/os/compositor/diff_export_spec.spl` | "AC-6: export_diff_artifacts returns true for valid report" | Failing (no impl) |
| AC-6 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-6: diff artifacts can be exported from consistency report" | Failing (no impl) |
| AC-6 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-6: diff image generation works with captured buffers" | Failing (no impl) |
| AC-7 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-7: markdown report contains divergence analysis" | Failing (no impl) |
| AC-7 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-7: markdown report documents font rasterization differences" | Failing (no impl) |
| AC-7 | `test/unit/os/compositor/wm_consistency_runner_spec.spl` | "AC-7: markdown report documents anti-aliasing normalization" | Failing (no impl) |
| AC-7 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-7: markdown documents rendering divergence root causes" | Failing (no impl) |
| AC-7 | `test/system/gui/wm_pixel_consistency_spec.spl` | "AC-7: markdown documents normalization strategies" | Failing (no impl) |

### 5-implement

## Implementation Files

| # | File | Lines | Role | Status |
|---|------|-------|------|--------|
| 1 | `src/os/compositor/perceptual_compare.spl` | 219 | YIQ perceptual distance, AA detection, full comparison | New |
| 2 | `src/os/compositor/tolerance_profile.spl` | 159 | Composable tolerance profiles: strict, text, blur, wm_default, merge | New |
| 3 | `src/lib/common/image/png_decode.spl` | 210 | Minimal PNG decoder: signature, IHDR, IDAT, ARGB output | New |
| 4 | `src/lib/common/image/__init__.spl` | 3 | Module init: re-exports decode_png_to_argb, PngImage | New |
| 5 | `src/os/compositor/wm_scene.spl` | 182 | Standard WM scene builder: desktop chrome, decoration, glass, text; HTML conversion | New |
| 6 | `src/os/compositor/screenshot_compare.spl` | +70 | Added compare_with_profile(), generate_diff_image_threshold(), ToleranceProfile import | Modified |
| 7 | `src/lib/nogc_sync_mut/qemu/qmp_client.spl` | +25 | Added qmp_screendump() for framebuffer capture to PNG/PPM | Modified |
| 8 | `src/os/compositor/electron_capture.spl` | 132 | Electron capture: HTML write, screenshot.js invoke, PNG decode to ARGB | New |
| 9 | `src/os/compositor/qemu_capture.spl` | 107 | QEMU capture: in-process via BrowserCompositorBackend, VM via QMP screendump | New |
| 10 | `src/os/compositor/diff_export.spl` | 126 | Diff artifact export: PPM diff images, channel diffs, directory creation | New |
| 11 | `src/os/compositor/wm_consistency_runner.spl` | 231 | Pipeline orchestrator: capture both, compare, perceptual, channels, regions, report | New |
| 12 | `doc/09_report/rendering_divergence_normalization.spl` | 91 | Divergence report: root causes, normalization strategies, structured categories | New |

**Total: 10 new files, 2 modified files, ~1,555 lines of implementation**

### Implementation Notes

- **No pass_todo stubs**: All functions fully implemented
- **No inheritance**: All types are structs with factory functions (D-5)
- **Proper imports**: Uses `std.nogc_sync_mut.ffi.io` for file I/O, `std.io` for shell, `std.common.image.png_decode` for PNG
- **Backward compatible**: Existing `generate_diff_image()` (4-arg) unchanged; new `generate_diff_image_threshold()` (5-arg) added alongside; `compare_with_profile()` added without modifying existing comparison functions
- **Circular dependency free**: `diff_export -> wm_consistency_runner` is one-way; runner does NOT import diff_export
- **Interpreter mode**: Test runner verifies file loading only; `it` block bodies don't execute. Implementation focuses on compile-clean code matching spec signatures

### 6-refactor

## Refactor Summary

**All files under 800 lines** — largest is `screenshot_compare.spl` at 505 lines.

### Changes Made

1. **`screenshot_compare.spl`** (551 -> 505 lines):
   - **Dedup**: `generate_diff_image()` was a near-exact copy of `generate_diff_image_threshold()` (with threshold=0). Refactored `generate_diff_image()` to delegate to `generate_diff_image_threshold(a, b, width, height, 0)`, eliminating 35 lines of duplicated pixel-loop logic.
   - **Dead code**: Removed duplicate empty "Single-Channel Diff Image" section header (appeared twice, the first was empty).

2. **`electron_capture.spl`** (132 -> 108 lines):
   - **Dedup**: Extracted `capture_error()` helper function for constructing error `CaptureResult` values. Replaced 5 identical 7-line error construction blocks with single-line calls.
   - **Unused import**: Removed `shell_output` from imports (only `shell` is used).

3. **`qemu_capture.spl`** (107 -> 86 lines):
   - **Dedup**: Now imports and uses `capture_error()` from `electron_capture.spl`. Replaced 3 error construction blocks with single-line calls.

4. **`qmp_client.spl`** (105 -> 100 lines):
   - **Dedup**: Extracted `qmp_send()` and `qmp_send_check()` internal helpers. The socat shell command pattern (`echo '...' | socat - UNIX-CONNECT:...`) was repeated 6 times. Now `qmp_send()` handles command dispatch and `qmp_send_check()` handles the exit-code + error-string check. All 6 callers now use these helpers.
   - **Dead code**: Removed empty "Exports" section at end of file.
   - **Unused import**: Removed `shell_output` from imports (only `shell` is used).

### Issues Reviewed But Not Changed

- **ARGB pixel extraction pattern** (`(pixel >> 16) & 0xFF` etc.) appears ~10 times across `screenshot_compare.spl`, `perceptual_compare.spl`, and `diff_export.spl`. NOT extracted because each context needs different types (i32 vs f64 vs u8 vs u32) and extraction would add function call overhead in hot pixel loops without meaningful clarity gain.
- **`CaptureResult` struct** defined once in `electron_capture.spl`, imported everywhere else — no duplication.
- **`perceptual_compare.spl`** (219 lines): Clean, no issues found. YIQ math functions are self-contained.
- **`tolerance_profile.spl`** (159 lines): Clean, no issues found. All factory functions follow consistent pattern.
- **`png_decode.spl`** (210 lines): Clean, no issues found.
- **`wm_scene.spl`** (182 lines): Clean, no issues found. `get_property()` helper is used once but worth keeping for readability.
- **`diff_export.spl`** (126 lines): Clean, no issues found.
- **`wm_consistency_runner.spl`** (231 lines): Clean, no issues found. Large markdown generation function is inherently verbose but well-structured.
- **`rendering_divergence_normalization.spl`** (91 lines): Clean, no issues found.
- **Spec files**: Reviewed briefly, no issues. All use built-in SSpec matchers correctly.

### Final Line Counts

| File | Before | After |
|------|--------|-------|
| `screenshot_compare.spl` | 551 | 505 |
| `electron_capture.spl` | 132 | 108 |
| `qemu_capture.spl` | 107 | 86 |
| `qmp_client.spl` | 105 | 100 |
| Others (8 files) | unchanged | unchanged |

### Exit Criteria

- [x] No file exceeds 800 lines (max: 505)
- [x] Duplication check: `generate_diff_image` dedup, `capture_error` extraction, `qmp_send` extraction
- [x] Unused imports removed (`shell_output` in 2 files)
- [x] Dead code removed (empty section headers, empty export section)
- [x] Naming conventions consistent (snake_case functions, PascalCase types throughout)
- [x] No behavior changes — all refactors are structural only

### 7-verify
<pending>

### 8-ship
<pending>

## Phase
refactor-done

## Log
- intake: Created state file with 7 acceptance criteria
- research: Found 15 reusable modules, 20+ existing files analyzed, 7 requirements drafted. Intensive web research: 10 domain topics (Chromium pixel tests, Playwright/pixelmatch, Percy, BackstopJS, font rasterization, subpixel AA, color spaces, Blink vs software renderer, SSIM vs pixel comparison, QEMU screendump). Key finding: existing `screenshot_compare.spl` covers ~80% of needed comparison logic; main gaps are (1) QMP screendump for QEMU capture, (2) Electron raw ARGB export, (3) YIQ perceptual distance upgrade, (4) golden test spec wiring both backends.
- arch: Designed 12 modules (8 new, 2 modified, 1 test spec, 1 doc output), 7 architecture decisions, no circular deps. Key decisions: YIQ perceptual compare as separate module (D-2), in-process BrowserCompositorBackend as primary QEMU path (D-3), Electron via existing screenshot.js + PNG decode (D-4), tolerance profiles as composable data structs (D-5), programmatic scene builder for deterministic cross-backend rendering (D-6). All 7 REQs covered.
- spec: Created 11 spec files with 126 total `it` blocks, 100% AC coverage (all 7 ACs). Key specs: perceptual_compare (17 tests for YIQ/AA/threshold), tolerance_profile (19 tests for presets/merge), wm_scene (15 tests for construction/rendering/HTML), golden test (19 end-to-end tests). All specs FAIL — no implementation exists. Only built-in SSpec matchers used.
- implement: Created 10 new files + modified 2 existing files (~1,555 lines). Key implementations: YIQ perceptual compare (Kotsarenko/Ramos 2010, Vyshniauskas 2009 AA detection), composable tolerance profiles (5 presets + merge), PNG decoder (signature/IHDR/IDAT), programmatic WM scene builder (4 element types + HTML conversion), Electron capture (screenshot.js + PNG decode), QEMU capture (in-process + QMP screendump), diff export (PPM with channel diffs), consistency runner (full pipeline + markdown report with divergence analysis). No pass_todo stubs, no circular deps, backward compatible modifications.
- refactor: 4 files modified (screenshot_compare, electron_capture, qemu_capture, qmp_client). Key changes: (1) `generate_diff_image` deduped to delegate to `generate_diff_image_threshold`, (2) `capture_error()` helper extracted and shared across electron/qemu capture, (3) `qmp_send()`/`qmp_send_check()` extracted to eliminate 6x socat pattern repetition, (4) removed unused imports (`shell_output` x2) and dead code (empty sections x3). Net reduction: ~65 lines. No behavior changes, all structural only.
