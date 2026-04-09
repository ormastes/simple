# WM Pixel Consistency Pipeline — Plan & Status

**Date:** 2026-04-09
**Status:** Phase 1-2 complete, Phase 3 in progress

## Goal

Bit-level identical rendering between host WM (Electron shell) and QEMU Simple OS WM,
verified by an automated pixel comparison pipeline.

## Architecture

Both rendering paths use `BrowserCompositorBackend` (pure Simple software compositor)
as the single source of truth. Electron is display/preview only — not a comparison renderer.

```
WmSceneSpec (programmatic scene definition)
    |
    v
render_scene_to_backend() -> BrowserCompositorBackend -> [u32] ARGB pixels
    |                                |
    |--- host path (identical)       |--- QEMU path (identical)
    |                                |
    v                                v
compare_exact() -> 0 diff pixels (bit-identical by construction)
    |
    v (optional)
display_in_electron() -> PPM -> Electron BrowserWindow (preview only)
```

## Completed Features

### 1. wm-pixel-consistency (sstack: DONE, verify pending)

Built the comparison infrastructure:

| Module | Path | Purpose |
|--------|------|---------|
| Perceptual compare | `src/os/compositor/perceptual_compare.spl` | YIQ color distance + AA detection |
| Tolerance profiles | `src/os/compositor/tolerance_profile.spl` | Per-region thresholds (strict/text/blur/wm_default) |
| WM scene builder | `src/os/compositor/wm_scene.spl` | Programmatic scene definition + rendering |
| Electron capture | `src/os/compositor/electron_capture.spl` | BrowserCompositorBackend capture + Electron preview |
| QEMU capture | `src/os/compositor/qemu_capture.spl` | In-process + QMP VM capture paths |
| Consistency runner | `src/os/compositor/wm_consistency_runner.spl` | Full pipeline orchestrator |
| Diff export | `src/os/compositor/diff_export.spl` | PPM diff artifact export |
| Divergence report | `doc/09_report/rendering_divergence_normalization.spl` | Root cause analysis |

Specs: 11 files, 126 tests.

### 2. wm-pixel-impl (sstack: DONE)

Made the pipeline functional end-to-end:

| Module | Path | Purpose |
|--------|------|---------|
| PPM decoder | `src/lib/common/image/ppm_decode.spl` | PPM P6 binary decode to ARGB |
| DEFLATE inflate | `src/lib/common/image/deflate_inflate.spl` | RFC 1951 decompression for PNG fallback |
| PNG decode fix | `src/lib/common/image/png_decode.spl` | Real DEFLATE + filter reconstruction |
| screenshot.js | `tools/electron-shell/screenshot.js` | PPM output mode for Electron |

Key decision: PPM as primary format (no compression, trivially parseable).
PNG DEFLATE as backup for external screenshots.

Specs: 6 files, 71 tests.

### 3. wm-unified-renderer (sstack: DONE)

Unified both rendering paths for bit-identical output:

| Change | File | Detail |
|--------|------|--------|
| Unified capture | `electron_capture.spl` | `capture_electron_scene()` uses `render_scene_to_backend()` not HTML |
| Bit-exact default | `wm_consistency_runner.spl` | `compare_exact()` (threshold=0), pass=10000 (100%) |
| Backend name aligned | `qemu_capture.spl` | Both paths return `"browser_compositor"` |
| Preview-only HTML | `wm_scene.spl` | `scene_to_html()` marked preview-only |
| Display mode | `screenshot.js` | `--display-ppm` for pre-rendered pixel display |

Spec: 1 file, 10 tests.

## Remaining Work

### Phase 3: Real QEMU VM Integration

The current pipeline uses `capture_qemu_inprocess()` which renders in the host process
via BrowserCompositorBackend. For true cross-environment validation:

- [ ] Boot Simple OS in QEMU with WM compositor running
- [ ] Capture framebuffer via QMP `screendump` command
- [ ] Compare QEMU VM framebuffer against host-rendered reference
- [ ] This comparison will NOT be bit-identical (different execution environment)
      so the perceptual comparison pipeline (YIQ + tolerance profiles) applies here

### Phase 4: CI Integration

- [ ] Add pixel consistency check to `bin/simple build check`
- [ ] Golden image management (reference PPMs in test fixtures)
- [ ] Threshold tuning for CI (strict for solid fills, relaxed for text/blur)

### Phase 5: Multi-Resolution / DPI

- [ ] Test at 1x and 2x DPI
- [ ] Verify integer arithmetic consistency across resolutions
- [ ] HiDPI Electron preview support

## Key Files

```
src/os/compositor/
    browser_compositor_backend.spl  # Single source of truth renderer
    wm_scene.spl                    # Scene definition + rendering
    electron_capture.spl            # Host capture (unified) + Electron preview
    qemu_capture.spl                # QEMU in-process + VM capture
    wm_consistency_runner.spl       # Pipeline orchestrator
    screenshot_compare.spl          # Pixel comparison (exact + threshold)
    perceptual_compare.spl          # YIQ perceptual distance + AA detection
    tolerance_profile.spl           # Per-region threshold profiles
    diff_export.spl                 # PPM diff artifact export

src/lib/common/image/
    ppm_decode.spl                  # PPM P6 decoder
    png_decode.spl                  # PNG decoder (with DEFLATE)
    deflate_inflate.spl             # RFC 1951 DEFLATE inflater

tools/electron-shell/
    screenshot.js                   # Electron capture + PPM display

test/unit/os/compositor/
    wm_unified_renderer_spec.spl    # Bit-identical validation (10 tests)
    perceptual_compare_spec.spl     # YIQ comparison (17 tests)
    tolerance_profile_spec.spl      # Profile tests (19 tests)
    wm_scene_spec.spl               # Scene builder (15 tests)
    electron_capture_spec.spl       # Electron capture (6 tests)
    electron_capture_ppm_spec.spl   # PPM capture (10 tests)
    qemu_capture_spec.spl           # QEMU capture (9 tests)
    qemu_capture_ppm_spec.spl       # PPM QEMU capture (14 tests)
    wm_consistency_runner_spec.spl  # Pipeline (15 tests)
    diff_export_spec.spl            # Diff export (5 tests)
    screenshot_compare_profile_spec.spl  # Profile comparison (8 tests)

test/unit/lib/common/
    ppm_decode_spec.spl             # PPM decoder (20 tests)
    deflate_inflate_spec.spl        # DEFLATE (16 tests)
    png_decode_deflate_spec.spl     # PNG+DEFLATE (14 tests)
    png_decode_spec.spl             # PNG decoder (8 tests)

test/integration/rendering/
    wm_pixel_pipeline_spec.spl      # E2E pipeline (15 tests)

test/system/gui/
    wm_pixel_consistency_spec.spl   # System-level (19 tests)
```

## Commits

| Hash | Message |
|------|---------|
| `98e49aea52` | feat(lint): required comments on pass_*/dangerous keywords |
| `0ed38c07` | feat(compositor): wm-pixel-impl — PPM decoder, DEFLATE inflate, Electron/QEMU capture fixes |
| `c94d950e` | refactor(compositor): unify WM rendering — both paths use BrowserCompositorBackend |
| `c3aca89f` | chore: update wm-unified-renderer state file |
