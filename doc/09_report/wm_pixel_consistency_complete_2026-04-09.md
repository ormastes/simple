# WM Pixel Consistency -- Completion Report

**Date:** 2026-04-09
**Pipeline:** SStack 8-phase
**Feature:** wm-pixel-consistency

## Summary

Build a pixel-level visual consistency verification pipeline that renders the same WM/compositor scene through the unified host and in-process QEMU capture paths, then compares the output at bit/color level to ensure rendering equivalence across the shared compositor backend. Electron remains a preview/display path only.

## Architecture

7 architecture decisions were made in Phase 3:

- **D-1: Extend screenshot_compare.spl rather than replace it** -- The existing module has 474 lines of proven pixel comparison logic. Added `compare_with_profile()` bridge function while preserving backward compatibility with the 3 existing test suites.

- **D-2: YIQ perceptual distance in a separate perceptual_compare.spl module** -- Algorithmically distinct from existing RGB channel-diff logic. Enables independent testing of the YIQ math (Kotsarenko & Ramos 2010) and anti-aliasing detection (Vyshniauskas 2009).

- **D-3: In-process BrowserCompositorBackend.get_pixel_buffer() as primary QEMU capture path, QMP screendump as secondary** -- In-process path avoids full QEMU VM for every test iteration. QMP screendump serves as true end-to-end validation when a running QEMU instance is available.

- **D-4: Electron capture via existing screenshot.js + PNG decode** -- Reuses existing `screenshot.js` that captures to PNG, then decodes PNG to ARGB in Simple. Keeps the Electron toolchain unchanged.

- **D-5: Tolerance profiles as composable data, not class hierarchy** -- Plain structs with factory functions (`profile_strict()`, `profile_text_tolerant()`, `profile_glass_blur()`, `profile_wm_default()`). Composition via `merge_profiles()`.

- **D-6: Standard WM scene built programmatically on BrowserCompositorBackend** -- Reference scene built by calling compositor drawing operations, ensuring both Electron HTML path and QEMU compositor path render the exact same logical scene.

- **D-7: Diff visualization as separate export module** -- Diff artifacts generated only on comparison failure or explicit request, keeping the comparison hot path free of I/O overhead.

## Files

### New Implementation Files (10)
- `src/os/compositor/perceptual_compare.spl` (219 lines) -- YIQ perceptual distance, AA detection, full comparison
- `src/os/compositor/tolerance_profile.spl` (159 lines) -- Composable tolerance profiles: strict, text, blur, wm_default, merge
- `src/os/compositor/wm_scene.spl` (182 lines) -- Standard WM scene builder: desktop chrome, decoration, glass, text; HTML conversion
- `src/os/compositor/electron_capture.spl` (108 lines) -- Electron capture: HTML write, screenshot.js invoke, PNG decode to ARGB
- `src/os/compositor/qemu_capture.spl` (86 lines) -- QEMU capture: in-process via BrowserCompositorBackend, VM via QMP screendump
- `src/os/compositor/wm_consistency_runner.spl` (231 lines) -- Pipeline orchestrator: capture both, compare, perceptual, channels, regions, report
- `src/os/compositor/diff_export.spl` (126 lines) -- Diff artifact export: PPM diff images, channel diffs, directory creation
- `src/lib/common/image/png_decode.spl` (210 lines) -- Minimal PNG decoder: signature, IHDR, IDAT, ARGB output
- `src/lib/common/image/__init__.spl` (3 lines) -- Module init: re-exports decode_png_to_argb, PngImage
- `doc/09_report/rendering_divergence_normalization.spl` (91 lines) -- Divergence report: root causes, normalization strategies

### Modified Files (2)
- `src/os/compositor/screenshot_compare.spl` (+70 lines) -- Added compare_with_profile(), generate_diff_image_threshold(), ToleranceProfile import
- `src/lib/nogc_sync_mut/qemu/qmp_client.spl` (+25 lines) -- Added qmp_screendump() for framebuffer capture to PNG/PPM

### Spec Files (11)
- `test/unit/os/compositor/perceptual_compare_spec.spl` -- 17 specs (AC-4)
- `test/unit/os/compositor/tolerance_profile_spec.spl` -- 19 specs (AC-4)
- `test/unit/os/compositor/wm_scene_spec.spl` -- 15 specs (AC-2, AC-3)
- `test/unit/os/compositor/electron_capture_spec.spl` -- 6 specs (AC-2)
- `test/unit/os/compositor/qemu_capture_spec.spl` -- 9 specs (AC-3)
- `test/unit/os/compositor/wm_consistency_runner_spec.spl` -- 15 specs (AC-1, AC-4, AC-5, AC-7)
- `test/unit/os/compositor/diff_export_spec.spl` -- 5 specs (AC-6)
- `test/unit/lib/common/png_decode_spec.spl` -- 8 specs (AC-2)
- `test/unit/os/compositor/screenshot_compare_profile_spec.spl` -- 8 specs (AC-4)
- `test/qemu/qmp_screendump_spec.spl` -- 5 specs (AC-3)
- `test/system/gui/wm_pixel_consistency_spec.spl` -- 19 specs (AC-1 through AC-7)

## Verification

- Tests: 126 `it` blocks across 11 spec files
- AC Coverage: 100% (all 7 ACs covered)
- Lint: clean
- Refactor: 4 files cleaned (dedup, dead code removal, helper extraction), net -65 lines
- No pass_todo stubs, no circular dependencies, backward compatible modifications

## Acceptance Criteria

| AC | Description | Status |
|----|-------------|--------|
| AC-1 | Research report covering industry pixel consistency tools | Verified |
| AC-2 | Electron host captures reference screenshot as raw ARGB [u32] | Verified |
| AC-3 | QEMU Simple OS captures same scene as raw ARGB [u32] | Verified |
| AC-4 | Comparison pipeline with per-channel threshold, match %, diff regions | Verified |
| AC-5 | Golden test validates >=99% pixel match across both backends | Verified |
| AC-6 | Diff visualization on threshold exceedance | Verified |
| AC-7 | Documentation of rendering divergence root causes and normalization | Verified |

## Timeline

| Phase | Status | Date |
|-------|--------|------|
| 1. Intake (Developer Lead) | done | 2026-04-09 |
| 2. Research (Analyst) | done | 2026-04-09 |
| 3. Architecture (Architect) | done | 2026-04-09 |
| 4. Spec (QA Lead) | done | 2026-04-09 |
| 5. Implement (Engineer) | done | 2026-04-09 |
| 6. Refactor (Tech Lead) | done | 2026-04-09 |
| 7. Verify (QA) | done | 2026-04-09 |
| 8. Ship (Release Mgr) | done | 2026-04-09 |
