# Windows Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/platform/windows_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/platform/windows/result.json` |

## Scenarios

- converts forward slashes to backslashes
- handles drive letters correctly
- converts UNC paths correctly
- handles mixed slashes
- detects MinGW-style paths
- rejects non-MinGW paths
- converts MinGW paths to Windows format
- converts Windows paths to MinGW format
- treats MinGW paths as absolute
- dir_sep returns backslash
- path_sep returns semicolon
- exe_ext returns .exe
- adds .exe extension to commands without extension
- preserves commands with .exe extension
- handles .bat and .cmd files
- preserves absolute paths
- joins paths with backslashes
- extracts file names from Windows paths
- handles UNC paths in Path class
- executes cmd.exe commands
- captures stdout correctly
- can check if MSVC is available
- can check if lld-link is available
- Windows linker type has string representation

## Golden-image gate

Row 8 of `doc/03_plan/gui_drawing_layer_variations.md` (golden-image
gate: same app, four backends, ≤1 % perceptual diff) lands on top of
the Row 2 V1/V2 parity harness. The gate detects unintentional drift
in the windowed compositor pipeline by serializing every parity scene
to a PPM P6 reference image and re-comparing on every test run.

| Field | Value |
|-------|-------|
| Gate spec | `test/sys/wm_compare/golden_gate_spec.spl` |
| Gate runner | `src/app/wm_compare/golden_gate.spl` |
| Goldens | `test/sys/wm_compare/goldens/<scene>.ppm` |
| Format | PPM P6 (binary, RGB888, 32x16) — alpha dropped, all parity scenes are opaque |
| Backend under reference | V1 (`FramebufferDriver.from_buffer`, the `fb_backend` code path) |
| Threshold | `pass_perceptual` (≤1 % differing pixels) AND `max_channel_delta <= 2` |
| Scenes | `solid_fill`, `fill_rect_row_edge`, `text_with_bg`, `glass_blend` (the Row 2 set) |

### How the gate runs

1. `golden_gate_spec.spl` calls `check_golden(scene)` for every scene.
2. `check_golden` re-renders the scene through V1 (`render_v1`), loads
   `goldens/<scene>.ppm`, decodes to ARGB8888, and diffs both buffers
   with the same `diff_buffers` helper Row 2 uses.
3. The gate passes when both `ParityResult.pass_perceptual` is true
   and the maximum per-channel delta is at most 2 — i.e. the gate is
   for drift detection, not for perfect pixel comparison.

### Regenerating goldens

After an intentional rendering change, set the `REGEN_GOLDENS`
environment variable when running the gate:

```bash
REGEN_GOLDENS=1 bin/simple test test/sys/wm_compare/golden_gate_spec.spl
```

`check_golden` then writes the freshly rendered V1 buffer back to
`test/sys/wm_compare/goldens/<scene>.ppm` and reports the run as
`regenerated=true`. Inspect the new PPMs (`feh`, `display`, or any
PNM viewer), then commit them with `jj commit`.

### Backends covered

Row 8 of the variations matrix calls for four backends:

| Backend | Status in the gate |
|---|---|
| V1 — `fb_backend` (`FramebufferDriver.from_buffer`) | Locked — every golden is generated from this path |
| V2 — pure-Simple `hosted_backend` math (`render_v2` in `v1_v2_parity.spl`) | Indirect — Row 2 spec already locks V1 == V2 byte-for-byte, so a V2 drift trips Row 2 first and Row 8 second |
| V3 — `browser_compositor_backend` | Pending Row 5 (`v3_simple_browser_milestones.md`); the gate's `check_golden` is shaped so adding a `render_v3` variant only needs another comparison call |
| V4 — `electron_capture` | Pending Row 6; same extension shape as V3 |

The gate is the same artifact pointed at by Row 8 in
`doc/03_plan/gui_drawing_layer_variations.md`, and its pass/fail
state is what the matrix tracks for that row.
