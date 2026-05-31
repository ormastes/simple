# Windows Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/platform/windows_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SPipe scenarios.

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

golden gate of `doc/03_plan/gui_drawing_layer_variations.md` (golden-image
gate: same app, four backends, exact pixel parity) lands on top of
the framebuffer/software gate framebuffer/software parity harness. The gate detects unintentional drift
in the windowed compositor pipeline by serializing every parity scene
to a PPM P6 reference image and re-comparing on every test run.

| Field | Value |
|-------|-------|
| Gate spec | `test/system/wm_compare/golden_gate_spec.spl` |
| Gate runner | `src/app/wm_compare/golden_gate.spl` |
| Goldens | `test/system/wm_compare/goldens/<scene>.ppm` |
| Format | PPM P6 (binary, RGB888, 32x16) — alpha dropped, all parity scenes are opaque |
| Backend under reference | framebuffer baseline (`FramebufferDriver.from_buffer`, the `fb_backend` code path) |
| Threshold | exact pixel equality; perceptual values are diagnostic only |
| Scenes | `solid_fill`, `fill_rect_row_edge`, `text_with_bg`, `glass_blend` (the framebuffer/software gate set) |

### How the gate runs

1. `golden_gate_spec.spl` calls `check_golden(scene)` for every scene.
2. `check_golden` re-renders the scene through framebuffer baseline (`render_framebuffer_baseline`), loads
   `goldens/<scene>.ppm`, decodes to ARGB8888, and diffs both buffers
   with the same `diff_buffers` helper framebuffer/software gate uses.
3. The gate passes only when the rendered pixels are exactly equal to
   the golden image. Perceptual and channel-delta values remain in the
   report as diagnostics and must not accept a GUI hardening result.

### Regenerating goldens

After an intentional rendering change, set the `REGEN_GOLDENS`
environment variable when running the gate:

```bash
REGEN_GOLDENS=1 bin/simple test test/system/wm_compare/golden_gate_spec.spl
```

`check_golden` then writes the freshly rendered framebuffer baseline buffer back to
`test/sys/wm_compare/goldens/<scene>.ppm` and reports the run as
`regenerated=true`. Inspect the new PPMs (`feh`, `display`, or any
PNM viewer), then commit them with `jj commit`.

### Backends covered

golden gate of the variations matrix calls for four backends:

| Backend | Status in the gate |
|---|---|
| framebuffer baseline — `fb_backend` (`FramebufferDriver.from_buffer`) | Locked — every golden is generated from this path |
| software reference — pure-Simple `hosted_backend` math (`render_software_reference` in `backend_parity.spl`) | Indirect — framebuffer/software gate spec already locks framebuffer baseline == software reference byte-for-byte, so a software reference drift trips framebuffer/software gate first and golden gate second |
| browser shell — `browser_compositor_backend` | Pending browser-shell gate (`v3_simple_browser_milestones.md`); the gate's `check_golden` is shaped so adding a `render_browser_shell` variant only needs another comparison call |
| electron reference — `electron_capture` | Pending electron-reference gate; same extension shape as browser shell |

The gate is the same artifact pointed at by golden gate in
`doc/03_plan/gui_drawing_layer_variations.md`, and its pass/fail
state is what the matrix tracks for that row.
