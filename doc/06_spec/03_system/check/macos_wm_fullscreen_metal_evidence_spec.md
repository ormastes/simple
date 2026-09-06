# macOS WM fullscreen Metal evidence gate

> Validates the macOS host WM windowed/fullscreen Metal evidence gate: `scripts/check/check-macos-wm-fullscreen-metal-evidence.shs`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS WM fullscreen Metal evidence gate

Validates the macOS host WM windowed/fullscreen Metal evidence gate: `scripts/check/check-macos-wm-fullscreen-metal-evidence.shs`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_wm_fullscreen_metal_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the macOS host WM windowed/fullscreen Metal evidence gate:
`scripts/check/check-macos-wm-fullscreen-metal-evidence.shs`.

The gate launches `examples/06_io/ui/wm_fullscreen_metal_gui.spl` for real via a
`.app` bundle (so LaunchServices registers it with the window server and Metal
can create a device), toggles the window between windowed and borderless
fullscreen through the winit `rt_winit_window_set_fullscreen` runtime setter, and
proves both modes with genuine `gpu_frame_complete=true` GPU-lane markers plus a
real `screencapture` during the fullscreen dwell.

This spec is portable: it always validates that the gate script, the demo app,
and the Simple winit fullscreen wrappers ship with the expected contract. When a
real macOS evidence run has produced `build/wm_fullscreen_metal_evidence/report.md`
it additionally validates the report fields (status, sizes, GPU frame count,
restored marker).

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/macos_wm_fullscreen_metal_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

## Host Notes

A real fullscreen-window proof is platform-local (macOS + Metal). The gate itself
skips cleanly on non-macOS hosts. This spec runs anywhere: the report-field
assertions only fire when a macOS run has produced the report.

## Completion Keys

```text
wm_fullscreen_metal_status=pass
wm_fullscreen_metal_restored=true
```

## Scenarios

### macOS WM fullscreen Metal evidence gate

#### ships the gate script with the windowed+fullscreen+restored contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ships the gate script with the windowed+fullscreen+restored contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ships the gate script with the windowed+fullscreen+restored contract")
val gate = file_read(GATE)
expect(gate).to_contain("wm_fullscreen_metal_status")
expect(gate).to_contain("mode=windowed")
expect(gate).to_contain("mode=fullscreen")
expect(gate).to_contain("restored=true")
expect(gate).to_contain("gpu_frame_complete=true")
# Hard gate must require the fullscreen size to exceed the windowed size.
expect(gate).to_contain("fullscreen-not-larger")
# Real screenshot during fullscreen, degenerate capture is non-fatal.
expect(gate).to_contain("screencapture")
expect(gate).to_contain("CAPTURE_STATUS")
# Native-res re-render: both modes captured + validated.
expect(gate).to_contain("scale_mode=fit")
expect(gate).to_contain("scale_mode=no-resize")
expect(gate).to_contain("fullscreen_fit.png")
expect(gate).to_contain("fullscreen_noresize.png")
expect(gate).to_contain("fit-aspect-not-preserved")
expect(gate).to_contain("no-resize-content-not-original")
expect(gate).to_contain("wm_fullscreen_metal_fit_content")
expect(gate).to_contain("wm_fullscreen_metal_noresize_content")
# Fullscreen-fit magnified text must use the vector/hi-res text path.
expect(gate).to_contain("text_render=vector")
expect(gate).to_contain("wm_fullscreen_metal_text_render")
expect(gate).to_contain("fit-text-not-hires-vector")
# No-resize background must fill the whole native buffer (corner readback).
expect(gate).to_contain("noresize_bg_corners=ok")
expect(gate).to_contain("wm_fullscreen_metal_noresize_bg")
expect(gate).to_contain("no-resize-bg-corners-not-filled")
# Physical (Retina) surface + frontmost enforcement + capture-side checks.
expect(gate).to_contain("surface=physical")
expect(gate).to_contain("surface-not-physical")
expect(gate).to_contain("demo-window-not-frontmost")
expect(gate).to_contain("wm_fullscreen_metal_frontmost")
expect(gate).to_contain("wm_fullscreen_metal_physical")
expect(gate).to_contain("fit-capture-not-demo-blue")
expect(gate).to_contain("no-resize-capture-corners-not-navy")
# Web-engine phase: fullscreen pixels rendered by the HTML/CSS layout
# engine on the Metal fast path, captured + pixel-validated as a hard gate.
expect(gate).to_contain("web_engine=presented")
expect(gate).to_contain("fullscreen_webengine.png")
expect(gate).to_contain("wm_fullscreen_metal_webengine_marker")
expect(gate).to_contain("wm_fullscreen_metal_webengine_dims")
expect(gate).to_contain("web-engine-phase-not-proven")
expect(gate).to_contain("web-engine-capture-not-accent-blue")
expect(gate).to_contain("web-engine-capture-corners-not-navy")
```

</details>

#### ships the demo app that toggles real fullscreen via winit readback

- ships the demo app that toggles real fullscreen via winit readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ships the demo app that toggles real fullscreen via winit readback")
val app = file_read(APP)
expect(app).to_contain("winit_window_set_fullscreen")
expect(app).to_contain("winit_window_is_fullscreen")
expect(app).to_contain("winit_window_get_size")
expect(app).to_contain("[wm-fullscreen] mode=windowed")
expect(app).to_contain("[wm-fullscreen] mode=fullscreen")
expect(app).to_contain("[wm-fullscreen] restored=true")
# State growth is verified from real API readback, not assumed.
expect(app).to_contain("fullscreen-size-did-not-grow")
# Native-resolution re-render in two selectable modes.
expect(app).to_contain("SIMPLE_WM_FS_SCALE_MODE")
expect(app).to_contain("scale_mode=")
expect(app).to_contain("no-resize")
# A second native-res Metal backend is created at the real fullscreen dims.
expect(app).to_contain("metal-native-init-failed")
# Fullscreen-fit uses the antialiased high-resolution GPU text path.
expect(app).to_contain("draw_text_hires")
expect(app).to_contain("text_render=vector")
# No-resize bg fill proven by a native-framebuffer corner readback.
expect(app).to_contain("_bg_corners")
expect(app).to_contain("check_bg_corners")
# Physical (Retina) native render + present-dims + scale-factor evidence.
expect(app).to_contain("surface=physical")
expect(app).to_contain("winit_window_scale_factor")
expect(app).to_contain("_present=")
# Web-engine fullscreen phase: WM desktop expressed as HTML/CSS and
# rasterized through the fast Engine2D Metal web lane, presented in-window.
expect(app).to_contain("simple_web_layout_render_html_pixels_engine2d")
expect(app).to_contain("engine2d_fast_metal_available")
expect(app).to_contain("wm_web_scene_html")
expect(app).to_contain("[wm-fullscreen] web_engine=render")
expect(app).to_contain("[wm-fullscreen] web_engine=presented")
```

</details>

#### exposes the winit fullscreen set/get wrappers in the Simple windowing layer

- exposes the winit fullscreen set/get wrappers in the Simple windowing layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes the winit fullscreen set/get wrappers in the Simple windowing layer")
val wrap = file_read(WRAP)
expect(wrap).to_contain("fn winit_window_set_fullscreen")
expect(wrap).to_contain("fn winit_window_is_fullscreen")
expect(wrap).to_contain("fn winit_window_get_size")
expect(wrap).to_contain("rt_winit_window_set_fullscreen")
```

</details>

#### validates evidence report fields when a macOS run has produced them

- validates evidence report fields when a macOS run has produced them


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates evidence report fields when a macOS run has produced them")
val report = file_read(REPORT)
if report.contains("wm_fullscreen_metal_status"):
    # A real run wrote the report; enforce the full contract.
    if report.contains("wm_fullscreen_metal_status=pass"):
        expect(report).to_contain("wm_fullscreen_metal_status=pass")
        expect(report).to_contain("wm_fullscreen_metal_windowed_size=")
        expect(report).to_contain("wm_fullscreen_metal_fullscreen_size=")
        expect(report).to_contain("wm_fullscreen_metal_restored=true")
        expect(report).to_contain("wm_fullscreen_metal_gpu_frame_complete_count=")
        # Native-res re-render report keys.
        expect(report).to_contain("wm_fullscreen_metal_fit_content=")
        expect(report).to_contain("wm_fullscreen_metal_noresize_content=320x200")
        expect(report).to_contain("wm_fullscreen_metal_fit_capture_path=")
        expect(report).to_contain("wm_fullscreen_metal_noresize_capture_path=")
        # Fullscreen-fit magnified text rendered via the vector/hi-res path.
        expect(report).to_contain("wm_fullscreen_metal_text_render=vector")
        # No-resize background filled the whole native buffer.
        expect(report).to_contain("wm_fullscreen_metal_noresize_bg=ok")
        # Physical Retina surface + frontmost demo window proven on screen.
        expect(report).to_contain("wm_fullscreen_metal_surface=physical")
        expect(report).to_contain("wm_fullscreen_metal_frontmost=true")
        expect(report).to_contain("wm_fullscreen_metal_physical=")
        # Web-engine phase proven: HTML/CSS-rendered fullscreen window.
        expect(report).to_contain("wm_fullscreen_metal_webengine_marker=present")
        expect(report).to_contain("wm_fullscreen_metal_webengine_capture_path=")
    else:
        # Non-pass runs (fail/skip) must still carry a status + reason.
        expect(report).to_contain("wm_fullscreen_metal_status=")
        expect(report).to_contain("wm_fullscreen_metal_reason=")
else:
    # No macOS run yet on this host — nothing to validate here.
    expect(true).to_be_true()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afd6879f0379fb0f6ab03e8c5029bbe8b2cb2f82fbd4a70c2ab386fe26291408`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afd6879f0379fb0f6ab03e8c5029bbe8b2cb2f82fbd4a70c2ab386fe26291408`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afd6879f0379fb0f6ab03e8c5029bbe8b2cb2f82fbd4a70c2ab386fe26291408`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/check/macos_wm_fullscreen_metal_evidence_spec.spl
mirror: doc/06_spec/03_system/check/macos_wm_fullscreen_metal_evidence_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/macos_wm_fullscreen_metal_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/macos_wm_fullscreen_metal_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/macos_wm_fullscreen_metal_evidence_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the demo app that toggles real fullscreen via winit readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_wm_fullscreen_metal_evidence_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the winit fullscreen set/get wrappers in the Simple windowing layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
