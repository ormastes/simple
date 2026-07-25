# Bug: GUI widget RenderDoc goal blockers remain

Status: resolved on Linux 2026-07-03
Date: 2026-06-23
Area: GUI widget RenderDoc evidence

## Symptom

The GUI widget RenderDoc goal remains incomplete when:

- `gui_widget_renderdoc_goal_status` is not `pass`
- `gui_widget_renderdoc_goal_blocked_gate_count` is nonzero
- `gui_widget_renderdoc_goal_blocked_gates` lists missing Simple or Electron
  widget RenderDoc proof

Widget fixture coverage alone is not enough. Completion requires live RenderDoc
proof for the generated widget HTML fixture.

## Required Evidence

Completion requires:

- `gui_widget_renderdoc_goal_widget_feature_covered_count` matching the emitted
  `gui_widget_renderdoc_goal_widget_count`
- `gui_widget_renderdoc_goal_missing_widget_features` empty after comparing
  against `gui_widget_renderdoc_goal_expected_widget_features`
- `gui_widget_renderdoc_goal_simple_gate_status=pass`
- `gui_widget_renderdoc_goal_electron_gate_status=pass`
- `gui_widget_renderdoc_goal_blocked_gate_count=0`
- Simple GUI widget `.rdc` evidence on Vulkan Engine2D with `RDOC` magic
- Electron Chromium-on-Vulkan widget `.rdc` evidence with nonblank ARGB proof

Use `scripts/check/check-gui-widget-renderdoc-goal-status.shs --strict` only on
hosts with real Simple Vulkan Engine2D and Electron Chromium/Vulkan `.rdc`
evidence.

## Current Linux Evidence

Resolved on 2026-07-03:

- `sh scripts/check/check-gui-widget-renderdoc-goal-status.shs` reports
  `gui_widget_renderdoc_goal_status=pass`,
  `gui_widget_renderdoc_goal_widget_feature_covered_count=43`,
  `gui_widget_renderdoc_goal_simple_gate_status=pass`,
  `gui_widget_renderdoc_goal_electron_gate_status=pass`, and
  `gui_widget_renderdoc_goal_blocked_gate_count=0`.
- Simple widget capture:
  `build/renderdoc/widget-probe-small/simple/simple_gui_app_capture.rdc` with
  `RDOC` magic.
- Electron Chromium widget capture:
  `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc`
  with `RDOC` magic.
- The Electron RenderDoc capture-specific ARGB file remains absent, but the gate
  is satisfied by the direct Electron Vulkan ARGB proof from
  `build/gui-web-2d-vulkan-env-run-current/evidence.env`.
- Evidence reports:
  `doc/09_report/gui_widget_renderdoc_goal_status_2026-07-03.md` and
  `doc/09_report/gui_renderdoc_feature_coverage_status_2026-07-03.md`.

Resolved on 2026-06-26:

- Simple GUI widget RenderDoc evidence now passes with `RDOC` magic using
  `src/app/test/renderdoc_vulkan_widget_capture.spl`.
- The capture renders
  `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html` through
  the Simple Web layout pipeline and presents the resulting frame on Vulkan
  Engine2D inside an in-application RenderDoc capture.
- Evidence:
  `build/renderdoc/widget-probe-small/simple/evidence.env`
- Capture:
  `build/renderdoc/widget-probe-small/simple/simple_gui_app_capture.rdc`
- Gate report:
  `doc/09_report/gui_widget_renderdoc_goal_status_2026-06-26.md`

Historical Electron blocker before the 2026-07-03 pass:

- Electron Chromium-on-Vulkan widget `.rdc` capture. The ARGB proof is now
  present, so the remaining widget gate is the missing RenderDoc capture file.
- 2026-06-26 Electron display-helper rerun uses the current Chromium Vulkan
  launch flags and records a nonblank 1280x720 ARGB proof with 405674 nonblank
  pixels, but still fails with `missing-rdc`; the Chromium GPU process exits
  `139` under RenderDoc and no `.rdc` is produced:
  `build/renderdoc/electron-display-helper/electron-html/evidence.env`.
- 2026-06-29 gate classification now preserves the same missing `.rdc` and
  nonblank ARGB evidence, but reports the actionable top-level reason
  `electron-widget-renderdoc-gpu-process-crashed-under-renderdoc` and Electron
  gate reason `chromium-gpu-process-crashed-under-renderdoc`. Evidence reports:
  `doc/09_report/gui_widget_renderdoc_goal_status_2026-06-29.md` and
  `doc/09_report/renderdoc_electron_html_gate_2026-06-29.md`.
- 2026-06-26 no-child-hook RenderDoc diagnostics now record
  `rdoc_renderdoc_hook_children=0`. They avoid the direct child-hook crash path
  but still do not produce a browser GPU-process `.rdc`, so they are diagnostic
  only:
  `build/renderdoc/electron-no-child-hook-renderdoc-display/electron-html/evidence.env`.
- 2026-06-26 visible Electron GPU-process autocapture diagnostics added
  `RDOC_ELECTRON_SHOW_WINDOW=1` / `ELECTRON_CAPTURE_SHOW_WINDOW=1`. Visible
  data-url runs reach load/settle/capture stages, but no valid widget/browser
  `.rdc` is produced; RenderDoc preload crashes the GPU process and lazy
  `dlopen` stalls:
  `build/renderdoc/electron-visible-dataurl-dlopen-dlsym-trigger/electron-html/gpu-launcher.log`.
- 2026-06-26 display-only and ANGLE scheduling-hook diagnostics still fail the
  Electron widget/browser `.rdc` gate. The shim can reach
  `rdoc_autocapture_api=ready`, but RenderDoc ends with `ok=0` and zero
  submit/present/swap counters; a tiny animated HTML page also fails to produce
  `.rdc` under the GPU launcher:
  `build/renderdoc/electron-display-only-small-trigger/electron-html/gpu-launcher.log`.
- The aggregate GUI RenderDoc status now reports
  `gui_renderdoc_feature_coverage_reason=missing-electron-widget-renderdoc`
  rather than `missing-simple-widget-renderdoc`.
- The shared generated HTML fixture now includes a tiny CSS/rAF/WebGL pulse so
  Chrome/Electron RenderDoc probes have continuous browser-side frame activity.
  This does not close the Electron gate; it only removes a static-page trigger
  ambiguity from future browser capture diagnostics.
- A focused Electron GPU-process diagnostic now reaches RenderDoc API readiness
  and Electron DOM audit/geometry, but still fails with no `.rdc` and no
  offscreen ARGB paint:
  `build/renderdoc/electron-gpu-autocapture-elf-trigger-offscreen-failfast/electron-html/evidence.env`.
