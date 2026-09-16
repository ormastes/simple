# Bug: host-WM showcase wrappers have no headless presentation lane

**Date:** 2026-07-25  
**Status:** CONSTRAINT IDENTIFIED - Evidence collection blocked on shared hardware

## Problem
The host-WM showcase wrappers require `SIMPLE_GUI=1` and call `GuiRenderer.create("auto", ...)` to spawn real winit/Metal windows. Three files affected:
- `examples/06_io/ui/wm_widget_showcase_gui.spl:466-470`
- `wm_graphics_2d_showcase_gui.spl:465-469`
- `wm_web_standards_showcase_gui.spl:467-469`

Without `SIMPLE_GUI=1`, they fail closed with `error=no-gui-requested`.

## Consequence
- Host-WM matrix evidence cannot be collected offscreen
- On shared machines running concurrent window-evidence loops (single-window-capture invariant), the host-WM row becomes unrunnable without collision
- The offscreen `scripts/check/check-hosted-wm-capture-evidence.shs` can only drive a fixed synthetic 320x240 WM-chrome scene (via `src/os/compositor/hosted_wm_capture_evidence.spl`), with no knob to select real showcase content

## Fix Direction
Add a headless variant of the `wm_*` wrappers presenting via the same PPM-capture path as `hosted_wm_capture_evidence.spl` instead of `GuiRenderer.create`. Enables:
- Offscreen evidence collection
- Concurrent evidence-loop runs without window collision
- Full showcase content coverage in automated matrix checks
