# Bug: host-WM showcase wrappers have no headless presentation lane

**Date:** 2026-07-25  
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
