# Bug: host-WM showcase wrappers have no headless presentation lane
## Closed 2026-09-16 — ...b to select real showcase content ## Fix Direction Add a headless variant of the `wm_*` wr

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Date:** 2026-07-25  
**Status:** CONSTRAINT IDENTIFIED - Evidence collection blocked on shared hardware

> **Verification 2026-11-25 (release/1.0.0, `47d6c5eddd5`):** the fix
> direction has LANDED. All three wrappers now carry a headless
> presentation lane selected by `SIMPLE_WM_HEADLESS_CAPTURE=1`:
> `examples/06_io/ui/wm_widget_showcase_gui.spl` (line ~466 "Headless
> host-WM capture lane", `run_headless_capture`, PPM frame via
> `encode_ppm_p6`/`decode_ppm_to_argb`), `wm_graphics_2d_showcase_gui.spl`,
> and `wm_web_standards_showcase_gui.spl` (4-5 `SIMPLE_WM_HEADLESS_CAPTURE`
> references each at this base). Offscreen evidence collection without
> `GuiRenderer.create`/real windows is now possible, closing the gap this
> record describes. Verification here is by code inspection at the release
> base; a live capture run was not attempted on this host (Windows
> worktree, and the tracked `bin/simple.exe` predates the seed's
> `@representation_boundary` directive fix so it cannot load today's
> annotated std-lib modules). Closed — the "blocked on shared hardware"
> constraint no longer applies to the headless lane.

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

