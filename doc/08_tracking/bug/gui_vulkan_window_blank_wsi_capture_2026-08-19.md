# check-gui-vulkan-window: Vulkan initializes (compute+graphics) but window capture is blank — blank_wsi

- **Date:** 2026-08-19
- **Status:** OPEN — re-confirmed 2026-11-11 (lane ne11); BLOCKED on this host, see addendum
- **Severity:** medium — presented-window evidence lane red; offscreen lanes unaffected
- **Host:** RTX A6000 + TITAN RTX, Vulkan 1.4, nvidia + lvp ICDs present

## Symptom
`sh scripts/check/check-gui-vulkan-window.shs` fails:

```
renderer_log_line=...status=Initialized;api=vulkan;gate=vulkan_runtime;shader=spirv;compute=true;graphics=true;present=false;reason=Vulkan initialized
window_capture_status=blank_wsi
assert_window_capture=blank_wsi
overall=fail
```

Device init is genuinely green (compute=true, graphics=true) but
`present=false` and the captured window is blank — the WSI/swapchain present
path never puts pixels on screen. Consistent with the offscreen results the
same day: `check-vulkan-8k-buffer-fill` PASSes but records
`vulkan_8k_swapchain_presented=false`, i.e. NO lane currently proves a real
present.

## Notes
- Not the E0252 vulkan-feature build bug (that blocks lanes which rebuild
  `simple-runtime --features vulkan`); this lane got a working Vulkan device
  and fails later, at present/capture.
- Suspects: headless/X capture path, swapchain creation on this host, or the
  capture reading before the first present.
- Evidence log: `build/gui-window-evidence/evidence.log` (worktree
  `/mnt/data/worktrees/render-harden`).

---

## 2026-11-11 addendum — lane ne11 (P3 traverse, batch ne11)

**Verdict: OPEN, BLOCKED on this host (Linux Xvfb evidence lane required).**

- `scripts/check/check-gui-vulkan-window.shs` is unchanged in shape and is
  Xvfb-only by design ("Launches the widget showcase as a REAL on-screen winit
  window under a PRIVATE Xvfb display ... There is deliberately NO escape hatch
  to a live $DISPLAY"). It cannot run on this Windows host, so the
  present/blank_wsi symptom is neither reproduced nor cleared here — "does not
  run on Windows" is not evidence of a fix.
- The script's own header still records the honest limitation that no lane
  proves a real present on the reference host (Vulkan raster offscreen ->
  winit blit; llvmpipe device under Xvfb).
- Grant: run `sh scripts/check/check-gui-vulkan-window.shs` on a Linux lane
  with Xvfb + a Vulkan ICD (lavapipe acceptable per script header) and attach
  `build/gui-window-evidence/evidence.log`.
