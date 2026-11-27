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

## 2026-11-12 fix attempt — lane fix-runpath-gpu-20261112 (check-script hardening landed; present defect still OPEN)

In-scope change to `scripts/check/check-gui-vulkan-window.shs` (the only
lane-owned file for this record):

1. **Window-mapping wait before capture** (the record's "capture reading
   before the first present" suspect). Phase B previously started `xwd`
   ~2s after `OFFSCREEN_PPM` appeared, which the showcase writes BEFORE
   opening the winit window — so the capture could run before the window
   mapped and before its first present reached the Xvfb root pixmap. The
   script now polls `xwininfo -root -children` on the PRIVATE display (up
   to 30s, optional tool — without it the old timing is kept) and records
   `window_mapped_wait_secs` / `window_id`.
2. **Capture the mapped window by id** (`xwd -id`) with root-pixmap
   fallback, instead of only ever reading the root.
3. **Honest liveness + new status.** The loop records
   `app_alive_at_last_capture`, and a new `app_exited_no_window` status
   distinguishes "the app died before mapping any window, so the WSI
   present path never ran" from a mapped-but-blank surface (`blank_wsi`).

Verification done here (macOS host, no Xvfb — full lane still requires
Linux Xvfb + Vulkan ICD per the 2026-11-11 addendum):
- `sh -n` passes.
- End-to-end harness run with stubbed Xvfb/xwininfo/xwd/convert/timeout
  and a stub `simple` binary: mapped-window path classifies
  `window_capture_status=captured` with `window_id` set after
  `window_mapped_wait_secs=0`; no-window + app-exited path classifies
  `app_exited_no_window` with `app_alive_at_last_capture=0`. Gate logic
  (renderer/offscreen/oracle hard asserts, window capture soft) unchanged.

What this does NOT fix: `present=false` / blank WSI surface itself lives in
the runtime winit/Vulkan present path (`winit_present_rgba`, outside this
lane's touch scope), so the record stays OPEN, BLOCKED on a Linux Xvfb
evidence lane, with the capture-timing suspect now ruled out by
construction.

Status: fix-implemented-verification-pending (script); underlying
present-path defect OPEN.


---

## 2026-11-13 addendum — P3 gpu lane p3-gpu-20261113 (work/p3-gpu-20261113, base 6f4cb189867)

**Verdict: OPEN, BLOCKED on this host — unchanged.** `scripts/check/check-gui-vulkan-window.shs`
remains Xvfb-only by design with no `$DISPLAY` escape hatch, so it cannot run on
this Windows host; the blank_wsi symptom is neither reproduced nor cleared here
("does not run on Windows" is not evidence of a fix). Grant unchanged: run the
gate on a Linux lane with Xvfb + a Vulkan ICD and attach
`build/gui-window-evidence/evidence.log`.

## Triage 2026-11-13 (Linux aarch64, lane uia) — row stays OPEN

Blocked on this host: check-gui-vulkan-window.shs needs Xvfb and a gui-feature seed; this host has xwd but no Xvfb or xvfb-run, and the gate app examples/06_io/ui/widget_showcase_gui.spl is owned by another lane today. Source note: present=false in the renderer line is static metadata (BackendProbeResult.has_present is never set for Vulkan in backend_probe.spl), not a symptom.
