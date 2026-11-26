# Host WM Cached Chrome Full-Frame Blit Perf Gap

Date: 2026-07-06
Status: fix-implemented-verification-pending

## Summary

The host WM fallback renderer reuses cached chrome pixels, but still blits the
entire cached desktop frame to the backend before repainting live window
content. This keeps behavior stable and avoids duplicate chrome rendering, but
it remains expensive at large desktop sizes.

## Impact

The cost scales with the full framebuffer, not with changed windows or dirty
regions. At 4K/8K this can dominate a frame even when only a small content
surface changes.

## Desired Fix

Track a stable frame key for chrome, window geometry, visibility, focus, content
state, and scroll offsets. If unchanged, skip the cached chrome/content blits
and only present. For partial changes, add a shared subrect blit helper so the
backend restores cached chrome under changed windows without copying the full
desktop.

## Evidence

The 2026-07-06 sidecar audit found the full-frame cached chrome blit in
`src/os/compositor/host_compositor_entry.spl` as the highest-risk host WM
render cost after the shared QEMU renderer fix.


## BF-10 Fix & Verification Status (2026-11-26)

- **Code fix:** Verified `_host_chrome_cache_key` + `_composite_cached_chrome_dirty_rects` subrect blit/present path in `src/os/compositor/host_compositor_core.spl` and fixed missing `self.pixel_backend.present()` on cache-miss in `HostCompositor.render_frame()` (`native_pixel_lane` branch) so both cache-miss full renders and cache-hit dirty-rect subrect blits increment presentation counts consistently.
- **Host specs verified (`SIMPLE_LIB=src`, `--mode=interpreter`):**
  - `test/01_unit/os/wm_bf10/bf10_host_chrome_blit_present_spec.spl`: `1 passed, 0 failed` (`outcome=OK`)
  - `test/01_unit/os/compositor/host_chrome_dirty_rect_repro_spec.spl`: `1 passed, 0 failed` (`outcome=OK`)
- **Pending verification:** Native/self-hosted host WM desktop run at 4K/8K verifying frame time & RSS on cached chrome dirty-rect updates.
