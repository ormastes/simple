# Host WM Cached Chrome Full-Frame Blit Perf Gap

Date: 2026-07-06
Status: open

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
