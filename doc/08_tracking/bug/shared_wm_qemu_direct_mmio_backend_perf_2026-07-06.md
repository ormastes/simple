# Shared WM QEMU Direct-MMIO Backend Perf Gap

Date: 2026-07-06
Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Summary

The x86_64 SimpleOS WM QEMU entry now renders the real shared MDI scene and no
longer uses the host Simple Web renderer or synthetic rectangle scene in the
normal desktop path. The remaining hot path still renders the shared scene into
a temporary `SharedMdiFramebufferBackend.pixels` buffer and then copies every
pixel to BGA MMIO in `gui_entry_engine2d.spl`.

## Impact

This preserves correctness and the shared architecture, but it adds one full
frame allocation plus one full frame CPU copy before presentation. At
1024x768x32 this is acceptable for the current evidence gate, but it is the
wrong shape for higher-resolution or interactive SimpleOS WM rendering.

## Desired Fix

Add a baremetal `CompositorBackend` adapter in the x86_64 QEMU entry, or a
shared helper that renders any `CompositorBackend` directly, so
`render_shared_mdi_windows_to_backend(...)` can write fill/text/blit operations
straight to BGA MMIO. Keep the shared renderer source unchanged; only the
presentation backend should differ.

## Evidence

- `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` passed on
  2026-07-06 with `renderer=shared_mdi_framebuffer_scene`.
- Sidecar perf audit identified the temporary scene plus full MMIO copy as the
  largest remaining QEMU-specific render cost.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
