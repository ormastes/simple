# SimpleOS bare Engine2D current-state refresh — 2026-08-12

Status: focused correctness PASS; performance and booted 8K/80 remain open.

## Current evidence

The canonical production bare fill matrix was rerun from the current shared
worktree and exited 0:

- x86-64 SSE2, host-user: exact pixels PASS;
- AArch64 NEON, QEMU-user: exact pixels PASS;
- RV64GCV/RVV VLEN=128, QEMU-user: exact pixels PASS;
- sentinels, scalar parity, enabled/hit/chunk/tail receipts: PASS.

The focused `backend_baremetal_image_clip_spec.spl` also exited 0 with three
examples covering negative/edge clipping, clip+mask+alpha parity, bounded
examined-pixel counts, bulk unmasked blending, and exact dirty rectangles.

The current bare backend already intersects image bounds once, delegates
unmasked rectangles to `framebuffer_blit_argb`, avoids the emulation layer's
full-frame readback for image blending, and records source versus examined
pixel counts. No overlapping source edits were made in this refresh.

## Honest result

This closes the current exact-fill matrix and focused image clipping checks.
It does not measure per-operation p50/p95, boot a SimpleOS desktop, prove
physical scanout, or allocate/render a 7680x4320 framebuffer. Fill/copy/blend
timing under bare QEMU and the booted WM checksum/RSS/fallback receipt remain
required before any bare 8K/80 claim.
