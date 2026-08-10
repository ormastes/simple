# Showcase apps system-test plan

For every app/surface pair, launch through the catalog, locate the titled window, exercise at least one real event, capture semantic state, and verify a nonblank frame with provenance. The web app additionally types, clicks, navigates, and scrolls. The GUI app toggles, drags, minimizes/restores, and closes. The 2D app verifies labeled scene regions and readback.

SimpleOS scenarios require an installed app path, guest PID/window ownership, QEMU framebuffer evidence, and post-event pixel/state change. Missing QEMU or platform support is `skipped`; a designated ready runner that cannot launch is failure.

Negative cases reject unknown app IDs/surfaces, unavailable backends, blank or unchanged frames, missing events, placeholder renderer output, synthetic handles, and mismatched readback checksums.

## ARM64 QEMU graphics slice

Run the attested ARM64 desktop producer, then
`scripts/check/check-simpleos-arm64-qmp-input-evidence.shs`. One live run must
prove the canonical showcase identity and section anchors, exact guest/RAMFB
checksums, ordered pointer/button/key correlation, native NEON execution with
bit-exact parity, and at least 39 FPS over 4 warmup plus 64 guest-timed frames.
The current-main semantic port has not yet re-proven the FPS row; do not infer
it from desktop-ready or from the older integration-lane result.
