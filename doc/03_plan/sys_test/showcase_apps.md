# Showcase apps system-test plan

For every app/surface pair, launch through the catalog, locate the titled window, exercise at least one real event, capture semantic state, and verify a nonblank frame with provenance. The web app additionally types, clicks, navigates, and scrolls. The GUI app toggles, drags, minimizes/restores, and closes. The 2D app verifies labeled scene regions and readback.

SimpleOS scenarios require an installed app path, guest PID/window ownership, QEMU framebuffer evidence, and post-event pixel/state change. Missing QEMU or platform support is `skipped`; a designated ready runner that cannot launch is failure.

Negative cases reject unknown app IDs/surfaces, unavailable backends, blank or unchanged frames, missing events, placeholder renderer output, synthetic handles, and mismatched readback checksums.
