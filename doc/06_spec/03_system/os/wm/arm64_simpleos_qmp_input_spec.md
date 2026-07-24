# ARM64 SimpleOS QMP input

**Status:** FAIL — VirtIO-MMIO input transport is not wired.

The production `arm64-desktop-engine2d` lane must consume QMP keyboard
press/release and pointer move/button events through real guest hardware.
PL011 characters are not accepted as key-state or pointer evidence.

The executable contract is
`test/03_system/os/wm/arm64_simpleos_qmp_input_spec.spl`. It remains fail-fast
until device discovery, VirtIO eventq ownership, shared `KeyEvent`/`MouseEvent`
translation, guest-owned receipt sequences, WM-state correlation, and
post-input framebuffer correlation are implemented.

See
`doc/08_tracking/bug/simpleos_arm64_qmp_input_transport_missing_2026-07-24.md`
for the implementation boundary and capture prerequisites.
