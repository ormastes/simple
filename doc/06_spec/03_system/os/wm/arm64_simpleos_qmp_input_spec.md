# ARM64 SimpleOS QMP input

**Status:** FAIL — source transport implemented; canonical compositor input
ownership and live QMP evidence remain blocked.

The production `arm64-desktop-engine2d` lane must consume QMP keyboard
press/release and pointer move/button events through real guest hardware.
PL011 characters are not accepted as key-state or pointer evidence.

The executable contract is
`test/03_system/os/wm/arm64_simpleos_qmp_input_spec.spl`. Its source-preflight
scenario verifies capability-based device discovery, modern eventq ownership,
DMA acquire/release ordering, strict used-length validation, shared
`KeyEvent`/`MouseEvent` translation, rejection of device `FAILED` and
`DEVICE_NEEDS_RESET` status, and QEMU MMIO device attachment.

The transport cannot yet be installed as the compositor's canonical
`InputBackend`: freestanding native lowering erases the trait method
`poll_mouse() -> MouseEvent?` to `ANY`, so the compositor cannot safely access
the returned event. Raw VirtIO polling remains diagnostic-only and emits
`[backend2d-event-blocker]`; it must not emit `[backend2d-event-ready]`.

The live scenario remains fail-fast until QMP proves both keyboard edges plus
pointer move/button down/button up. Pointer REL/button records within one
`SYN_REPORT` frame share one guest-owned sequence. Keyboard press and release
each require a device receipt, truthful poll receipt, state receipt, and later
frame receipt. `[wm-pointer-irq]` is forbidden because this path polls the used
ring; the truthful marker is `[wm-pointer-poll] source=poll`.

Traceability: `REQ-007` (canonical SimpleOS route). The installed generated
theme snapshot remains the `REQ-001` single authority; input transport does
not introduce a second theme or renderer path.

See
`doc/08_tracking/bug/simpleos_arm64_qmp_input_transport_missing_2026-07-24.md`
for the implementation boundary and capture prerequisites.
