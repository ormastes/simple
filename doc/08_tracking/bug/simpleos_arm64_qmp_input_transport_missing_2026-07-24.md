# SimpleOS ARM64 QMP input transport is missing

**Status:** OPEN — production blocker
**Scope:** `arm64-desktop-engine2d` on QEMU `virt`
**Observed:** 2026-07-24

## Symptom

The canonical ARM64 desktop accepts PL011 characters and maps them to a small
set of window-manager actions. QMP `input-send-event` keyboard and pointer
events cannot reach the guest. PL011 character receipt is not keyboard
press/release evidence and cannot provide pointer evidence.

The entry therefore correctly reports
`[backend2d-event-blocker] ... event_backend=pl011-uart` and must not emit
`[wm-input-irq]` or `[wm-pointer-irq]` receipts for UART characters.

## Root cause

The repository has only the platform-independent evdev translation owner:

- `src/os/drivers/virtio/virtio_input_ops.spl` converts VirtIO input fields to
  the existing `KeyEvent` and `MouseEvent` models.

The production path is missing all hardware-facing ownership:

- `get_arm64_desktop_engine2d_target()` attaches RAMFB and VirtIO block only;
  it does not attach QEMU VirtIO keyboard or pointer devices.
- No ARM64 driver discovers VirtIO MMIO device ID 18.
- No owner negotiates a VirtIO input device, provisions eventq 0 with writable
  eight-byte event buffers, drains its used ring, and requeues buffers.
- The ARM64 entry has no `InputBackend` backed by that transport.
- No guest-owned monotonic input sequence correlates device receipt, WM state
  mutation, and the later framebuffer revision.

PS/2 is x86 port-I/O and is not an ARM64 solution. The current USB xHCI code is
a probe lane, not a HID event transport.

## Required canonical implementation

1. Add `src/os/drivers/virtio/virtio_input_mmio.spl` as the sole ARM/RISC-V
   VirtIO-MMIO input transport owner.
2. Discover the QEMU `virt` MMIO slots at `0x0a000000`, stride `0x200`, and
   select device ID 18. Identify keyboard and relative-pointer capabilities
   through the VirtIO input configuration space; do not depend on slot order.
3. Negotiate modern VirtIO correctly, provision eventq 0 with DMA-safe,
   non-overlapping storage, pre-post writable eight-byte
   `{type:u16, code:u16, value:u32}` buffers, and recycle every used buffer.
4. Reuse `virtio_input_key_event` and `VirtioMouseAccum`; do not create new
   key, mouse, or WM action models.
5. Expose one `InputBackend` implementation returning real `KeyEvent.Press`,
   `KeyEvent.Release`, and flushed `MouseEvent` values.
6. Attach `virtio-keyboard-device` and `virtio-mouse-device` to both canonical
   ARM64 WM/desktop target definitions.
7. Route events through the existing compositor/shell input owners. Assign a
   guest monotonic `input_seq` only after a used-ring event is consumed.
8. Emit distinct device, WM-state, and post-render frame receipts carrying the
   same sequence. Never copy a host nonce into guest evidence.

## Acceptance and capture prerequisites

- Build:
  `SIMPLE_BINARY=$PWD/bin/release/aarch64-apple-darwin/simple SIMPLE_LIB=src SIMPLE_OS_BUILD_TIMEOUT_MS=900000 $PWD/bin/release/aarch64-apple-darwin/simple os test --scenario=arm64-desktop-engine2d --log=off`
- QEMU must expose a QMP Unix socket and attach the two VirtIO-MMIO input
  devices to the production ELF.
- Inject one key down/up pair and a pointer move plus left-button down/up using
  QMP `input-send-event`.
- Require separate guest device receipts for both key edges and both button
  edges, a pointer-motion receipt, matching WM-state receipts, and a later
  framebuffer revision for handled events.
- Capture baseline and post-input RAMFB images through QMP `screendump` or
  guest-address-aware `pmemsave`; reject missing, stale, or identical
  action-expected captures.
- Keep the focused system contract red until all correlations above are real.
