# ARM64 VirtIO-MMIO input preflight — 2026-07-24

## Scope

Repair the canonical `arm64-desktop-engine2d` input boundary without launching
QEMU.  This lane owns ARM64 `virt` MMIO discovery, queue memory, event
recycling, ARM target device attachment, and the desktop's route into the
existing shared input models.

## Implemented source route

1. `baremetal_stubs.c` scans `0x0a000000 + slot * 0x200` for device ID 18.
   It classifies devices through `VIRTIO_INPUT_CFG_EV_BITS`: keyboard requires
   `KEY_A`; pointer requires `REL_X`, `REL_Y`, and `BTN_LEFT`.  Slot order is
   never used as device identity.
2. Each discovered device waits boundedly for reset, accumulates status bits,
   rejects stale QueueReady, validates queue size/alignment/identity-mapped DMA
   windows, negotiates modern VirtIO (`VIRTIO_F_VERSION_1`), owns queue 0, and
   posts 32 writable eight-byte evdev records. Used-index/payload observation
   has DMA acquire ordering; descriptor recycling publishes the available
   index only after a DMA release barrier. Invalid IDs or non-exact lengths
   fail the device without clearing prior status bits.
3. `src/os/kernel/arch/arm64/virtio_input.spl` exposes only raw events.
   `gui_entry_desktop.spl` continues to translate through
   `virtio_input_key_event` and `VirtioMouseAccum`, then writes guest-owned
   device, pointer state, and post-render markers. Pointer REL/button records
   share one sequence until SYN; press and release each get key state/frame
   evidence.
4. Both ARM64 WM targets attach `virtio-keyboard-device` and
   `virtio-mouse-device`; UART is fallback-only when either required device is
   absent.

## Admission still required

The live system contract stays deliberately red.  After the host-first gate
is green, boot the canonical target with QMP and prove: key press/release,
pointer motion, left-button down/up, matching guest `input_seq` device/WM/frame
markers, and distinct baseline/post-input RAMFB captures.  Source wiring is
not a substitute for that evidence.

## Bounded preflight result

- PASS: `clang --target=aarch64-none-elf -ffreestanding -fsyntax-only
  examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`
- PASS: `git diff --check`
- PASS: `sh scripts/check/check-arm64-virtio-input-preflight.shs`
- BLOCKED before Simple entry compilation: the diagnostic ARM64 build invokes
  `scripts/os/make_os_disk.shs`, which fails because
  `bin/release/aarch64-unknown-simpleos/simple` is missing.  No QEMU launch or
  capture occurred.
