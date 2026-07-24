# SimpleOS ARM64/RV64 QMP input transport is missing

**Status:** OPEN — production blocker
**Scope:** `arm64-desktop-engine2d` and `riscv64-display-smoke` on QEMU `virt`
**Observed:** 2026-07-24

## Symptom

The canonical ARM64 desktop accepts PL011 characters and maps them to a small
set of window-manager actions. QMP `input-send-event` keyboard and pointer
events cannot reach the guest. PL011 character receipt is not keyboard
press/release evidence and cannot provide pointer evidence.

The canonical RV64 desktop has the same boundary: its loop consumes only
`serial_read_byte()`. The RV64 evidence wrapper currently attaches PCI VirtIO
keyboard and mouse devices, but no guest owner discovers, negotiates, or drains
them. Attaching a device is not input evidence.

The entry therefore correctly reports
`[backend2d-event-blocker] ... event_backend=pl011-uart` and must not emit
`[wm-input-irq]` or `[wm-pointer-irq]` receipts for UART characters.
RV64 likewise correctly emits
`[rv64-input-evidence-unavailable] reason=virtio-input-transport-not-wired`.

## Root cause

The repository has only the platform-independent evdev translation owner:

- `src/os/drivers/virtio/virtio_input_ops.spl` converts VirtIO input fields to
  the existing `KeyEvent` and `MouseEvent` models.

The production path is missing all hardware-facing ownership:

- `get_arm64_desktop_engine2d_target()` attaches RAMFB and VirtIO block only;
  it does not attach QEMU VirtIO keyboard or pointer devices.
- No ARM64 driver discovers VirtIO MMIO device ID 18.
- No RV64 driver discovers VirtIO MMIO device ID 18 either; the existing RV64
  PCI VirtIO-GPU owner does not provide an input queue.
- No owner negotiates a VirtIO input device, provisions eventq 0 with writable
  eight-byte event buffers, drains its used ring, and requeues buffers.
- Neither entry has an `InputBackend` backed by that transport.
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
6. Attach MMIO `virtio-keyboard-device` and `virtio-mouse-device` to the
   canonical ARM64 and RV64 WM/desktop target definitions. Do not attach the
   current PCI variants to an MMIO-only guest driver.
7. Route events through the existing compositor/shell input owners. Assign a
   guest monotonic `input_seq` only after a used-ring event is consumed.
8. Emit distinct device, WM-state, and post-render frame receipts carrying the
   same sequence. Never copy a host nonce into guest evidence.

## Acceptance and capture prerequisites

- Build:
  `SIMPLE_BINARY=$PWD/bin/release/aarch64-apple-darwin/simple SIMPLE_LIB=src SIMPLE_OS_BUILD_TIMEOUT_MS=900000 $PWD/bin/release/aarch64-apple-darwin/simple os test --scenario=arm64-desktop-engine2d --log=off`
- RV64 build:
  `bin/simple os build --scenario=riscv64-display-smoke`
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
  The RV64 live gate is
  `scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input`;
  the older requested `check-rv64-simpleos-wm-font-input-evidence.shs` name
  does not exist.

## RV64 font and scanout admission review

The font blocker is also below the desktop entry, not in rendering. The x86
desktop reads `/SYS/FONTS/NOTOSANS`, validates it through
`Engine2D.load_font_bytes`, and registers the selected bytes with the shared
`FontRenderer`. The reusable owner
`simpleos_desktop_register_selected_fonts_from_vfs()` already performs the
shared registration and is used by ARM64.

RV64 cannot safely call that owner yet:

- `riscv64-display-smoke` attaches no FAT32 block image.
- `vfs_boot_init_virtio_fat32()` reaches the ARM-named
  `rt_arm_virtio_blk_set_mmio_base` boundary.
- No RV64 freestanding definition of that binding exists.

Adding only the VFS imports would therefore trade an honest unavailable marker
for an unresolved boot closure. The font marker must remain until the existing
VirtIO-FAT32 and shared font bootstrap owners are reachable on RV64.

The RV64 framebuffer is suitable for stronger independent capture once its
metadata boundary is completed. `freestanding_runtime.c` allocates
`g_rt_gpu_fb` as contiguous identity-mapped guest RAM, attaches it to the
VirtIO-GPU resource as `B8G8R8A8_UNORM`, and presents with
TRANSFER_TO_HOST_2D plus RESOURCE_FLUSH. QMP `pmemsave` can therefore read the
guest-owned backing bytes directly. The current wrapper instead uses
`screendump`, and the Simple facade declares address/pitch/bpp/present calls
whose RV64 freestanding definitions are absent.

## Bounded implementation sequence

1. Complete the RV64 display runtime facade: return the physical backing
   address, byte pitch, bpp, exact pixel format, and a scanout generation owned
   by resource creation/recreation; keep present in the same GPU owner.
2. After a successful present, emit one guest scanout marker carrying address,
   width, height, stride, format, scanout generation, and frame revision.
3. Change only the RV64 wrapper to parse and bounds-check that marker, issue
   QMP `pmemsave(address, stride * height)`, and convert BGRA memory bytes to
   RGB row-by-row. Pin a new RV64 `right56,bottom48` crop from a retained run;
   never copy the x86 crop or hash.
4. Generalize the ARM-named VirtIO-block runtime binding to one ARM/RISC-V
   owner, attach the existing staged RV64 FAT32 image, and verify its
   `/SYS/FONTS/NOTOSANS` length/hash before boot.
5. Call `vfs_boot_init_virtio_fat32()` and
   `simpleos_desktop_register_selected_fonts_from_vfs()` before first
   composition. Reuse Engine2D/Draw IR; add no renderer, atlas, or cache.
6. Implement the MMIO input owner above, attach MMIO keyboard/pointer devices,
   and route decoded events through the existing compositor/shell owners.
7. Capture baseline and post-input buffers with `pmemsave`. Admit PASS only
   after guest IRQ, WM-state, later frame generation, and distinct pixels all
   correlate; serial-only or host-nonce-only evidence remains invalid.
