# SimpleOS ARM64/RV64 QMP input transport evidence gap

**Status:** PARTIAL — ARM64/RV64 source implemented; live proof remains open
**Scope:** `arm64-desktop-engine2d` and `riscv64-display-smoke` on QEMU `virt`
**Observed:** 2026-07-24

## Symptom

Historically the canonical ARM64 desktop accepted only PL011 characters. The
ARM64 source now attaches QEMU MMIO keyboard/pointer devices, discovers device
ID 18 by capability, owns eventq 0, drains/recycles exact eight-byte records,
and routes them through the shared evdev translators. This is preflight source,
not proof that QMP `input-send-event` reaches a current-source guest. PL011
remains fallback-only and is not keyboard press/release or pointer evidence.

The canonical RV64 desktop now uses QEMU's modern-only PCI VirtIO keyboard
and mouse devices (the device ignores requested legacy enablement and retains
PCI ID `1af4:1052`). Its freestanding owner discovers both by evdev
capability, owns eventq 0, acknowledges the PCI ISR, refills every consumed
descriptor, and injects raw records into the same shared compositor backend as
ARM64. This remains source evidence until a current RV64 ELF proves delivery.

The ARM entry reports `event_backend=virtio-mmio` ready only when both device
classes initialize; otherwise it reports a blocker and labels UART as fallback.
Because the guest polls eventq, evidence uses `[wm-pointer-poll] source=poll`,
never a false IRQ marker. One pointer `SYN_REPORT` transaction owns one sequence
across its REL/button records; key press and release each own state/frame
correlation even when release does not mutate WM state.
RV64 emits an unavailable marker only when both input device classes do not
initialize.

## Historical root cause and current boundary

The repository has only the platform-independent evdev translation owner:

- `src/os/drivers/virtio/virtio_input_ops.spl` converts VirtIO input fields to
  the existing `KeyEvent` and `MouseEvent` models.

The original production path was missing all hardware-facing ownership.
ARM64 now closes its source portion through `boot/baremetal_stubs.c` and
`os.kernel.arch.arm64.virtio_input`; RV64 closes its separate legacy-PCI
transport through `riscv64/boot/freestanding_runtime.c` and
`os.kernel.arch.riscv64.virtio_input`. Both inject the same raw-event poller
into the existing compositor backend. The following items remain unproved:

- ARM64 has no retained live run proving the new queue owner and receipts.
- RV64 has no retained current-ELF run proving PCI queue/ISR/refill and
  receipt delivery.
- ARM64 QMP key edges/pointer frames and later RAMFB revisions have not been
  correlated in production evidence.

PS/2 is x86 port-I/O and is not an ARM64 solution. The current USB xHCI code is
a probe lane, not a HID event transport.

## Required canonical implementation status

1. Both source owners are implemented in their architecture freestanding
   runtimes plus thin Simple facades; the evdev/backend owner is shared.
2. ARM64 implemented: discover QEMU `virt` MMIO slots at `0x0a000000`, stride `0x200`, and
   select device ID 18. Identify keyboard and relative-pointer capabilities
   through the VirtIO input configuration space; do not depend on slot order.
3. ARM64 implemented/preflight-only: negotiate modern VirtIO, reject stale
   QueueReady, validate identity-mapped DMA layout, provision eventq 0 with
   DMA acquire/release ordering and
   non-overlapping storage, pre-post writable eight-byte
   `{type:u16, code:u16, value:u32}` buffers, and recycle every used buffer.
4. ARM64 implemented: reuse `virtio_input_key_event` and `VirtioMouseAccum`; do not create new
   key, mouse, or WM action models.
5. Implemented: expose one `InputBackend` implementation returning real
   `KeyEvent.Press`, `KeyEvent.Release`, and flushed `MouseEvent` values.
6. Implemented by topology: ARM64 uses MMIO devices; RV64 traverses modern PCI
   common/notify/ISR/device capabilities for `virtio-keyboard-pci` and
   `virtio-mouse-pci`.
7. Source implemented/live open: route events through existing
   compositor/shell input owners. Assign a
   guest monotonic `input_seq` only after a used-ring event is consumed.
8. Source implemented/live open: emit distinct device, WM-state, and post-render frame receipts carrying the
   same sequence. Never copy a host nonce into guest evidence.

## Acceptance and capture prerequisites

- Canonical no-build live gate:
  `sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs`.
  It consumes the current `build/os/simpleos_arm64_desktop_engine2d.elf` and
  `build/os/fat32-arm64-desktop.img`; no path override is admitted. It requires
  the canonical build manifest to bind both artifact hashes and the guest
  source revision to current `HEAD`, then re-hashes both at launch and after
  capture. It injects the ordered QMP events and correlates guest-owned
  sequences through WM frames. Admission additionally requires one successful
  guest RAMFB visual-commit receipt for the baseline and every input, carrying
  address, authoritative rendered revision, monotonic presentation frame ID,
  checksum, bounded checksum duration, and an explicitly conservative
  full-frame damage bound. The checker injects only one logical
  edge at a time and waits for its poll/frame/commit chain before sending the
  next edge, so queued pointer/key batching cannot be misattributed. The
  canonical ARM64 desktop emits the receipt only after its Engine2D frame
  presenter returns, using a checksum read from the actual RAMFB scanout; live
  admission remains red until a host QEMU run proves the complete correlation.
- Canonical attested build:
  `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`.
  The wrapper invokes exactly
  `bin/simple os build --scenario=arm64-desktop-engine2d` with pinned LLVM,
  log, and timeout settings. Before and after the build it requires a clean
  guest-source worktree, unchanged `HEAD`, unchanged compiler identity, and
  the same deterministic content fingerprint/count across every source root
  consumed by the scenario (`build/os/generated`, `src/os`, `src/lib`, and
  `examples/09_embedded/simple_os`). Only then does it atomically publish the
  canonical ELF/disk manifest. The live gate recomputes the same source
  snapshot before launch and after capture.
- RV64 build:
  `bin/simple os build --scenario=riscv64-display-smoke`
- QEMU must expose a QMP Unix socket and attach the target's two production
  VirtIO input devices: MMIO for ARM64, modern PCI for RV64.
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
- The full `rt_arm_virtio_blk_*` runtime family is implemented in the ARM32
  and ARM64 `boot/baremetal_stubs.c` runtimes, but not RV64.
- RV64's freestanding runtime owns a separate private PCI VirtIO-BLK probe,
  but it does not expose the full `VirtioBlkDriver` extern surface: MMIO
  u32/u64 read and u32 write; MMIO, queue, and DMA bases; queue configure,
  reset, available push, and used index; prepare-read, completion wait,
  status, direct sector read, and sector-byte return.

Adding only the VFS imports would therefore trade an honest unavailable marker
for an unresolved boot closure. The font marker must remain until the existing
VirtIO-FAT32 and shared font bootstrap owners are reachable on RV64.

The RV64 framebuffer ABI now exposes its existing backing address, pitch, bpp,
and checked present path. It is suitable for stronger independent capture once
its receipt gains format and generation. `freestanding_runtime.c` allocates
`g_rt_gpu_fb` as contiguous identity-mapped guest RAM, attaches it to the
VirtIO-GPU resource as `B8G8R8A8_UNORM`, and presents with
TRANSFER_TO_HOST_2D plus RESOURCE_FLUSH. QMP `pmemsave` can therefore read the
guest-owned backing bytes directly. The current wrapper instead uses
`screendump`, so its crop remains diagnostic.

## Bounded implementation sequence

1. Extend the now-connected RV64 display facade with exact pixel format and a
   scanout generation owned by resource creation/recreation; keep present in
   the same GPU owner.
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
6. Build a current ELF and prove the implemented target-specific input owner
   routes decoded events through the shared compositor/shell owners.
7. Capture baseline and post-input buffers with `pmemsave`. Admit PASS only
   after guest IRQ, WM-state, later frame generation, and distinct pixels all
   correlate; serial-only or host-nonce-only evidence remains invalid.
