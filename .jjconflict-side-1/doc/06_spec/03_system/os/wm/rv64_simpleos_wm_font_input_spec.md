# RV64 SimpleOS WM font and input evidence

Status: **BLOCKED — no live RV64 font or input PASS is claimed.**

This is the RV64 QEMU dev-board lane for
`examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`. It is
separate from both the x86_64 SimpleOS gate and the generic RV64 nonblank
display-smoke gate.

## Required production proof

1. Boot the current pure-Simple
   `build/os/simpleos_riscv64_display_smoke.elf`.
2. Load `/SYS/FONTS/NOTOSANS` with exactly 1,708,408 bytes and SHA-256
   `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
   The guest must emit this exact marker:
   `[rv64-font-evidence] guest_path=/SYS/FONTS/NOTOSANS asset_bytes=1708408 asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081 route=shared-wm-draw-ir component_id=taskbar-clock`.
   Any `rv64-font-evidence-unavailable` or
   `rv64-input-evidence-unavailable` marker rejects the run before PASS.
3. Render the taskbar clock through
   `SharedWmScene -> DrawIrComposition -> Engine2D`.
4. Inject a keyboard event and a pointer press/release through QMP
   `input-send-event` into RV64 VirtIO input devices.
5. Correlate each new guest input sequence across device IRQ, WM state, and a
   later framebuffer generation: keyboard sequence is above the pre-injection
   baseline and its frame generation is above the desktop-present revision;
   pointer sequence is later than keyboard and its frame generation is later
   than keyboard's. The later receipt-bound `pmemsave` must also differ from
   the baseline scanout; a serial-only generation is insufficient.
6. Parse and range-check the guest `scanout-present` address, dimensions,
   stride, bpp, format, and generation; capture that exact backing buffer with
   QMP `pmemsave`; convert BGRA8888 to RGB; then extract the RV64-only
   `right56,bottom48` crop (8,064 bytes). Require its exact pinned SHA-256,
   flip `crop[0]` in a copy, and prove the same oracle rejects the copy.

The crop hash must come from a fresh RV64 QMP capture. The x86_64 crop hash is
not admissible.

## Shared font primary flow

1. Load the pinned multilingual font manifest
2. Accept exact-face-bound simple-script shaping
3. Prepare one shared font batch for 2D and 3D
4. Emit the selected font composite program and plan compilation
5. Prove native submission and device readback

The same live scenario traces and rejects boundary failures with:

1. Trace the production font and event boundary
2. Submit the boundary output to its canonical consumer
3. Correlate visible pixels and input with one frame identity
4. Reject disconnected stale or replayed evidence

## Current blockers

- The RV64 framebuffer-address, pitch, bpp, generation, and present ABI is
  connected to the existing VirtIO-GPU state. The wrapper now parses and
  range-checks the receipt, issues QMP `pmemsave`, requires the exact capture
  byte count, and converts the guest BGRA8888 buffer to RGB. Admission remains
  blocked on a current live ELF, attached font media, and crop calibration.
- The canonical RV64 entry now fails closed unless the legacy-PCI VirtIO-BLK
  font medium mounts through `vfs_boot_init_riscv64_virtio_fat32()` and the
  shared `simpleos_desktop_register_selected_fonts_from_vfs()` accepts every
  pinned face. The RV64 adapter reuses `SharedFat32Driver`; it does not reuse
  ARM's `rt_arm_virtio_blk_*` MMIO ABI or create a font cache.
- The canonical scenario builder creates
  `build/os/fat32-riscv64-desktop.img`, and both the scenario and live wrapper
  attach its legacy `virtio-blk-pci` view. Before launch, the wrapper extracts
  `/SYS/FONTS/NOTOSANS` from that exact image and verifies its byte count and
  SHA-256. The live run must still prove the emitted exact font marker.
- The RV64 freestanding owner now discovers QEMU's modern-only
  `virtio-keyboard-pci` and `virtio-mouse-pci` devices by evdev capability,
  traverses their `1af4:1052` common/notify/ISR/device PCI capabilities,
  posts and refills eventq 0, acknowledges the PCI ISR, and exports raw events
  through `riscv64/virtio_input.spl`. The RV64 entry injects that poller into
  the shared `VirtioInputBackend`, dispatches through `Compositor.handle_input`,
  and emits IRQ -> WM state -> presented-generation receipts only for
  delivered events. QMP sends pointer down and up in separate synchronization
  frames and waits for the exact down receipt before release. A current live
  ELF must still prove this route.
- `RV64_WM_FONT_REGION_EXPECTED_SHA256` is intentionally empty until a genuine
  RV64 `pmemsave` crop is captured.
- No qualifying current-source RV64 ELF exists in the worktree, so QEMU was
  not launched during this static design pass.

## Commands

Parser and corruption calibration only:

```bash
sh scripts/check/check-rv64-display-smoke-qmp-evidence.shs --self-test-wm-font-input
```

Build the current source and deterministic font medium once, then collect the
live calibration result:

```bash
bin/simple os build --scenario=riscv64-display-smoke
RV64_DISPLAY_SMOKE_BUILD=0 \
  scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input
```

Pin only a fresh `pmemsave` crop reported by this wrapper, then rerun once with
`RV64_WM_FONT_REGION_EXPECTED_SHA256` set. PASS requires exact font identity,
the exact guest marker, absence of unavailable markers, the exact crop,
corrupt-copy rejection, and both keyboard and pointer correlation rows.
