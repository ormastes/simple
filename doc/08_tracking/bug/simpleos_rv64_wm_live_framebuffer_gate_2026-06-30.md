# SimpleOS RV64 WM Live Framebuffer Gate Missing

- status: blocked-rv64-display-abi-font-media-input-transport-and-pmemsave
- gate: `scripts/check/check-simpleos-host-configuration-matrix.shs`
- failing field: `simpleos_host_configuration_qemu_riscv64_wm_live_status=missing`
- current source: `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`
- latest result: the canonical entry reaches the shared WM source path, but the
  current RV64 runtime/device boundary cannot produce admissible font/input
  evidence

## Current source audit (2026-07-24)

The remaining gap is below the shared WM renderer, not another renderer:

- `src/os/kernel/arch/riscv64/display.spl` declares
  `rt_display_framebuffer_address`, `rt_display_pitch`, `rt_display_bpp`, and
  `rt_display_present`, but
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` currently defines
  only display initialization, the test fill/flush probe, width, and height.
  A current-source production ELF therefore has no complete display ABI to
  link against.
- The entry reports only width, height, and stride. It does not emit the
  physical scanout address, byte format, or scanout generation required to
  bind host capture to the guest-owned backing buffer.
- `scripts/check/check-rv64-display-smoke-qmp-evidence.shs` uses QMP
  `screendump`. The WM/font admission lane must instead parse guest-emitted
  address/stride/format/generation, range-check them, and issue QMP
  `pmemsave`. Its current rightmost crop is diagnostic only and cannot be
  pinned.
- The shared font VFS bootstrap already exists, but the RV64 display entry
  does not call it and the direct evidence wrapper attaches no FAT32 block
  device. A successful registry return, not an unconditional serial string,
  must guard any `[rv64-font-evidence]` receipt.
- `src/os/drivers/virtio/virtio_input_ops.spl` is a pure evdev decoder with
  unit coverage and no production caller. There is no RV64 VirtIO input
  discovery, event-virtqueue setup/refill, interrupt acknowledgement, or
  compositor input backend. Adding QEMU `virtio-keyboard-pci` and
  `virtio-mouse-pci` devices does not create that guest transport.

The minimum closure order is: complete the architecture-owned display ABI and
generation counter; provision the existing RV64 FAT32 image and call the
shared VFS/font bootstrap; add one RV64 VirtIO input transport which feeds the
existing decoder and compositor; then switch the wrapper to guest-addressed
`pmemsave` and capture a fresh RV64-only crop. x86_64 addresses, crops, and
hashes are not admissible substitutes.

The smaller `riscv64-display-smoke` scenario now routes the renamed production
entry through `src/os` and `src/lib`. Its architecture facade discovers the
VirtIO mode dynamically, `FramebufferDriver` exposes that scanout to the
canonical compositor, and `DesktopShell` renders through
`Engine2dWmFrameExecutor` before the sole checked transfer/flush present.
Optional host execution reuses the existing ivshmem mapper and RV64 protocol
identity; it does not create a private renderer.

Evidence contract v2 rejects the old fixed-resolution/anchor report. A passing
fresh report must correlate one positive scene revision across ordered render,
present, and ready markers, validate PPM dimensions/stride/completeness, and
observe at least four canonical desktop palette roles. TODO 567 remains open
for replacing the facade's transitional C DMA/queue transport with pure Simple.
TODO 548 remains the live-build blocker, so source and parser work do not close
this bug or claim QEMU/physical-board PASS.

Historical scanout-probe evidence:
- `riscv64-display-smoke` boots the display probe.
- QMP capture proves a nonblank framebuffer:
  `rv64_display_smoke_qmp_nonblack=76800`.
- Capture validates the five C-owned probe anchors:
  `rv64_display_smoke_qmp_wm_anchor_matches=5`.

Production WM acceptance remains open:
- Simple owns an authoritative `SharedWmScene` and content frames.
- `FramebufferDriver` and `Engine2dWmFrameExecutor` render the live scene.
- An architecture display owner discovers the VirtIO scanout mode and
  presents the resulting frame without leaf-level direct `rt_*` calls.
- QMP evidence correlates the rendered scene and host-GPU receipt rather than
  accepting unconditional markers or fixed probe pixels.
