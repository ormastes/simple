# SimpleOS RV64 WM Live Framebuffer Gate Missing

- status: blocked-rv64-font-block-transport-input-transport-and-pmemsave
- gate: `scripts/check/check-simpleos-host-configuration-matrix.shs`
- failing field: `simpleos_host_configuration_qemu_riscv64_wm_live_status=missing`
- current source: `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`
- latest result: the canonical entry reaches the shared WM source path, but the
  current RV64 runtime/device boundary cannot produce admissible font/input
  evidence

## Current source audit (2026-07-24)

The remaining gap is below the shared WM renderer, not another renderer:

- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` now defines the
  framebuffer-address, pitch, bpp, and present calls declared by
  `src/os/kernel/arch/riscv64/display.spl`. Address and metadata fail closed
  until the existing VirtIO-GPU owner is ready, and present reuses its checked
  transfer/flush path. The focused source contract is
  `test/01_unit/os/riscv64_display_abi_contract_test.shs`.
- The entry now emits physical scanout address, dimensions, stride, bpp,
  `bgra8888` format, successful-present generation, and scene revision. The
  focused ABI contract pins the generation increment to a successful
  transfer/flush.
- `scripts/check/check-rv64-display-smoke-qmp-evidence.shs` uses QMP
  `screendump`. The WM/font admission lane must parse the new guest receipt,
  range-check it, and issue QMP `pmemsave`. Its current rightmost crop is
  diagnostic only and cannot be pinned.
- The pinned media builder already stages `/SYS/FONTS/NOTOSANS` with the
  required 1,708,408-byte/SHA-256 identity in `build/os/fat32-riscv64.img`,
  but the display scenario does not ensure or attach that image and the direct
  evidence wrapper attaches no block device. More importantly,
  `vfs_boot_init_virtio_fat32()` reaches the ARM-only
  `rt_arm_virtio_blk_*` ABI, whose production definitions live in the ARM32
  and ARM64 `boot/baremetal_stubs.c` runtimes.
  RV64 instead has a private PCI block probe in `freestanding_runtime.c` with
  no architecture-neutral `BlockDevice`/FAT32 sector-byte interface. Merely
  adding QEMU media or VFS imports would leave an unresolved boot closure.
  The missing owner is one shared or RV64 adapter implementing the complete
  `driver_class.spl` extern surface: MMIO u32/u64 reads and u32 writes; MMIO,
  queue, and DMA bases; queue configuration, reset, available-ring push, and
  used index; prepare-read, completion wait, status, direct sector read, and
  sector-byte return. Only then may the entry
  call the shared VFS/font bootstrap. A successful registry return, not an
  unconditional serial string, must guard any `[rv64-font-evidence]` receipt.
- `src/os/drivers/virtio/virtio_input_ops.spl` is a pure evdev decoder with
  unit coverage and an ARM64 compositor caller, but no RV64 production caller. There is no RV64 VirtIO input
  discovery, event-virtqueue setup/refill, interrupt acknowledgement, or
  compositor input backend. Adding QEMU `virtio-keyboard-pci` and
  `virtio-mouse-pci` devices does not create that guest transport.

The minimum closure order is: generalize or implement the architecture-owned
VirtIO-BLK sector-byte adapter; provision the existing RV64 FAT32 image and
call the shared VFS/font bootstrap; add the display generation/format receipt;
add one RV64 VirtIO input transport which feeds the existing decoder and
compositor; then switch the wrapper to guest-addressed `pmemsave` and capture a
fresh RV64-only crop. x86_64 addresses, crops, and hashes are not admissible
substitutes.

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
