# QRB2210 DRM/KMS kernel owner

Status: BLOCKED — the repository has the fail-closed
`Qrb2210DrmKmsDisplayProvider` adapter, but it does not contain the physical
QRB2210 display-controller kernel owner that the adapter requires. Do not
promote display readiness or construct receipts until this owner runs on an
attached UNO Q under SimpleOS.

## Audit result

The current lower layers provide useful generic mechanisms, but not enough
information or control to implement a real QRB2210 atomic display pipeline:

- `os.kernel.boot.mmio` provides volatile MMIO reads and writes. There is no
  QRB2210 MDSS/DPU/DSI/DP register map, clock/reset/power-domain controller,
  or display-controller probe in `src/os`.
- `os.kernel.memory.memory_dma_pages` and the kernel DMA allocation contract
  provide generic pages/addresses. There is no QRB2210 SMMU/IOMMU domain,
  display DMA mapping, GEM/framebuffer object owner, or cache-maintenance
  contract for scanout buffers.
- `os.kernel.arch.arm64.interrupt` is a QEMU-virt GICv2 implementation with
  fixed `0x08000000`/`0x08010000` bases. It cannot identify or service the
  QRB2210 display IRQ topology. `os.kernel.arch.common.gic_common` only
  supplies register-layout helpers; it is not a board GICv3/ITS owner.
- `os.kernel.boot.dtb_parser` classifies QEMU/RISC-V UART, PLIC, CLINT, RAM,
  and CPU nodes. It does not expose generic `compatible`, `reg`, `interrupts`,
  `clocks`, `resets`, `power-domains`, `iommus`, graph endpoints, reserved
  memory, or simple-framebuffer/display nodes needed by QRB2210.
- `os.kernel.ipc.syscall_device` and `os.userlib.device` broker PCI-style
  BAR/IRQ/DMA grants. QRB2210 display hardware is platform/DT described; no
  platform-device grant or `/dev/dri/card0` character-device/ioctl owner exists.
- `os.drivers.framebuffer.fb_driver` consumes an already-established linear
  framebuffer. `os.drivers.dma.display_dma` is capability/dirty-rectangle
  policy. Neither performs modesetting, atomic plane commits, vblank/page-flip
  completion, or physical scanout capture.

Therefore generic MMIO calls alone are not an authorization to write guessed
Qualcomm registers. A real implementation also requires the board's exact
firmware/DT description and public register/command contracts for the shipped
QRB2210 display path.

## Required kernel APIs and drivers

1. **Board discovery:** a bounded generic FDT walker plus typed platform-device
   resources for MMIO ranges, interrupt specifiers, clocks, resets,
   power-domains, IOMMU streams, reserved memory, and display graph endpoints.
2. **QRB2210 interrupt owner:** board-discovered GICv3 redistributor/system
   register support and registered display/vblank/error handlers with mask,
   acknowledge, and EOI ordering.
3. **Power and interconnect owners:** Qualcomm clock/reset/power-domain and
   bandwidth/interconnect votes required before display MMIO is accessed.
4. **Display hardware owner:** the exact QRB2210 MDSS/DPU plus the attached
   encoder/bridge/panel path; probe must validate compatible/revision and fail
   closed for unknown hardware.
5. **Memory owner:** DMA-coherent scanout allocation, QRB2210 SMMU mapping,
   format/modifier/pitch validation, framebuffer lifetime, and explicit cache
   synchronization. No physical address may be accepted from an untrusted app.
6. **KMS object owner:** connector/encoder/CRTC/plane/mode enumeration and
   stable generation-scoped handles. The owner, not the adapter, mints these
   handles and `/dev/dri/card0` identity.
7. **Atomic commit owner:** validate one complete state, program it as one
   transaction, associate a monotonic submission/present ID, and declare
   success only after the matching hardware vblank/page-flip interrupt.
8. **Capture owner:** copy/read back the actual committed scanout after its
   completion interrupt, report exact dimensions/byte count, and calculate the
   checksum over the visible XRGB8888 pixels read from that physical scanout.
   The adapter contract is tightly packed (`width * height * 4`), so the owner
   must copy rows into canonical packed order and exclude pitch padding before
   calculating the checksum. A Vulkan staging buffer is not scanout capture
   evidence.
9. **Capability/device-node owner:** expose only narrowly scoped mode,
   framebuffer, atomic-present, completion, and capture operations. Mint
   `Qrb2210BoardDeviceHandle` and `Qrb2210DrmKmsKernel*Receipt` values from
   kernel-owned state with boot ID and driver generation.

## Adapter contract mapping

The kernel owner must implement the existing
`Qrb2210DrmKmsKernelPort`; the staged work must not introduce another display
port or bypass `Qrb2210DrmKmsDisplayProvider`:

- `readiness_status()` remains unavailable until the physical identity below
  can be derived from one live kernel-owned binding.
- `physical_identity(binding)` must return the exact board device, boot ID,
  kernel owner, connector, CRTC, plane, framebuffer, and driver generation in
  the binding, with `physical_device` true. The adapter requires the device
  identity `/dev/dri/card0`; a hosted node with that spelling is not proof.
- `atomic_present(binding, readback)` consumes the exact Vulkan device-memory
  readback receipt and may return `presented: true` only after the matching
  hardware completion. Its submission ID, frame ID, framebuffer identity,
  checksum, boot ID, and generation must correlate exactly; submission, frame,
  and present IDs must advance monotonically.
- `capture_scanout(binding, present)` consumes only the last admitted present.
  It must return the same frame/present/framebuffer identity, a strictly
  advancing capture ID, tightly packed visible-pixel byte count, the same
  visible-pixel checksum, and source `qrb2210-drm-kms-scanout`.

DT compatible/revision, resource, IRQ, IOMMU, and mode receipts in Stages A/B
are kernel-internal prerequisites. They are not substitutes for any field in
the public identity/present/capture receipts and do not independently make the
provider ready.

## Staged implementation plan

### Stage A — discovery and interrupt foundation

- Extend FDT parsing without changing the existing QEMU/RISC-V result type.
- Add typed platform resources and QRB2210 fixture coverage from the exact
  board DTB/DTS revision.
- Implement board-discovered GICv3 routing and prove one real display IRQ on
  the attached board.

Exit evidence: SimpleOS boot receipt records exact DT compatible/revision,
resource ranges, interrupt number, boot ID, and driver generation. No display
capability is promoted.

### Stage B — memory and inactive display probe

- Bind power/clock/reset/interconnect and SMMU owners.
- Probe MDSS/DPU and the physical connector path read-only first.
- Allocate and map two XRGB8888 scanout buffers with checked stride and
  lifetime; retain one kernel-owned capture buffer.

Exit evidence: resource, IOMMU, and mode receipts originate from one boot and
generation; unsupported revisions and modes remain unavailable.

### Stage C — modeset and atomic present

- Implement initial modeset and plane state validation.
- Commit a known scanout buffer atomically.
- Mint `Qrb2210DrmKmsKernelPresentReceipt` only from the matching vblank/page
  flip completion, preserving Vulkan submission/frame/checksum correlation.

Exit evidence: physical panel changes and a hardware interrupt advances the
present ID. Timeout, stale IRQ, cross-boot handle, and device-reset cases fail
closed.

### Stage D — physical capture and adapter binding

- Capture the committed scanout bytes after completion and mint
  `Qrb2210DrmKmsKernelCaptureReceipt` from the kernel owner.
- Bind the owner to `Qrb2210DrmKmsDisplayProvider` without adding a second
  presentation path.
- Exercise animated DrawIR, text, pointer/keyboard events, and audio through
  the shared Simple2D composition root on the attached UNO Q.

Exit evidence: capture dimensions and byte count match the mode, the checksum
matches the tightly packed visible pixels copied from physical scanout and the
provider receipt, consecutive IDs are strictly monotonic, and the live checker
admits the same board/boot/generation.

## Prohibited substitutes

ADB or Android/Linux DRM results, host `/dev/dri`, QEMU ramfb/virtio-gpu, a
static framebuffer copy, replayed interrupts, constructed receipts, and Vulkan
device-memory readback do not satisfy any physical QRB2210 KMS exit criterion.
