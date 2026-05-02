<!-- codex-design -->
# Agent Tasks: x86_64 Desktop Driver Completion

## Assumed Selection

Use Feature Option B and NFR Option 2 unless the user selects a different requirement option.

## P0: Driver Acceptance Matrix

- Define the mandatory x86_64 QEMU desktop driver matrix: UEFI/OVMF, ACPI/MADT, PCI, NVMe or VirtIO-BLK, framebuffer/BGA or VirtIO-GPU, PS/2 input, virtio-net.
- Add one serial capability summary emitted during desktop boot: platform, storage, display, input, network, DMA, interrupt mode.
- Make resident launch fallback, hidden heap-copy DMA fallback, and false acceleration claims fail the complete-driver acceptance lane.

## P0: Platform And Device Discovery

- Ensure UEFI/OVMF desktop scenario logs boot path, ACPI RSDP/MADT parse status, PCI device count, and selected interrupt mode.
- Add PCI resource ownership records for BAR, IRQ, DMA, and device class before drivers bind.
- Keep polling fallback legal only when the capability summary says `interrupt_mode=polling`.

## P0: Storage Driver Path

- Unify NVMe and VirtIO-BLK read/write result summaries around the shared DMA descriptor.
- Ensure the desktop disk mount and packaged app reads use generic VFS byte streams, not special host or resident bridges.
- Add timeout and completion-error markers for storage queues.

## P1: Display And Input

- Report display mode as `framebuffer`, `bga`, or `virtio_gpu`, with `accelerated=false` unless VirtIO-GPU command completion is observed.
- Keep PS/2 keyboard/mouse as QEMU desktop input acceptance.
- Add xHCI enumeration diagnostics as non-blocking hardware-alpha output.

## P1: Network

- Require virtio-net initialization, MAC reporting, queue setup, and a bounded packet/TCP smoke through the SimpleOS netstack.
- Report net backend capabilities; keep RDMA, SR-IOV, and packet I/O disabled unless explicitly selected by capability.

## P2: Verification And Rollout

- Add SPipe coverage for capability summaries and false-claim rejection.
- Add QEMU live acceptance with `x64-desktop-uefi`: boot, mount disk, draw desktop, handle input shortcut, launch process-backed app, network smoke, and `TEST PASSED`.
- Run touched-file stub scan and the x86_64 desktop QEMU scenario before marking complete.

