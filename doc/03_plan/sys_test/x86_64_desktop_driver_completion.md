<!-- codex-design -->
# System Test Plan: x86_64 Desktop Driver Completion

## Coverage

- UEFI desktop boot emits OVMF/UEFI boot marker, ACPI marker, PCI device count, and interrupt mode.
- Driver summary contains storage, display, input, network, DMA, and fallback fields.
- Storage path mounts the desktop disk and reads packaged app bytes through VFS.
- Display path reaches `desktop-ready` and labels framebuffer versus VirtIO-GPU acceleration truthfully.
- Input path drives at least one launcher shortcut.
- Network path initializes virtio-net and completes a bounded smoke.
- Complete-driver lane rejects resident process fallback and false acceleration markers.

## Acceptance Markers

- `[driver-summary] platform=x86_64 boot=uefi`
- `[driver-summary] acpi=madt-ok pci_devices=... interrupt_mode=...`
- `[driver-summary] storage=... dma=... hidden_copy=false`
- `[driver-summary] display=... accelerated=...`
- `[driver-summary] input=ps2`
- `[driver-summary] network=virtio-net`
- `[desktop-e2e] process-backed:ok`
- `TEST PASSED`

## Negative Markers

- `process-backed:resident`
- `process-backed:unknown`
- `hidden_copy=true`
- `accelerated=true driver=vga`
- `FAULT @`
- `EXCEPTION`

