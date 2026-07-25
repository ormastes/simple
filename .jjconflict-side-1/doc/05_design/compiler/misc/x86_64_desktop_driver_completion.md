<!-- codex-design -->
# Detail Design: x86_64 Desktop Driver Completion

## Data Flow

1. UEFI/OVMF boots the x86_64 desktop image and passes boot state through the existing boot-info path.
2. Kernel parses ACPI and initializes interrupt routing before driver binding.
3. PCI manager enumerates devices and grants typed resources to matching drivers.
4. Storage driver mounts the desktop disk through VFS.
5. Display driver exposes framebuffer or VirtIO-GPU surface to compositor.
6. Input driver feeds keyboard/mouse events into the desktop shortcut path.
7. Network driver initializes virtio-net and exposes backend capabilities to netstack/socket code.
8. Driver summary is emitted before `desktop-ready` or immediately after device init.

## Interfaces

- `DriverCapabilitySummary`: driver name, device class, device id, dma mode, interrupt mode, acceleration flag, fallback flag, last error.
- `StorageDriverSummary`: block size, queue count, completion mode, mount result.
- `DisplayDriverSummary`: mode, resolution, stride, acceleration, command completion evidence.
- `NetworkDriverSummary`: MAC, rx/tx queue state, backend capabilities, smoke result.

## Error Handling

- Initialization failure records a typed summary and returns a failed state; desktop may continue only if a fallback driver exists.
- Timeout failures must include driver name, queue id, command id, and timeout budget.
- Hidden fallback copies are legal only when summary says `hidden_copy=false` is not claimed and the status identifies copied I/O.

## Verification Hooks

- Serial driver summary markers for live QEMU.
- Unit specs for summary construction and false-claim rejection.
- System spec for `x64-desktop-uefi` complete-driver lane.

