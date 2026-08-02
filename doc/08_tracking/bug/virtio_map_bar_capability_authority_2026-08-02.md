# Bug: VirtIO MapBar capability authority mismatch

Status: open

## Reproducer

Inspect syscall 83 dispatch and the VirtIO-GPU modern capability path:

- `src/os/kernel/ipc/syscall.spl` checks the fixed capability tuple
  `DeviceBarMap(0,0,0,0)` rather than the requested device and BAR.
- `src/os/kernel/ipc/syscall_device.spl::_handle_map_bar` accepts a
  caller-provided physical base and length without resolving them from a
  BDF/BAR grant.
- `VirtioGpuDriver.try_map_modern_pci_caps` resolves capability BAR physical
  addresses from PCI config and accesses `bar_phys | offset` without an
  authorized mapping.

## Impact

DEVICE_CFG or Venus `HOST_VISIBLE` SHM on BAR2/BAR4 cannot be mapped with
per-device authority. Physical/virtual conflation can also access the wrong
aperture when BAR and offset bits overlap.

## Required fix

Bind MapBar to packed BDF, BAR index, offset/length, owner token, and generation.
The kernel must resolve the BAR, validate checked containment, map UC/NX pages,
and return a CPU virtual address. Extend the bounded grant ABI beyond BAR0 or
add a per-BAR grant syscall. Then replace the VirtIO-GPU physical `| offset`
path with the authorized mapped aperture plus checked offset.

## Current regression evidence

`test/01_unit/os/drivers/virtio/virtio_gpu_venus_pci_caps_spec.spl` proves the
pure snapshot/parser contract fails closed for missing, invalid, overflowing,
or out-of-aperture grants while preserving the existing 2D-only row.
