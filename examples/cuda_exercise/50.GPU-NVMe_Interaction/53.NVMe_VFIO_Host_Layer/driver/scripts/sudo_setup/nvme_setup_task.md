# NvmeSetupTask - Why No Script Needed

## What This Task Does

`NvmeSetupTask` performs NVMe device setup inside the C++ test harness:
- Opens `/dev/vfio/*` device files
- Maps NVMe BAR0 (controller registers) via `mmap()`
- Configures I/O queues (submission/completion queues)

## Why No Shell Script

All operations use **userspace APIs** after VFIO binding:
- `open()` - Open VFIO device files
- `mmap()` - Map NVMe BAR0 registers
- `ioctl()` - Configure queues via VFIO

No privileged operations beyond what VFIO already provides.

## Prerequisites

1. **Device bound to vfio-pci**: Run `vfio_binding_task.sh` first
2. **User in vfio group**: Access to `/dev/vfio/*`

## Implementation

Setup happens in C++ code:
```cpp
// File: src/host/mapper/mapper_host.cpp
NvmeDevice dev(nvme_bdf);
dev.open_vfio();         // open(/dev/vfio/*)
dev.map_bar0();          // mmap() BAR0
dev.create_io_queues();  // ioctl() queue setup
```

**Result**: No separate script needed - all handled in test harness.
