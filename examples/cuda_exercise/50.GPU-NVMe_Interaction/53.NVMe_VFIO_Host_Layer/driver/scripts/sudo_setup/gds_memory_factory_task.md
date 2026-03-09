# GdsMemoryFactoryTask - Why No Script Needed

## What This Task Does

Allocates GPU memory accessible by NVMe via **GPUDirect Storage (GDS)**:
- Uses NVIDIA cuFile API for storage-GPU direct path
- Bypasses CPU for data transfers
- Leverages NVIDIA's proprietary GDS stack

## Why No Shell Script

GDS setup is handled entirely by **NVIDIA's software stack**:

1. **Kernel Driver**: `nvidia-fs.ko` (NVIDIA's GDS kernel module)
2. **Userspace Library**: `libcufile.so` (cuFile API)
3. **Configuration**: `/etc/cufile.json` (optional tuning)

All setup is done by NVIDIA's installation process - no custom script needed.

## Prerequisites

### 1. Install NVIDIA Drivers with GDS Support

```bash
# NVIDIA driver with GPUDirect Storage
sudo apt install nvidia-driver-XXX  # Version with GDS support
sudo modprobe nvidia-fs             # Load GDS kernel module
```

### 2. Install cuFile Library

```bash
# From NVIDIA CUDA toolkit or separate GDS package
# Provides /usr/lib/x86_64-linux-gnu/libcufile.so
```

### 3. Verify GDS Setup

```bash
# Check kernel module loaded
lsmod | grep nvidia_fs

# Check device node exists
ls -l /dev/nvidia-fs

# Check library available
ldconfig -p | grep cufile
```

## Implementation

Application uses cuFile API directly:

```cpp
// File: src/cuda_gpu/memory/gds_memory_buffer.cpp
#include <cufile.h>

// Allocate GPU buffer
cudaMalloc(&gpu_ptr, size);

// Register with GDS (makes it accessible to NVMe)
CUfileDescr_t cf_descr;
cf_descr.type = CU_FILE_HANDLE_TYPE_OPAQUE_FD;
cf_descr.handle.fd = nvme_fd;

CUfileHandle_t cf_handle;
cuFileHandleRegister(&cf_handle, &cf_descr);

// Read directly to GPU memory (bypasses CPU)
cuFileRead(cf_handle, gpu_ptr, size, offset, 0);
```

**Result**: All GDS operations use NVIDIA's API - no custom setup script.

## What Happens Behind the Scenes

When you call `cuFileRead()`:

```
Application (cuFile API)
    ↓ cuFileRead(gpu_ptr, ...)
libcufile.so (userspace)
    ↓ ioctl()
nvidia-fs.ko (kernel driver)
    ↓ Setup DMA mapping
    ↓ Issue NVMe command
NVMe Controller
    ↓ DMA directly to GPU memory
GPU Memory (VRAM)
```

All managed by NVIDIA stack - no manual intervention needed.

## Comparison: GDS vs Manual P2P

| Aspect | GDS (cuFile) | Manual P2P (Our Driver) |
|--------|--------------|-------------------------|
| **Provider** | NVIDIA proprietary | Custom dual-driver |
| **Setup** | Install NVIDIA packages | Build/load kernel modules |
| **API** | cuFile library | Custom ioctl |
| **Mapping** | Automatic | Manual (2-stage ioctl) |
| **Performance** | Optimized by NVIDIA | Experimental |
| **Script Needed?** | ❌ No | ✅ Yes (gpu_p2p_setup_task.sh) |

**Result**: GDS is turnkey - just install NVIDIA software, no custom scripts.
