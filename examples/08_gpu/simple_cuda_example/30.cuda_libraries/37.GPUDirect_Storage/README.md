# GPUDirect Storage

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

GPUDirect Storage (GDS) is an NVIDIA hardware-specific feature that enables direct
data paths between GPU memory and storage devices (NVMe SSDs), bypassing the CPU
and system memory. This requires specific NVIDIA hardware, drivers, and filesystem
support (ext4, XFS on Linux).

This is a hardware-level optimization that cannot be abstracted in Simple's GPU model.

For high-performance data loading in Simple, consider:
- **Async I/O:** Use Simple's async file operations to overlap I/O with computation
- **Memory-mapped files:** Map large datasets directly into address space
- **Streaming buffers:** Pipeline data loading with GPU computation

## Original CUDA Exercise

See the original GPUDirect Storage exercise for the NVIDIA-specific implementation
using `cuFileRead()`, `cuFileBufRegister()`, etc.

**Reference:** [NVIDIA GPUDirect Storage](https://docs.nvidia.com/gpudirect-storage/overview-guide/index.html)
