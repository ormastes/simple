# Multi-GPU Programming

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Multi-GPU with `cudaSetDevice()`, peer-to-peer memory access

## Simple Approach

Simple abstracts multi-GPU management through the `GpuDevice` API. Instead of raw
CUDA device selection, you use `GpuDevice.get(id)` to obtain a device handle and
execute kernels on specific devices.

Key differences from CUDA:
- **Device selection:** `GpuDevice.get(id)` returns a `Result<GpuDevice, GpuError>` instead of `cudaSetDevice()`
- **Memory transfer:** `gpu_copy_peer(src_buf, dst_buf)` replaces `cudaMemcpyPeer()`
- **Synchronization:** `device.sync()` replaces `cudaDeviceSynchronize()`
- **Error handling:** `Result<T, GpuError>` with `?` operator instead of checking `cudaError_t`

## Concepts Covered

- Enumerating available GPU devices
- Allocating memory on specific devices
- Cross-device memory copies
- Running kernels on multiple devices in parallel
- Synchronizing across devices

## Files

- `main.spl` - Multi-GPU vector addition across two devices
- `spec.spl` - Tests for multi-GPU operations
