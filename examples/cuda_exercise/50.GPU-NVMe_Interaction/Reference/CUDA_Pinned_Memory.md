# 🎯 CUDA Pinned Memory and NVMe DMA Integration

**Goal**: Understanding the requirements and best practices for using CUDA-pinned host memory and GPU memory as DMA buffers for NVMe devices.

This document explores the technical requirements for integrating CUDA memory with NVMe storage, covering both host-pinned memory and GPU device memory as DMA targets. Understanding these patterns is essential for building high-performance GPU-accelerated storage systems.

---

## Quick Navigation
- [1. NVMe DMA and User-Space Drivers](#1-nvme-dma-and-user-space-drivers)
- [2. CUDA Host Memory for NVMe DMA](#2-cuda-host-memory-for-nvme-dma)
- [3. GPU Memory as DMA Target](#3-gpu-memory-as-dma-target)
- [4. VFIO and IOMMU Requirements](#4-vfio-and-iommu-requirements)
- [5. Key Considerations](#5-key-considerations)
- [6. Summary](#6-summary)
- [7. Practical Recommendations](#7-practical-recommendations)

---

## **1. NVMe DMA and User-Space Drivers**

NVMe controllers implement PCIe devices and transfer data using Direct Memory Access (DMA). This section explains the fundamental requirements for user-space NVMe drivers to interact with device memory.

User-space NVMe drivers (e.g., SPDK or custom VFIO drivers) must program the device with physical addresses of the data buffers. If an IOMMU is enabled (which is common on modern x86 systems), the device cannot see a process's virtual addresses; a translation from the process's virtual address space to I/O virtual addresses (IOVAs) must be configured.

SPDK documentation explains that NVMe controllers can only perform DMA to memory that is locked in physical memory and that user-space drivers rely on either VFIO or UIO drivers to translate virtual addresses to physical pages. SPDK encourages using VFIO with IOMMU enabled because it safely registers memory and provides the IOVA mapping through VFIO DMA map ioctls.

### **1.1 Buffer Requirements for NVMe DMA**

The key requirements for a buffer to be used directly by an NVMe controller are:

1. **Pinned physical pages** – The operating system must prevent the pages from being swapped out.

2. **IOMMU mapping** – The device must see a contiguous IOVA range describing the physical pages.

3. **Alignment and size constraints** – NVMe PRP lists or SGLs require buffers to be aligned to at least 4-KB boundaries; SPDK and DPDK allocate 2-MB huge pages to satisfy this requirement.

---

## **2. CUDA Host Memory for NVMe DMA**

This section examines whether CUDA's host-pinned memory can be used directly for NVMe DMA operations. Understanding the limitations and workarounds is crucial for efficient GPU-storage integration.

### **2.1 Can cudaHostAlloc() Memory Be Used Directly?**

`cudaHostAlloc()` (or `cuMemHostAlloc()`) returns page-locked host memory that is accessible by both the CPU and the GPU. The CUDA driver pins the host pages so that GPU DMA can reach them. However, being pinned does not automatically make the memory visible to a PCIe device via the IOMMU.

NVIDIA's GPUDirect RDMA documentation introduces a critical device attribute:

- **`CU_DEVICE_ATTRIBUTE_HOST_ALLOC_DMA_BUF_SUPPORTED`** – Indicates whether host memory allocated via `cuMemHostAlloc()`/`cudaHostAlloc()` can be exported as a dma_buf file descriptor. If this attribute is false, the memory cannot be shared with other devices via dma-buf.

### **2.2 Exposing CUDA Host Memory to NVMe**

Consequently, on current discrete GPUs these page-locked host buffers are not inherently mapped into the IOMMU and NVMe controllers cannot DMA into them without additional steps. To expose such memory to a device, a user-space driver must:

1. **Retrieve the physical addresses** of the pinned pages. Neither CUDA nor Linux exposes them directly; SPDK solves this by allocating memory through DPDK and registering it with VFIO, which returns an IOVA mapping.

2. **Map the buffer into the NVMe device's IOVA space** using `VFIO_IOMMU_MAP_DMA`. Without VFIO, the IOMMU translation tables are not updated. SPDK's developers explicitly recommend using VFIO with an IOMMU enabled because it programs the IOMMU for user-space DMA.

### **2.3 Recommended Approach**

Therefore, using `cudaHostAlloc()` memory directly as an NVMe DMA target is not sufficient; the memory must still be registered with the IOMMU via VFIO. Moreover, many GPUs do not support exporting host-allocated pinned memory as dma-bufs.

**Best Practice**: In practice, applications that want to use NVMe and CUDA together allocate NVMe buffers through SPDK/DPDK's `spdk_dma_malloc()` or `rte_malloc()`, and then perform `cudaHostRegister()` on that memory to allow GPU access. This path preserves both NVMe DMA requirements and GPU accessibility and is used in SPDK's CUDA engine and NVIDIA GPUDirect Storage.

**Example**: SPDK's CUDA engine uses `spdk_dma_malloc()` to allocate DMA-capable host buffers, then calls `cudaHostRegister()` to make the same memory visible to the GPU. SPDK warns that the memory must be 2-MB aligned and must be registered via `spdk_mem_register()` to create the IOVA mapping. This demonstrates that memory pinned by CUDA alone does not meet NVMe DMA requirements; it must be pinned and mapped via VFIO/DPDK first.

---

## **3. GPU Memory as DMA Target**

GPU device memory can serve as a direct DMA target for NVMe devices through GPUDirect RDMA technology. This section covers the technical requirements and available solutions.

### **3.1 GPUDirect RDMA and Pinning GPU Memory**

GPU memory allocated via `cudaMalloc()` or `cuMemAlloc()` resides on the device and is not directly accessible to other devices. GPUDirect RDMA allows devices such as NICs or NVMe controllers to access GPU memory through peer-to-peer DMA.

According to NVIDIA's GPUDirect RDMA documentation, using GPU memory for DMA requires special handling:

1. **GPU memory pinning** – Unlike host memory, GPU memory cannot be pinned with `get_user_pages()`. Instead, a kernel driver must call NVIDIA's `nvidia_p2p_get_pages()` on the GPU pointer (aligned to 64-KB boundaries) to obtain a page table of physical GPU pages that can be programmed into the device's DMA engine. The driver must also call `nvidia_p2p_put_pages()` when the memory is no longer used. User-space cannot perform these calls directly; the device driver must be modified to integrate with the NVIDIA kernel module.

2. **IOMMU translation** – When an IOMMU is enabled, the GPU's physical addresses differ from the CPU's physical addresses. The device driver must call `nvidia_p2p_dma_map_pages()` to map the GPU pages into the IOMMU address space.

### **3.2 Specialized Solutions**

Because of these requirements, most commodity NVMe drivers cannot DMA directly into GPU memory. Specialized solutions exist:

#### **3.2.1 GPUDirect Storage (GDS)**

This NVIDIA technology allows NVMe controllers to directly read/write GPU memory. It uses a kernel module (`nvidia-peermem`) to perform the above pinning and IOMMU mapping, and user-space uses the `cuFile` API to submit I/O. The NVMe controller must support peer-to-peer DMA. The GDS blog notes that it provides a direct path between storage and GPU memory and eliminates the need for bounce buffers.

#### **3.2.2 Custom User-Space NVMe Stacks**

Projects like `libnvm` claim to provide NVMe access directly from CUDA kernels; their README states that I/O queues and data buffers can reside in GPU memory, eliminating CPU involvement. Such stacks typically use GPUDirect RDMA and `nvidia-peermem` to obtain GPU physical pages and map them to the NVMe device. The device must be bound to VFIO so that user-space can configure IOMMU mappings and program NVMe registers.

#### **3.2.3 GPUDirect RDMA User APIs**

CUDA 13.0+ supports `cuMemGetHandleForAddressRange()` with handle type `CU_MEM_RANGE_HANDLE_TYPE_DMA_BUF_FD`. If the device attributes `CU_DEVICE_ATTRIBUTE_DMA_BUF_SUPPORTED` and (for host memory) `CU_DEVICE_ATTRIBUTE_HOST_ALLOC_DMA_BUF_SUPPORTED` are set, this API returns a dma_buf file descriptor for GPU memory.

A user-space driver can pass this FD into VFIO's DMA-mapping ioctls to map GPU memory into the IOMMU and share it with an NVMe device. This approach is supported by the `nvidia-peermem` module and is the basis for GPUDirect Storage.

### **3.3 GDRCopy**

GDRCopy is a user-space library that allows the CPU to map GPU memory into its address space for low-latency copies. It uses GPUDirect RDMA internally but is not a mechanism for NVMe DMA.

The README clarifies that `gdr_pin_buffer()` accepts addresses returned by `cudaMalloc()` and that the user must ensure page-aligned addresses; contiguous allocations may not map as a single region. GDRCopy is primarily used for CPU copy, not for letting other devices (like NVMe) read or write GPU memory.

---

## **4. VFIO and IOMMU Requirements**

This section explains the critical role of VFIO in mapping both host-pinned and GPU memory for NVMe DMA operations. VFIO is essential for user-space drivers to safely program IOMMU translations.

### **4.1 Is VFIO Needed for GPU Memory DMA?**

**Yes.** When a device driver wants to DMA into GPU memory in user space, it must program the IOMMU to map the GPU pages into the device's domain. This is usually done via VFIO's DMA map ioctls (`VFIO_IOMMU_MAP_DMA` and `VFIO_IOMMU_UNMAP_DMA`).

The `nvidia-peermem` module exports GPU memory as dma-buf, which user-space can import and map via VFIO. Without VFIO (e.g., using kernel NVMe driver with GPUDirect RDMA patches), mapping is performed in kernel space. For user-space drivers, VFIO is the standard way to set up DMA mappings; IOVA translation is necessary even if the memory is already pinned.

---

## **5. Key Considerations**

Understanding these considerations is essential for building robust and performant GPU-NVMe integration systems.

### **5.1 Page Size & Alignment**

- **NVMe requirements**: PRP lists require 4-KB aligned segments; SPDK uses 2-MB hugepages to reduce list length
- **GPU memory**: `nvidia_p2p_get_pages()` requires pointers aligned to 64-KB boundaries
- **GDRCopy**: `gdr_map()` also demands page-aligned addresses

### **5.2 NUMA Locality**

For best performance, both the NVMe device and the GPU should reside under the same PCIe root complex. GPUDirect RDMA works only when devices share a PCIe switch or root complex.

### **5.3 Driver Support**

The NVMe controller's firmware must support peer-to-peer DMA. Some Linux NVMe drivers include experimental P2PDMA support, but user-space stacks (SPDK) typically do not support GPU memory directly and rely on GDS.

### **5.4 Security and Stability**

Mapping GPU memory into the IOMMU exposes the GPU's memory pages to devices; incorrect programming can lead to memory corruption. VFIO's IOMMU mapping and the `nvidia-peermem` driver enforce permission checks.

---

## **6. Summary**

### **6.1 CUDA Pinned Host Memory**

`cudaHostAlloc()` produces page-locked host memory but does not automatically make it visible to other PCIe devices. To use it as an NVMe DMA buffer via a user-space driver, the memory must be registered with VFIO/DPDK so that the IOMMU mapping is configured. Many GPUs do not support exporting such memory as dma-bufs.

**Recommended approach**: Allocate DMA-capable memory through SPDK/DPDK (`spdk_dma_malloc()`), then register it with CUDA using `cudaHostRegister()`.

### **6.2 Pinned GPU Memory**

GPU memory can be a DMA target only through GPUDirect RDMA. The device driver must call NVIDIA's `nvidia_p2p_get_pages()` to pin the GPU memory, obtain a page table, and map it into the IOMMU. User-space drivers must use VFIO to map the resulting pages and program the NVMe device.

Technologies like GPUDirect Storage or custom stacks (e.g., `libnvm`) implement this. GDRCopy is for CPU–GPU copies and does not help for NVMe DMA. New CUDA APIs (`cuMemGetHandleForAddressRange`) provide a dma-buf descriptor for GPU memory on supported devices, which can then be mapped via VFIO.

### **6.3 VFIO Role**

VFIO is needed to map both host-pinned memory and GPU memory into the NVMe device's IOMMU address space. Without VFIO, user-space drivers cannot program the IOMMU, and the device cannot see the memory. SPDK strongly recommends using VFIO with IOMMU enabled to ensure safe DMA operations.

---

## **7. Practical Recommendations**

### **7.1 Host Buffers Accessible by Both GPU and NVMe**

Allocate memory via SPDK/DPDK using hugepages, register it with CUDA using `cudaHostRegister()`, and then map it via VFIO to the NVMe device. **Do not rely solely on `cudaHostAlloc()`.**

```cpp
// Recommended approach
void* host_buffer = spdk_dma_malloc(size, alignment, NULL);
cudaHostRegister(host_buffer, size, cudaHostRegisterDefault);
// Map via VFIO for NVMe access
```

### **7.2 Direct NVMe ↔ GPU Transfers**

Use NVIDIA's GPUDirect Storage or similar technologies that integrate NVMe drivers with GPUDirect RDMA. Ensure your hardware (GPU, NVMe controller, platform) supports peer-to-peer DMA and that the `nvidia-peermem` module is available.

In user-space, use `cuMemGetHandleForAddressRange()` to obtain a dma_buf FD for GPU memory and map it via VFIO.

```cpp
// CUDA 13.0+ approach
CUmemGenericAllocationHandle handle;
int dma_buf_fd;
cuMemGetHandleForAddressRange(&handle, gpu_ptr, size,
                                CU_MEM_RANGE_HANDLE_TYPE_DMA_BUF_FD, 0);
// Map dma_buf_fd via VFIO for NVMe access
```

### **7.3 Alignment and Device Support Verification**

- Ensure memory addresses are aligned (4-KB or 64-KB)
- Verify GPU supports dma_buf export (`CU_DEVICE_ATTRIBUTE_DMA_BUF_SUPPORTED`)
- Confirm NVMe device's driver supports P2P DMA
- Use VFIO for IOMMU mappings to ensure safety and portability

---

## **References**

- [NVIDIA GPUDirect RDMA Documentation](https://docs.nvidia.com/cuda/gpudirect-rdma/)
- [SPDK User-Space NVMe Driver](https://spdk.io/)
- [CUDA Runtime API Documentation](https://docs.nvidia.com/cuda/cuda-runtime-api/)
- [GPUDirect Storage](https://developer.nvidia.com/gpudirect-storage)
