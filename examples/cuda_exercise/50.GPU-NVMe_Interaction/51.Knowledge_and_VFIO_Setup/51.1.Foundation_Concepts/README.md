# 🎯 Part 51.1: Foundation Concepts

**Goal**: Understand the fundamental address spaces and memory translation mechanisms required for GPU-NVMe integration.

This section covers the core concepts of address spaces (CPU VA, Physical, IOVA, GPU VA, MMIO) and how the IOMMU provides memory protection and address translation for DMA operations.

---

## Quick Navigation

- [51.1.1 Address Spaces and Memory Model](#5111-address-spaces-and-memory-model)
- [51.1.2 IOMMU Architecture and Translation](#5112-iommu-architecture-and-translation)

---

## **51.1.1 Address Spaces and Memory Model**

In GPU-NVMe systems, different components use different address spaces to refer to memory. Understanding these address types and when to use each is critical for correct DMA operations.

### **The Five Address Spaces**

| Address Type | Who Uses It | What It Is | How to Get It | Valid Where |
|--------------|-------------|------------|---------------|-------------|
| **CPU Virtual Address (VA)** | CPU userspace code | Process virtual address | `malloc()`, `posix_memalign()` | CPU only, not valid for DMA |
| **Physical Address (PA)** | System RAM | Actual RAM location | Kernel manages (hidden from userspace) | Not directly used when IOMMU is enabled |
| **PCI/MMIO Address** | CPU for device registers | BAR address for NVMe registers | Map BAR via VFIO | Only for MMIO (doorbells, registers) |
| **I/O Virtual Address (IOVA)** | NVMe controller (DMA) | Device DMA address | VFIO `VFIO_IOMMU_MAP_DMA` | Program into ASQ/ACQ, PRP/SGL |
| **GPU Virtual Address (GPU-VA)** | GPU | GPU memory pointer | `cudaMalloc()`, `cuMemAlloc()` | GPU only, not directly DMA-capable |

Reference: [Address_Space.md](../../Reference/Address_Space.md)

### **Unified Virtual Addressing (UVA)**

**Unified Virtual Addressing (UVA)** is a CUDA feature that provides a unified address space between CPU and GPU memory, allowing the same pointer value to be used for accessing memory from both CPU and GPU code.

**Key Benefits:**
- **Single Address Space**: Same pointer value works on both CPU and GPU
- **Simplified Memory Management**: No need to track separate host/device pointers
- **Zero-Copy Access**: GPU can directly access pinned host memory without explicit copies
- **Automatic Migration**: CUDA runtime can migrate data between host and device as needed

**UVA Memory Types:**

| Memory Type | Allocation | CPU Access | GPU Access | Resides In |
|-------------|------------|------------|------------|------------|
| **Host Pinned** | `cudaHostAlloc()` | Direct | UVA pointer | System RAM |
| **Device Memory** | `cudaMalloc()` | Via UVA | Direct | GPU VRAM |
| **Managed Memory** | `cudaMallocManaged()` | Direct | Direct | Migrates automatically |

**UVA Address Space Layout:**

```
Unified Virtual Address Space (64-bit):
┌─────────────────────────────────────────────────────────────┐
│ 0x0000000000000000 - 0x00007FFFFFFFFFFF: Host VA space      │
│ 0x0000800000000000 - 0x00007FFFFFFFFFFF: GPU accessible     │
│ 0x1000000000000000 - 0x1FFFFFFFFFFFFFFF: GPU VRAM           │
│ 0x7F0000000000000  - 0x7FFFFFFFFFFFFFFF: Host pinned (UVA)  │
└─────────────────────────────────────────────────────────────┘
```

**Example UVA Usage:**

```c
// Allocate UVA host pinned memory
void *uva_buffer;
cudaHostAlloc(&uva_buffer, size, cudaHostAllocDefault);

// Same pointer works on CPU
memset(uva_buffer, 0x42, size);  // CPU writes

// Same pointer works on GPU
gpu_kernel<<<blocks, threads>>>(uva_buffer);  // GPU reads

// Can be used for NVMe DMA (via IOVA mapping)
struct vfio_iommu_type1_dma_map map = {
    .vaddr = (uint64_t)uva_buffer,  // UVA pointer as CPU-VA
    .iova = 0x7800000000ULL,        // IOVA for NVMe
    .size = size
};
ioctl(container, VFIO_IOMMU_MAP_DMA, &map);

// NVMe writes to IOVA, data appears in uva_buffer for both CPU and GPU
```

**UVA in GPU-NVMe Context:**

UVA is particularly useful for GPU-NVMe integration because:

1. **Host Staging Buffers**: Use `cudaHostAlloc()` to create pinned memory that's accessible from both CPU (for setup) and GPU (for processing)
2. **Zero-Copy GPU Access**: GPU can read NVMe data directly from host pinned buffers without `cudaMemcpy()`
3. **Simplified Pointer Management**: Single pointer for CPU setup, GPU processing, and VFIO mapping

**UVA Detection and Requirements:**

```c
// Check if UVA is supported
int uva_supported;
cudaDeviceGetAttribute(&uva_supported, 
                       cudaDevAttrUnifiedAddressing, 
                       device_id);

if (uva_supported) {
    printf("UVA supported - can use unified pointers\n");
} else {
    printf("UVA not supported - separate host/device pointers needed\n");
}
```

**Requirements for UVA:**
- CUDA Compute Capability 2.0 or higher
- 64-bit operating system and application
- Fermi architecture or newer GPU

### **VFIO_IOMMU_MAP_DMA Explained**

`VFIO_IOMMU_MAP_DMA` is an **ioctl command code** used to create mappings between user-space virtual addresses and device DMA addresses (IOVAs).

**What it does:**
- Creates a mapping: `CPU Virtual Address → IOVA`
- Programs the IOMMU to translate device DMA accesses from IOVA to physical addresses
- Pins the memory pages to prevent swapping
- Enforces access permissions (read/write) for the device

**Usage example:**

```c
#include <linux/vfio.h>

// Allocate buffer
void *my_buffer = aligned_alloc(4096, buffer_size);

// Create IOVA mapping
struct vfio_iommu_type1_dma_map dma_map = {
    .argsz = sizeof(dma_map),
    .flags = VFIO_DMA_MAP_FLAG_READ | VFIO_DMA_MAP_FLAG_WRITE,
    .vaddr = (uint64_t)my_buffer,        // CPU VA
    .iova = 0x7000000000ULL,              // IOVA (device DMA address)
    .size = buffer_size
};

if (ioctl(vfio_container_fd, VFIO_IOMMU_MAP_DMA, &dma_map) < 0) {
    perror("Failed to create DMA mapping");
}

// Now use IOVA in NVMe commands
nvme_cmd.prp1 = 0x7000000000;  // Use IOVA, not CPU-VA
```

**Complete flow:**

```
1. Allocate buffer:        void *buf = malloc(size);          // CPU-VA: 0x7f10abcd0000
2. Map with VFIO:          ioctl(fd, VFIO_IOMMU_MAP_DMA, ...) // Creates IOVA: 0x7000000000
3. Program NVMe:           cmd.prp1 = 0x7000000000;           // Use IOVA in command
4. NVMe controller DMA:    Device reads/writes to IOVA 0x7000000000
5. IOMMU translates:       IOVA → Physical Address (transparent)
6. Data appears in:        CPU can read via buf pointer (CPU-VA)
```

**Critical Rule:** Never use CPU virtual addresses directly in NVMe queue entries or PRP/SGL fields. Always use the IOVA obtained from `VFIO_IOMMU_MAP_DMA`.

### **Address Space Relationships**

```
┌─────────────────────────────────────────────────────────────┐
│ CPU Process                                                 │
│  Virtual Address (malloc) → MMU → Physical Address          │
└───────────────────────────────┬─────────────────────────────┘
                                │
                                ↓ (when pinned & mapped via VFIO)
┌─────────────────────────────────────────────────────────────┐
│ IOMMU                                                       │
│  IOVA (for NVMe) ──────────→ Physical Address               │
└───────────────────────────────┬─────────────────────────────┘
                                │
                                ↓ (NVMe uses IOVA for DMA)
┌─────────────────────────────────────────────────────────────┐
│ NVMe Controller                                             │
│  Reads/Writes using IOVA addresses                          │
│  (PRP1, PRP2, ASQ/ACQ base all use IOVA)                    │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│ GPU Device                                                  │
│  GPU Virtual Address → GPU MMU → GPU Physical (VRAM)        │
│  (Requires special kernel support to map to IOVA)           │
└─────────────────────────────────────────────────────────────┘
```

### **Example GPU to NVMe IO Address Mapping (Optimal Placement)**

| Object | CPU VA | IOVA (for NVMe) | GPU VA | Physical Location | Who Writes | Who Reads | Why This Location |
|--------|--------|-----------------|--------|------------------|-----------|----------|-------------------|
| Admin SQ | `0x7f10_abcd_0000` | `0x7100_0000_0000` | - | **Host RAM** | CPU | NVMe (DMA) | CPU builds commands + rings doorbell; host RAM minimizes latency |
| Admin CQ | `0x7f10_abcd_1000` | `0x7200_0000_0000` | - | **Host RAM** | NVMe (DMA) | CPU | CPU polls completions; host RAM enables cache-friendly polling |
| I/O SQ | `0x7f10_abcd_2000` | `0x7300_0000_0000` | `0x7f10_abcd_2000` (UVA) | **Host RAM** | CPU/GPU | NVMe (DMA) | CPU/GPU build commands; CPU rings doorbell (see Note 1) |
| I/O CQ | `0x7f10_abcd_3000` | `0x7400_0000_0000` | `0x7f10_abcd_3000` (UVA) | **Host RAM** | NVMe (DMA) | CPU/GPU | CPU polls for fast path; host RAM ~6× faster than GPU VRAM read |
| PRP List | `0x7f10_abcd_5000` | `0x7500_0000_0000` | - | **Host RAM** | CPU | NVMe (DMA) | CPU builds; NVMe reads once; small size (<4KB); no benefit from GPU |
| Buffer Pool Metadata | - | `0x7600_0000_0000` | `0x1400_3000_0000` | **GPU VRAM** | GPU | GPU | GPU-managed allocation; VRAM atomics ~10× faster than PCIe roundtrip |
| Data Buffer (Host pinned, Modules ≤54) | `0x7f10_abcd_4000` | `0x9800_0000_0000` | `0x7f10_abcd_4000` (UVA) | **Host RAM** | NVMe (DMA) | GPU (UVA) | Zero-copy GPU access; simpler than GPU VRAM mapping |
| Data Buffer (GPU VRAM, Modules ≥55) | - | `0x9900_0000_0000` | `0x1400_2000_0000` | **GPU VRAM** | NVMe (DMA) | GPU | Direct NVMe→GPU; eliminates host bounce buffer; ~2× bandwidth |
| NVMe BAR0 (Doorbells) | `0x7f10_f720_0000` | - | - | NVMe Device | CPU | NVMe (HW) | MMIO registers; CPU writes to ring doorbells |

**Placement Notes:**

**Default vs Legacy GPU Buffer**
- **Default GPU Buffer (Optimal)**: SQ/CQ/PRP in **host RAM**, data + buffer pool in **GPU VRAM**. This is now the standard for Modules 53, 56, 57, 58, 59.
- **Naive GPU Buffer (Legacy)**: SQ/CQ/PRP/data all in **GPU VRAM**; kept for Module 56 experiments. Expect higher CPU doorbell and polling latency.

**Note 1: GPU-Initiated Commands (Advanced)**
- Modules 56+ explore GPU kernels writing directly to SQ
- This requires SQ in GPU-accessible memory (host pinned UVA or GPU VRAM)
- Trade-off: GPU avoids CPU involvement but adds doorbell synchronization complexity
- See [Module 56: GPU Queue with GPU Buffer](../../56.GPU_Queue_GPU_Buffer/README.md) for details

**Note 2: Why Not CQ in GPU VRAM?**
- GPU VRAM read from CPU: ~1000 cycles (PCIe latency)
- Host RAM read from CPU: ~160 cycles (cached)
- Polling CQ is latency-critical → host RAM wins by 6×
- Exception: Pure GPU-to-GPU pipelines may benefit from GPU VRAM CQ if GPU polls directly

**Performance Summary:**
- **Control plane in Host RAM** (SQ/CQ/PRP): Optimizes CPU command submission and completion processing
- **Data plane in GPU VRAM** (buffers/pool): Eliminates bounce buffers, enables direct NVMe→GPU DMA
- **Result**: ~2-3× speedup for typical workloads vs. all-host or all-GPU placement

For detailed performance analysis, see [Address_Space.md: Optimal Memory Placement Strategy](../../Reference/Address_Space.md#optimal-memory-placement-strategy)

**Address usage rules:**

1. **For DMA addresses** (ASQ/ACQ base, PRP entries, SGL entries): Always use **IOVA**
2. **For MMIO registers** (BAR0 doorbells, controller registers): Use **CPU virtual address** (mapped from BAR)

**Host-pinned vs. GPU VRAM data buffers**

- **Host-pinned UVA path (Modules ≤54)**: Allocate page-locked host memory using `cudaHostAlloc()` with UVA support, register it with VFIO for NVMe DMA, and access from both CPU and GPU using the same unified pointer. NVMe DMAs into host RAM, and the GPU reads the results through zero-copy UVA access—no `cudaMemcpy()` needed.
- **GPU VRAM path (Modules ≥55)**: Allocate device memory with `cudaMalloc`, export the pages through `nvidia-peermem`/GPUDirect Storage, and obtain the corresponding IOVAs via the kernel helper (`nvidia_p2p_get_pages`). NVMe now DMAs directly into GPU memory—no host bounce buffer—once the VFIO mapping is created.

Direct NVMe→GPU copies demand the GPU VRAM path: the memory must be registered with the NVIDIA peer-to-peer driver so the NVMe controller sees a valid IOVA. Without that registration, the host-pinned path is the only safe option.

---

## **51.1.2 IOMMU Architecture and Translation**

The IOMMU (Input-Output Memory Management Unit) provides memory protection and address translation for devices performing DMA operations.

### **What is IOMMU?**

IOMMU is a hardware component between PCIe devices and system memory that provides:

1. **Address Translation**: Translates IOVA → Physical Address
2. **Memory Protection**: Prevents devices from accessing unauthorized memory
3. **Memory Isolation**: Ensures different devices/VMs cannot access each other's memory

**Hardware implementations:**
- **Intel VT-d** (Virtualization Technology for Directed I/O)
- **AMD-Vi** (AMD I/O Virtualization)
- **ARM SMMU** (System Memory Management Unit)

Reference: [IOMMU_Technical_Guide.md](../../Reference/IOMMU_Technical_Guide.md)

### **Why IOMMU is Needed**

Without IOMMU, devices can access **any** physical memory, creating security problems:

```
Without IOMMU:
┌─────────────────────────────────┐
│ Physical Memory                 │
├─────────────────────────────────┤
│ 0x0000-0x0FFF: Process A        │
│ 0x1000-0x1FFF: Kernel           │
│ 0x2000-0x2FFF: Process B        │
└─────────────────────────────────┘
    ↑                    ↑
Device owned by Process A could
access Process B's memory - SECURITY BREACH!

With IOMMU:
┌─────────────────────────────────┐
│ IOMMU Domain 1 (Process A)      │
├─────────────────────────────────┤
│ IOVA 0x0000 → PA 0x0000         │
│ IOVA 0x1000 → PA 0x5000         │
└─────────────────────────────────┘
Device can ONLY access its own domain - SAFE!
```

### **IOMMU Translation Flow**

```
1. NVMe Device Initiates DMA:
   "I want to write to IOVA 0x2000"
   ↓
2. IOMMU Intercepts:
   - Check requester ID (PCIe Bus:Device.Function)
   - Check if IOVA 0x2000 is mapped
   - Check permissions (read/write)
   - Translate IOVA → Physical Address
   ↓
3. Translation Result:
   "IOVA 0x2000 → Physical 0x8000"
   ↓
4. Memory Access:
   Write data to physical address 0x8000
```

### **IOMMU Page Tables**

IOMMU uses multi-level page tables similar to CPU MMU:

```
Intel VT-d Page Table (4-level):

IOVA (48-bit):
┌────┬────┬────┬────┬────────────┐
│ L4 │ L3 │ L2 │ L1 │  Offset    │
│ 9b │ 9b │ 9b │ 9b │  12 bits   │
└────┴────┴────┴────┴────────────┘

Page Table Walk:
Root Table (indexed by PCIe Bus)
    ↓
Level 4 Table (indexed by IOVA[47:39])
    ↓
Level 3 Table (indexed by IOVA[38:30])
    ↓
Level 2 Table (indexed by IOVA[29:21])
    ↓
Level 1 Table (indexed by IOVA[20:12])
    ↓
Physical Page (PA[51:12] + IOVA[11:0])
```

**IOTLB (I/O Translation Lookaside Buffer):**
- Caches recent IOVA → PA translations
- Typical hit rate: 95-99%
- Miss requires full page table walk (~4 memory reads)

### **VFIO and IOMMU Integration**

VFIO provides userspace interface to IOMMU:

```c
// 1. Open VFIO container
int container = open("/dev/vfio/vfio", O_RDWR);

// 2. Attach group to container
int group = open("/dev/vfio/1", O_RDWR);
ioctl(group, VFIO_GROUP_SET_CONTAINER, &container);

// 3. Set IOMMU type
ioctl(container, VFIO_SET_IOMMU, VFIO_TYPE1_IOMMU);

// 4. Map memory for DMA
struct vfio_iommu_type1_dma_map map = {
    .argsz = sizeof(map),
    .flags = VFIO_DMA_MAP_FLAG_READ | VFIO_DMA_MAP_FLAG_WRITE,
    .vaddr = (uint64_t)host_buffer,
    .iova  = 0x7000000000ULL,
    .size  = buffer_size
};
ioctl(container, VFIO_IOMMU_MAP_DMA, &map);

// Now device can DMA using IOVA 0x7000000000
```

---

## **Summary**

This section covered the foundation concepts for GPU-NVMe integration:

1. **Address Spaces**: Five distinct address types (CPU-VA, PA, MMIO, IOVA, GPU-VA) and when to use each
2. **VFIO_IOMMU_MAP_DMA**: The mechanism to create IOVA mappings for device DMA
3. **IOMMU**: Hardware that translates IOVA → PA and enforces memory protection
4. **Critical Rule**: Always use IOVA (not CPU-VA or GPU-VA) in NVMe DMA fields

**Key Takeaways:**
- **UVA simplifies GPU-NVMe integration** by providing unified pointers that work on both CPU and GPU
- **Host-pinned UVA memory** enables zero-copy access patterns: NVMe → Host RAM ← GPU (via UVA)
- **Always use IOVA addresses** in NVMe commands, even when working with UVA pointers
- **IOMMU provides security** by isolating device DMA operations to authorized memory regions

**Next**: [Part 51.2: NVMe Fundamentals](../51.2.NVMe_Fundamentals/README.md) - Learn about NVMe queue architecture, doorbells, PRP/SGL, and DBC.
