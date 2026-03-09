# 🎯 Part 55.0: Shared GPU Memory Implementation

**Goal**: Provide shared implementation foundation for GPU-initiated NVMe I/O with template and runtime APIs, common data structures, and shared headers used by modules 55.1-55.3 and 56.

**Architecture**: Documentation and Reference Module

> **⚠️ IMPORTANT**: The implementation code for this module has been **fully consolidated into Module 53** (NVMe VFIO Host Layer) at `53.NVMe_VFIO_Host_Layer/src/cuda_gpu/`. Module 55.0 now serves **exclusively as documentation** and contains NO source code.

**Implementation Note**: All core implementation has been **consolidated into Module 53** (NVMe VFIO Host Layer) as part of the unified architecture. Module 55.0 now serves primarily as:
- **Documentation** of GPU memory approaches and different doorbell modes
- **Conceptual reference** for GPU-specific patterns (Modes 2-4)
- **Educational guide** to understanding GPU-initiated NVMe I/O

**For new development**, use **Module 53** which provides complete implementations for Modes 0-5 in a single unified codebase with comprehensive performance testing:
- **Source code**: `53.NVMe_VFIO_Host_Layer/src/cuda_gpu/`
- **Libraries**: `libcuda_io_gpu_mem_55.a`, `libmapping_gpu_55.a`
- **Documentation**: [Module 53 Section 53.8](../../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing)

This module historically provided:
- **Template Submit/Poll APIs** with compile-time dispatch for optimal performance (now in Module 53)
- **Runtime Submit/Poll APIs** with dynamic dispatch for flexibility (now in Module 53)
- **Shared Headers** defining GPU queue descriptors and P2P IOCTL interfaces (now in Module 53)
- **Common GPU Memory Management** for buffer pools and DMA mapping (now in Module 53)

## Module Inheritance Hierarchy

```
55.0_Shared_Implementation (This Module)
    ├── Provides: Template APIs, Runtime APIs, Shared Headers
    │
    ├─► 55.1_Host_Daemon_Doorbell
    │       Uses: nvme_gpu_queue.h, gpu_p2p_ioctl.h
    │       Adds: Host daemon for doorbell writes
    │
    ├─► 55.2_DBC_Shadow_Doorbell
    │       Uses: nvme_gpu_queue.h, DBC setup functions
    │       Adds: Hardware DBC shadow doorbell support
    │
    ├─► 55.3_Host_DBC_Daemon
    │       Uses: nvme_gpu_queue.h, DBC setup functions
    │       Adds: Software daemon for DBC shadow buffer polling
    │
    └─► 56.GPU_Queue_GPU_Buffer
            Inherits: All template/runtime APIs from 55.0
            Adds: Doorbell mode abstraction, auto-detection
```

## Project Structure
```
55.0_Shared_Implementation/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration with CUDA support
├── doxygen/           - Doxygen documentation configuration
│   ├── Doxyfile.in               - Doxygen configuration template
│   └── mainpage.md               - Doxygen main page content
├── src/               - Source implementations
│   ├── common/
│   │   ├── cuda_io_gpu_mem.h           - GPU submit/poll template APIs ⭐ NEW
│   │   ├── cuda_io_gpu_mem_impl.h      - Internal implementation details
│   │   ├── nvme_gpu_queue.h            - GPU queue descriptor (SHARED)
│   │   ├── nvme_gpu_queue_impl.h       - GPU queue implementation details
│   │   ├── gpu_p2p_ioctl.h             - P2P IOCTL interface (SHARED)
│   │   └── nvme_vio_cuda_gpu.h         - NVMe VFIO CUDA GPU integration API (includes queue setup)
│   └── kernels/
│       ├── cuda_io_gpu_mem.cpp         - GPU memory pool implementation
│       └── nvme_vio_cuda_gpu.cpp       - GPU buffer management & queue setup
└── test/              - Test files
    ├── helper/                          - Test helper implementations (used by tests)
    │   ├── dbc_setup.cpp                   - DBC setup test helper
    │   └── gpu_shadow_doorbell.cu          - Shadow doorbell test kernel
    ├── integration/
    │   ├── test_dbc_integration.cu         - DBC integration test
    │   ├── test_read_write_verify.cu       - End-to-end GPU I/O test
    │   └── test_gpu_doorbell_write.cu      - Doorbell write test
    └── unit/
        ├── host/
        │   ├── test_dbc_setup.cpp           - DBC setup unit tests
        │   └── test_gpu_p2p_ioctl.cpp       - P2P IOCTL tests
        └── kernels/
            └── test_cuda_io_gpu_mem.cpp     - GPU memory tests
```

## Quick Setup

**Requirements**: NVIDIA GPU with CUDA support, NVMe device bound to VFIO

```bash
# 1. Setup VFIO environment (uses Module 53's script)
cd ../53.NVMe_VFIO_Host_Layer/scripts
sudo ./setup_vfio.sh

# 2. Build Module 55.0
cd ../../../build
ninja

# 3. Run integration tests
export NVME_BDF="0000:XX:00.0"  # Your NVMe device
export NVME_NSID=1
./50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.0_Shared_Implementation/test/test_55_read_write_verify
```

Test executables are built to `build/50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.0_Shared_Implementation/test/`.

## Quick Navigation
- [55.0.1 Template API Architecture](#5501-template-api-architecture)
- [55.0.2 Shared Headers](#5502-shared-headers)
- [55.0.3 GPU Memory Buffer Pools](#5503-gpu-memory-buffer-pools)
- [55.0.4 Module Inheritance Pattern](#5504-module-inheritance-pattern)
- [Build & Test](#build--test)
- [55.0.5 Summary](#5505-summary)

---

## **55.0.1 Template API Architecture**

Module 55.0 introduces template-based submit and poll APIs matching the pattern established in Modules 53 and 54, enabling compile-time dispatch for optimal GPU performance.

### **55.0.1.1 Template Submit API**

The `gpu_submit<>` template provides compile-time command and doorbell type selection.

```cpp
// src/common/cuda_io_gpu_mem.h - Template submit API
template<CommandType cmd, DoorbellType doorbell>
inline std::uint16_t gpu_submit(Queue* iosq, std::uint32_t nsid,
                                std::uint64_t slba, std::uint32_t lba_size,
                                std::size_t bytes,
                                std::uint64_t prp1, std::uint64_t prp2) {
    return gpu_submit_runtime(cmd, doorbell, iosq, nsid, slba, lba_size, bytes, prp1, prp2);
}
```

**Usage Example:**
```cpp
// Compile-time command selection (READ or WRITE)
auto cid = gpu_submit<CMD_READ, DOORBELL_MMIO>(iosq, nsid, slba, lba_size,
                                                 buffer_bytes, prp1, prp2);
```

**Key Benefits:**
- Compile-time type safety
- Compiler can optimize away runtime branches
- Consistent with Module 53 (host_submit<>) and Module 54 (cuda_host_submit<>)

### **55.0.1.2 Template Poll API**

The `gpu_poll_completion<>` template provides compile-time async type selection.

```cpp
// src/common/cuda_io_gpu_mem.h - Template poll API
template<AsyncType async_type>
inline NvmeStatus gpu_poll_completion(Queue* iocq, std::uint16_t* out_cid,
                                       PollResult* out_poll_result = nullptr,
                                       std::uint32_t timeout_us = 0) {
    return host_poll_completion_runtime(async_type, iocq, out_cid, out_poll_result, timeout_us);
}
```

**Usage Example:**
```cpp
// Compile-time async mode selection (SYNC or ASYNC)
NvmeStatus status = gpu_poll_completion<ASYNC_TYPE_SYNC>(iocq, &cid);
```

**Note**: Currently reuses `host_poll_completion_runtime()` from Module 53 since completion polling logic is identical.

### **55.0.1.3 Runtime APIs**

Runtime versions support dynamic dispatch when command/doorbell types are not known at compile time.

```cpp
// Runtime submit - dynamic command and doorbell selection
std::uint16_t gpu_submit_runtime(CommandType cmd, DoorbellType doorbell,
                                   Queue* iosq, std::uint32_t nsid,
                                   std::uint64_t slba, std::uint32_t lba_size,
                                   std::size_t bytes,
                                   std::uint64_t prp1, std::uint64_t prp2);
```

---

## **55.0.2 Shared Headers**

Module 55.0 owns and exports three critical headers used by all child modules (55.1-55.3) and Module 56.

### **55.0.2.1 nvme_gpu_queue.h - GPU Queue Descriptor**

Uses the unified `NvmeQueue` structure (defined in Module 53's `nvme_queue.h`) for both host and GPU queue operations.

```cpp
// From ../../../53.NVMe_VFIO_Host_Layer/src/common/nvme_queue.h
struct NvmeQueue {
    // Virtual addresses (used by host userspace and GPU kernels)
    NvmeCmd*   sq_base;              // Virtual address of SQ (host or GPU)
    NvmeCqe*   cq_base;              // Virtual address of CQ (host or GPU)

    // IOVA addresses (used by VFIO for DMA mapping, NULL for GPU-only queues)
    void* sq_addr;                   // Submission Queue IOVA address
    void* cq_addr;                   // Completion Queue IOVA address

    // Doorbell addresses (for GPU direct access, NULL for host-managed queues)
    volatile std::uint32_t* sq_doorbell; // SQ doorbell (mode-dependent)
    volatile std::uint32_t* cq_doorbell; // CQ doorbell (mode-dependent)

    // Queue parameters
    std::uint16_t sq_depth;          // SQ depth (entries)
    std::uint16_t cq_depth;          // CQ depth (entries)
    std::uint16_t qid;               // Queue ID

    // Phase tracking
    std::uint8_t  sq_phase;          // Current SQ phase bit
    std::uint8_t  cq_phase;          // Current CQ phase bit

    // Doorbell mode (for GPU queues, ignored for host-only)
    std::uint8_t  doorbell_mode;     // Doorbell mode (DOORBELL_MODE_*)
    std::uint8_t  padding;           // Padding for alignment

    // Queue indices (use unsigned int for atomic operations on GPU)
    unsigned int  sq_tail;           // SQ tail index (use atomics in GPU code)
    unsigned int  cq_head;           // CQ head index (use atomics in GPU code)
};
```

**Doorbell Modes** (defined in this header):
- `DOORBELL_MODE_HOST_MMIO` (55.1): Host daemon monitors SQ tail and issues MMIO doorbells
- `DOORBELL_MODE_HOST_DBC`: Host queue backed by NVMe Doorbell Buffer Config (new)
- `DOORBELL_MODE_HOST_DBC_DAEMON`: Host queue with DBC shadow buffer mirrored by a daemon
- `DOORBELL_MODE_GPU_DBC` (55.2): NVMe controller polls the DBC shadow buffer written by the GPU
- `DOORBELL_MODE_GPU_DBC_DAEMON` (55.3): GPU updates shadow buffer, host daemon mirrors to MMIO
- `DOORBELL_MODE_GPU_MMIO` (56): GPU writes MMIO doorbells directly

**Device-side helper functions** (available in CUDA compilation):
```cpp
__device__ inline std::uint16_t nvme_gpu_alloc_sq_slot(NvmeQueue* q, std::uint16_t* out_cid);
__device__ inline void nvme_gpu_write_sq_command(...);
__device__ inline void nvme_gpu_ring_sq_doorbell(NvmeQueue* q);
__device__ inline bool nvme_gpu_poll_cq(NvmeQueue* q, std::uint16_t cid, NvmeStatus* out_status);
```

### **55.0.2.2 gpu_p2p_ioctl.h - P2P IOCTL Interface**

Defines IOCTL interface for GPU P2P memory mapping (used with kernel module).

```cpp
// src/common/gpu_p2p_ioctl.h - IOCTL definitions
#define GPU_P2P_MAP_BUFFER   _IOWR('G', 1, struct gpu_p2p_map_req)
#define GPU_P2P_UNMAP_BUFFER _IOW('G',  2, struct gpu_p2p_unmap_req)

struct gpu_p2p_map_req {
    uint64_t gpu_va;        // GPU virtual address
    uint64_t size;          // Buffer size
    uint64_t iova;          // Output: DMA address for NVMe
    uint64_t page_token;    // Output: Mapping token
};
```

### **55.0.2.3 nvme_vio_cuda_gpu.h - GPU Queue Setup**

Defines CUDA GPU integration API including buffer management and queue setup.

```cpp
// src/common/nvme_vio_cuda_gpu.h
// Create CUDA device buffer for NVMe DMA
Buffer* nvme_gpu_create_cuda_pinned_consecutive_buffer(std::size_t buffer_size);

// Query P2P tokens for GPUDirect RDMA
int nvme_cuda_query_p2p_tokens(const void* device_ptr, CudaP2PTokens* out_tokens);

// Setup GPU queue for NVMe submission
int nvme_setup_gpu_queue(NvmeDevice* nvme_dev, const char* nvme_bdf, NvmeQueue* out_gpu_queue);
```

**Why Module 55.0 Owns These Headers:**

1. **Single Source of Truth**: All modules inherit from 55.0, ensuring consistency
2. **CMake Dependency Management**: Child modules link to `cuda_io_gpu_mem_55` library
3. **No Header Duplication**: Module 56 previously had copies - now removed in refactoring

**CMake Inheritance Pattern:**
```cmake
# Module 56 CMakeLists.txt
target_link_libraries(${MODULE}_lib PUBLIC
    cuda_io_gpu_mem_55          # Automatically includes 55.0/src/common/
    nvme_vio_cuda_gpu_55        # Automatically includes 55.0/src/common/
)
```

---

## **55.0.3 GPU Memory Buffer Pools**

Module 55.0 provides GPU device memory buffer pool management for NVMe DMA transfers.

### **55.0.3.1 Buffer Pool API**

```cpp
// GPU buffer pool allocation (currently requires P2P kernel module)
CudaGpuPool* cuda_gpu_pool_create(NvmeDevice* dev, size_t buffer_size,
                                   size_t num_buffers);
void cuda_gpu_pool_destroy(CudaGpuPool* pool);

GpuDmaBuf* cuda_gpu_pool_acquire(CudaGpuPool* pool);
void cuda_gpu_pool_release(CudaGpuPool* pool, GpuDmaBuf* buf);
```

**Note**: Pool API requires GPU P2P kernel module to map GPU device memory for NVMe DMA. Integration tests use CUDA host pinned memory as staging area (Module 54 pattern).

### **55.0.3.2 Internal Implementation Details**

**File**: `src/kernels/cuda_io_gpu_mem.cpp`

**Internal functions** (not exposed in public API):
- `build_prps_for_gpu()`: Constructs PRP (Physical Region Page) lists for GPU buffers
- Buffer pool management internals

**Moved to implementation file** (refactoring 2025-10-25):
- Previously exposed in header - now properly encapsulated
- Tests updated to use public API only

---

## **55.0.4 Module Inheritance Pattern**

How child modules inherit from Module 55.0:

### **Inheritance via CMake Libraries**

Module 55.0 exports two libraries:
1. `cuda_io_gpu_mem_55`: GPU memory and template/runtime APIs
2. `nvme_vio_cuda_gpu_55`: NVMe VFIO GPU integration

**Export Pattern:**
```cmake
# Module 55.0 src/CMakeLists.txt
add_library(cuda_io_gpu_mem_55 STATIC
    kernels/cuda_io_gpu_mem.cpp
    host/dbc_setup.cpp
    # ...
)

# Export src/ as INTERFACE so child modules can include headers
target_include_directories(cuda_io_gpu_mem_55
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows #include "common/nvme_gpu_queue.h"
)
```

**Child Module Usage:**
```cmake
# Module 56 CMakeLists.txt
target_link_libraries(${MODULE}_lib PUBLIC
    cuda_io_gpu_mem_55          # Gets template APIs + headers
    nvme_vio_cuda_gpu_55        # Gets VFIO GPU integration
)
```

### **API Inheritance Matrix**

| Feature | Module 55.0 | Module 56 | How Inherited |
|---------|-------------|-----------|---------------|
| `gpu_submit<>` template | ✅ Defined | ✅ Inherited | Links to `cuda_io_gpu_mem_55` |
| `gpu_poll_completion<>` template | ✅ Defined | ✅ Inherited | Links to `cuda_io_gpu_mem_55` |
| `gpu_submit_runtime()` | ✅ Defined | ✅ Inherited | Links to `cuda_io_gpu_mem_55` |
| `nvme_gpu_queue.h` | ✅ Owns | ✅ Inherited | INTERFACE include from 55.0 |
| `gpu_p2p_ioctl.h` | ✅ Owns | ✅ Inherited | INTERFACE include from 55.0 |
| Doorbell abstraction | ❌ None | ✅ Adds | Module 56-specific feature |

---

## Build & Test

### Build Instructions

```bash
# From project root
cd build
ninja

# Build specific target
ninja cuda_io_gpu_mem_55
ninja test_55_read_write_verify
```

### Run Tests

```bash
# Set test environment (replace with your NVMe device)
export NVME_BDF="0000:41:00.0"
export NVME_NSID=1
export NVME_LBA_SIZE=512
export NVME_SLBA=2000000
export NVME_LBAS=16

# Run integration tests
./50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.0_Shared_Implementation/test/test_55_read_write_verify

# Run unit tests
./50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.0_Shared_Implementation/test/test_cuda_io_gpu_mem_55
./50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.0_Shared_Implementation/test/test_gpu_p2p_ioctl_55
```

### Test Coverage

**Integration Tests** (`test/integration/`):
- `test_read_write_verify.cu`: Full GPU → NVMe → GPU round-trip with pattern verification
- `test_dbc_integration.cu`: DBC (Doorbell Buffer Config) integration test
- `test_gpu_doorbell_write.cu`: GPU doorbell ring validation

**Unit Tests** (`test/unit/`):
- `test_cuda_io_gpu_mem.cpp`: GPU memory pool API tests (requires P2P module)
- `test_gpu_p2p_ioctl.cpp`: P2P IOCTL interface tests
- `test_dbc_setup.cpp`: DBC setup function tests

**Hardware Test Results** (2025-10-25):
- ✅ Integration: 2/2 tests passed (RTX A6000 + Samsung NVMe)
- ⏭️ Unit: 1 skipped (requires P2P kernel module)

---

## **55.0.5 Summary**

### **Key Achievements**

1. **Template API Foundation**: Introduced `gpu_submit<>` and `gpu_poll_completion<>` matching Module 53/54 pattern
2. **Shared Header Ownership**: Established Module 55.0 as canonical source for `nvme_gpu_queue.h`, `gpu_p2p_ioctl.h`, `nvme_vio_cuda_gpu.h`
3. **CMake Inheritance Pattern**: Child modules inherit APIs and headers via library dependencies
4. **Proper Encapsulation**: Internal functions moved from headers to implementation files

### **Module Dependencies**

**Modules that inherit from 55.0:**
- **55.1**: Host Daemon Doorbell (conceptual - not implemented)
- **55.2**: DBC Shadow Doorbell (partial implementation)
- **55.3**: Host DBC Daemon (conceptual - not recommended)
- **56**: GPU Queue GPU Buffer (full implementation - adds doorbell abstraction)

### **API Consistency Across Modules**

| Module | Submit Template | Poll Template | Runtime Submit | Runtime Poll |
|--------|----------------|---------------|----------------|--------------|
| 53 (Host) | `host_submit<>` | `host_poll_completion<>` | `host_submit_runtime()` | `host_poll_completion_runtime()` |
| 54 (CUDA Host) | `cuda_host_submit<>` | `cuda_host_poll_completion<>` | `cuda_host_submit_runtime()` | `cuda_host_poll_completion_runtime()` |
| 55.0 (GPU) | `gpu_submit<>` ⭐ | `gpu_poll_completion<>` ⭐ | `gpu_submit_runtime()` | Reuses `host_poll_completion_runtime()` |
| 56 (Complete) | Inherits from 55.0 | Inherits from 55.0 | Inherits from 55.0 | Inherits from 55.0 |

### **Performance Modes** (from Module 55.4)

Module 55.0 shared implementation supports all doorbell modes:
- **Mode #1**: Host queue + Host buffer (90-140µs latency) - Module 54
- **Mode #3**: GPU queue + Host buffer (130-160µs latency) - Not recommended
- **Mode #5**: DBC shadow + Host buffer (70-90µs latency) - Best performance

### **Next Steps**

- **For GPU-initiated I/O**: Use **Module 53** (unified implementation with comprehensive Mode 0-5 support)
- **For performance testing**: See [Module 53 Section 53.8](../../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing) for complete benchmarks
- **For Mode 2-4 concepts**: Read this module for educational understanding of different doorbell approaches
- **For production use**: Module 53 provides the production-ready implementation

### **References**

- **Module 53**: [NVMe VFIO Host Layer](../../53.NVMe_VFIO_Host_Layer/README.md) - **PRIMARY IMPLEMENTATION** with unified Mode 0-5 support
- **Module 53.8**: [Performance Testing](../../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing) - Comprehensive benchmarks for all modes
- **Module 54**: CUDA Host Memory (Mode 1 concepts)
- **Module 56**: GPU Queue GPU Buffer (legacy implementation, see Module 53 for current)
- **REFACTORING_PLAN.md**: Details of 2025-10-25 refactoring (template APIs, header deduplication)
