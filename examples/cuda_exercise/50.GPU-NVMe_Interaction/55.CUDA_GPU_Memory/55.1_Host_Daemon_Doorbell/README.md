# 🎯 Part 55.1: Host Daemon Doorbell (Mode 2)

**Goal**: Enable GPU-initiated NVMe I/O with GPU buffers using a host daemon for doorbell writes. Works on all consumer hardware without requiring GPU-to-MMIO doorbell mapping.

**Architecture**: IO Queue on **GPU** | Buffer in **GPU Memory** | Doorbell via **Host Daemon**

**Implementation Status**: This module provides **conceptual documentation** for Mode 2 (Host Daemon with GPU memory polling). The **production implementation** is now consolidated in [Module 53](../../53.NVMe_VFIO_Host_Layer/README.md) as part of the unified Mode 0-5 architecture.

**For Performance Testing**: See [Module 53 Section 53.8](../../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing) which includes Mode 2 benchmarks and comparison with other modes.

## Project Structure

```
55.1_Host_Daemon_Doorbell/
├── README.md                  - This documentation
├── CMakeLists.txt             - Build configuration
├── daemon/                    - Host doorbell daemon
│   ├── doorbell_daemon.cpp    - Daemon implementation
│   └── CMakeLists.txt         - Daemon build config
├── driver/                    - Kernel module for GPU P2P mapping
│   ├── src/
│   │   ├── gpu_g2p_map_module.c           - Core driver
│   │   ├── gpu_p2p_backend_nv.c           - NVIDIA P2P backend
│   │   └── gpu_p2p_nvme_queue_mapping.c   - Queue mapping
│   ├── Makefile               - kbuild Makefile
│   └── README.md              - Driver documentation
├── src/                       - Source implementations
│   ├── common/                - Shared utilities
│   │   ├── cuda_io_gpu_mem.h/cpp          - PRP construction
│   │   ├── nvme_vio_cuda_gpu.h/cpp        - GPU buffer management
│   │   └── nvme_gpu_submit_setup.cpp      - Queue setup
│   └── kernels/               - CUDA kernel implementations
│       ├── cuda_io_gpu_mem.cpp            - GPU memory operations
│       └── nvme_vio_cuda_gpu.cpp          - NVMe I/O kernels
├── include/                   - Public headers
│   ├── nvme_gpu_queue.h       - GPU queue API (NO doorbell ringing)
│   ├── nvme_gpu_submit_setup.h
│   └── gpu_p2p_ioctl.h        - IOCTL interface
└── test/                      - Test files
    ├── unit/                  - Unit tests (no hardware)
    │   ├── common/test_cuda_io_gpu_mem.cpp
    │   ├── host/test_gpu_p2p_ioctl.cpp
    │   └── part_specific/test_nvme_vio_cuda_gpu_buffer.cpp
    └── integration/           - Integration tests (requires hardware)
        └── test_daemon_assisted_io.cu - Full workflow test
```

## Quick Navigation

- [55.1.1 Architecture Overview](#5511-architecture-overview)
- [55.1.2 Why GPU Cannot Ring Doorbells Directly](#5512-why-gpu-cannot-ring-doorbells-directly)
- [55.1.3 Doorbell Daemon](#5513-doorbell-daemon)
- [55.1.4 GPU Queue Operations](#5514-gpu-queue-operations)
- [55.1.5 GPU P2P Memory Mapping](#5515-gpu-p2p-memory-mapping)
- [55.1.6 Build & Run](#5516-build--run)
- [55.1.7 Testing](#5517-testing)
- [55.1.8 Summary](#5518-summary)

---

## **55.1.1 Architecture Overview**

This module demonstrates GPU-initiated NVMe I/O using a **host daemon** to ring NVMe doorbells on behalf of GPU kernels. This approach works on all consumer hardware without requiring specialized GPU-to-MMIO doorbell mapping.

### **Architecture Diagram**

```
┌─────────────────────────────────────────────────────────────────┐
│                         GPU Device                               │
│                                                                   │
│  ┌──────────────┐                                                │
│  │ GPU Kernel   │                                                │
│  │              │                                                │
│  │ 1. Alloc SQ  │──┐                                             │
│  │    slot      │  │                                             │
│  │ 2. Write cmd │  │                                             │
│  │ 3. Update    │  │                                             │
│  │    sq_tail   │  │ atomicAdd(&queue.sq_tail, 1)                │
│  └──────────────┘  │                                             │
│                    ▼                                             │
│  ┌──────────────────────────────────┐                           │
│  │ Submission Queue (SQ) in GPU VRAM│◄──────┐                   │
│  │                                  │       │                   │
│  │ - NvmeCmd entries                │       │ Polls             │
│  │ - sq_tail (atomic counter)       │───────┘                   │
│  └──────────────────────────────────┘                           │
│                                                                   │
│  ┌──────────────────────────────────┐                           │
│  │ Completion Queue (CQ) in GPU VRAM│                           │
│  │                                  │                           │
│  │ - NvmeCqe entries                │                           │
│  │ - cq_head (atomic counter)       │                           │
│  └──────────────────────────────────┘                           │
│                    ▲                                             │
│                    │                                             │
│  ┌──────────────┐  │                                             │
│  │ GPU Kernel   │  │                                             │
│  │              │  │                                             │
│  │ 5. Poll CQ   │──┘                                             │
│  │ 6. Process   │                                                │
│  │    data      │                                                │
│  └──────────────┘                                                │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
                    ▲                           ▲
                    │                           │
                    │ P2P DMA                   │ Polls sq_tail
                    │                           │ (via mapped GPU mem)
                    │                           │
        ┌───────────┴───────────┐   ┌──────────┴──────────┐
        │   NVMe Controller     │   │  Host Daemon        │
        │                       │   │                     │
        │ - Reads SQ (via P2P)  │   │ - Polls sq_tail     │
        │ - Writes CQ (via P2P) │   │ - Rings doorbells   │
        │ - Waits for doorbell  │◄──┤   (MMIO write)      │
        │                       │   │                     │
        └───────────────────────┘   └─────────────────────┘
```

### **Data Flow**

1. **GPU Kernel → SQ**: GPU kernel allocates SQ slot via `atomicAdd(&queue.sq_tail, 1)`
2. **GPU Kernel → SQ**: GPU kernel writes NVMe command to SQ entry
3. **GPU Kernel → sq_tail**: GPU kernel updates sq_tail (atomic increment)
4. **Host Daemon → sq_tail**: Daemon polls sq_tail (mapped GPU memory)
5. **Host Daemon → NVMe**: Daemon detects change, writes NVMe doorbell register (MMIO)
6. **NVMe → SQ**: Controller reads commands from SQ (P2P DMA from GPU)
7. **NVMe → CQ**: Controller writes completions to CQ (P2P DMA to GPU)
8. **GPU Kernel → CQ**: GPU kernel polls CQ for completion

### **Key Innovation**

**Problem**: GPU cannot directly write to NVMe doorbell MMIO registers on consumer hardware.

**Solution**: Host daemon acts as a "doorbell proxy":
- GPU updates `sq_tail` in GPU memory (visible to host via P2P mapping)
- Daemon polls `sq_tail` with low latency (~10µs)
- Daemon performs MMIO doorbell write on GPU's behalf
- NVMe controller sees doorbell write and processes commands

---

## **55.1.2 Why GPU Cannot Ring Doorbells Directly**

NVMe doorbell registers reside in the NVMe controller's **PCIe Base Address Register (BAR) space**, which is mapped as **MMIO (Memory-Mapped I/O)** at specific physical addresses.

### **NVMe Doorbell Register Location (NVMe Spec 1.4, Section 3.1.10)**

Doorbell registers are located in **BAR0** at fixed offsets:
- **SQ Tail Doorbell** (queue y): Offset `0x1000 + (2y × (4 << CAP.DSTRD))`
- **CQ Head Doorbell** (queue y): Offset `0x1000 + ((2y+1) × (4 << CAP.DSTRD))`

Where `CAP.DSTRD` (Doorbell Stride) is read from NVMe Controller Capabilities register.

### **Why GPU Cannot Access NVMe Doorbells (PCIe P2P Limitations)**

**Problem 1: Physical Address Constraints**

PCIe peer-to-peer (P2P) access requires that the target BAR's physical address is within the source device's addressing capability:

- **AMD GFX8 GPUs**: Can only access BARs below 2⁴⁰ (1 TB)
- **AMD GFX9 (Vega) GPUs**: Can only access BARs below 2⁴⁴ (16 TB)
- **NVIDIA GPUs**: Similar limitations based on GPU generation

If the NVMe doorbell BAR exceeds the GPU's physical addressing limit, **the GPU cannot access it**.

**Problem 2: System Topology Constraints**

Even when addresses are compatible, PCIe P2P requires:
- Both devices on same PCIe root complex
- BIOS/chipset support for 64-bit I/O memory space
- No address translation or security restrictions (IOMMU/ACS)

Many consumer systems lack proper P2P support for doorbell registers.

**Problem 3: Linux Kernel Limitations**

The Linux kernel's P2P DMA framework (`pci/p2pdma.c`) currently supports:
- ✅ P2P memory (device RAM, like GPU VRAM)
- ❌ Doorbell registers (MMIO-mapped control registers)

**Quote from kernel documentation**:
> "For the time being P2P resources are typically going to be P2P memory, and future work will likely expand this to include other types of resources like doorbells."

**Conclusion**: GPU-to-NVMe doorbell writes are **not universally supported** on consumer hardware, necessitating the daemon approach.

### **NVMe Doorbell BAR Structure**

```
NVMe BAR0 (MMIO Space):
┌──────────────────────────────────────────┐
│ 0x0000 - 0x0FFF: Controller Registers    │
│   - CAP (Capabilities)                   │
│   - VS (Version)                         │
│   - CC (Configuration)                   │
│   - CSTS (Status)                        │
│   - AQA (Admin Queue Attributes)         │
│   - ASQ (Admin SQ Base Address)          │
│   - ACQ (Admin CQ Base Address)          │
│                                           │
│ 0x1000+: I/O Queue Doorbells             │
│   - SQ0 Tail (Admin): 0x1000             │
│   - CQ0 Head (Admin): 0x1000 + (4<<DSTRD)│
│   - SQ1 Tail (I/O):   0x1000 + 2×(4<<DSTRD)│
│   - CQ1 Head (I/O):   0x1000 + 3×(4<<DSTRD)│
│   - ...                                  │
│                                           │
│ (Each doorbell is 4 bytes, typically     │
│  stride=0 means consecutive 4B writes)   │
└──────────────────────────────────────────┘

❌ GPU cannot write here directly (P2P limitations)
✅ Host CPU can write here (VFIO/UIO mapping)
```

### **Solution: Host Daemon as Doorbell Proxy**

Since GPU → NVMe doorbell writes are blocked, we use:
1. GPU writes `sq_tail` counter in **GPU memory** (visible via P2P mapping)
2. Host daemon polls `sq_tail` (mapped to host address space)
3. Daemon writes NVMe doorbell **MMIO register** on GPU's behalf

This works because:
- ✅ GPU → GPU memory: Always works (local writes)
- ✅ Host → GPU memory: Works via CUDA host mapping
- ✅ Host → NVMe doorbell: Works via VFIO/UIO BAR mapping

---

## **55.1.3 Doorbell Daemon**

The doorbell daemon is a lightweight host process that monitors GPU queue state and rings NVMe doorbells.

### **Implementation**

Source: `daemon/doorbell_daemon.cpp`

```cpp
class DoorbellDaemon {
private:
    volatile uint32_t* sq_tail_gpu;   // Mapped GPU memory
    uint32_t sq_tail_shadow;          // Last known value
    volatile uint32_t* sq_doorbell;   // NVMe doorbell (MMIO)

public:
    void poll_loop() {
        while (running) {
            uint32_t current_tail = *sq_tail_gpu;  // Read GPU memory

            if (current_tail != sq_tail_shadow) {
                // New commands detected!
                uint16_t wrapped_tail = current_tail % sq_depth;
                ring_sq_doorbell(wrapped_tail);  // MMIO write
                sq_tail_shadow = current_tail;
            }

            std::this_thread::sleep_for(
                std::chrono::microseconds(poll_interval_us)
            );
        }
    }

    void ring_sq_doorbell(uint16_t new_tail) {
        *sq_doorbell = new_tail;  // MMIO write to NVMe controller
        __sync_synchronize();     // Memory barrier
    }
};
```

### **Polling Strategy**

**Configurable Polling Interval**:
- **10µs**: Low latency mode (99th percentile: ~20µs)
- **50µs**: Balanced mode (99th percentile: ~80µs)
- **100µs**: Low CPU mode (99th percentile: ~150µs)

**Trade-offs**:
| Interval | Latency (p99) | CPU Usage | Use Case |
|----------|---------------|-----------|----------|
| 10µs     | ~20µs         | ~10%      | Latency-critical (interactive) |
| 50µs     | ~80µs         | ~2%       | Balanced (general purpose) |
| 100µs    | ~150µs        | ~1%       | Throughput-focused (batch) |

### **Memory Mapping**

**Mapping GPU Memory to Host**:

```cpp
// In GPU kernel setup (host side)
cudaMalloc(&d_queue, sizeof(NvmeQueue));
cudaHostRegister(&d_queue->sq_tail, sizeof(uint32_t), cudaHostRegisterMapped);

// Get host pointer to GPU memory
uint32_t* h_sq_tail;
cudaHostGetDevicePointer(&h_sq_tail, &d_queue->sq_tail, 0);

// Pass to daemon
daemon.initialize(nvme_bdf, qid, h_sq_tail, sq_depth);
```

**Mapping NVMe Doorbells (via VFIO)**:

```cpp
// Open VFIO device
int nvme_fd = open("/dev/vfio/X", O_RDWR);

// Map BAR0 (contains doorbell registers)
void* bar0 = mmap(NULL, bar0_size, PROT_READ | PROT_WRITE,
                   MAP_SHARED, nvme_fd, 0);

// Calculate doorbell offset (NVMe spec 1.4 section 3.1.10)
uint32_t dstrd = 0;  // From CAP.DSTRD
uint32_t sq_db_offset = 0x1000 + (2 * qid * (4 << dstrd));

volatile uint32_t* sq_doorbell = (volatile uint32_t*)
    ((char*)bar0 + sq_db_offset);
```

---

## **55.1.4 GPU Queue Operations**

GPU kernels interact with NVMe queues without directly ringing doorbells.

### **Modified Queue API**

Source: `include/nvme_gpu_queue.h`

**Key Difference from Module 55/56**: `nvme_gpu_ring_sq_doorbell()` is a **NO-OP** in 55.1.

```cpp
// NO-OP: Host daemon rings doorbells instead
__device__ inline void nvme_gpu_ring_sq_doorbell(NvmeQueue* q) {
    // The atomicAdd() in nvme_gpu_alloc_sq_slot() already updated sq_tail
    // The daemon polls sq_tail and performs the actual MMIO doorbell write
    __threadfence_system();  // Ensure writes are visible to host
}
```

### **GPU Kernel Example**

```cuda
__global__ void submit_read_kernel(NvmeQueue* queue,
                                    uint64_t lba,
                                    void* gpu_buffer) {
    // 1. Allocate SQ slot (atomically increments sq_tail)
    uint16_t cid;
    uint16_t slot = nvme_gpu_alloc_sq_slot(queue, &cid);

    // 2. Write NVMe read command
    nvme_gpu_write_sq_command(queue, slot, OPC_NVM_READ,
                               1, gpu_buffer, 0, lba, 1, cid);

    // 3. Ring doorbell (NO-OP in 55.1 - daemon handles this)
    nvme_gpu_ring_sq_doorbell(queue);

    // At this point:
    // - sq_tail has been incremented
    // - Daemon will detect change within ~10-50µs
    // - Daemon will ring MMIO doorbell
    // - NVMe will process command

    // 4. Poll CQ for completion
    NvmeStatus status;
    while (!nvme_gpu_poll_cq(queue, cid, &status)) {
        // Busy wait (or sleep)
    }

    // 5. Data is now in gpu_buffer
}
```

---

## **55.1.5 GPU P2P Memory Mapping**

This module uses the same GPU P2P queue mapping as Module 55, but does **NOT** map doorbells to GPU.

### **IOCTL Interface**

Source: `include/gpu_p2p_ioctl.h`

```c
struct gpu_p2p_nvme_queue_req {
    uint64_t p2p_token;       // From cuPointerGetAttribute
    uint64_t va_space;        // CUDA VA space
    uint64_t nvme_pci_bdf;    // NVMe device BDF
    uint64_t gpu_va;          // GPU virtual address of queue
    uint64_t bytes;           // Queue size
    uint64_t gpu_va_out;      // GPU-accessible address (output)
};

#define GPU_P2P_MAP_NVME_QUEUES _IOWR('G', 0xE1, struct gpu_p2p_nvme_queue_req)
```

**Note**: No `GPU_P2P_MAP_NVME_DOORBELLS` IOCTL in 55.1 (doorbells stay in MMIO space).

### **Driver Implementation**

Source: `driver/src/gpu_p2p_nvme_queue_mapping.c`

```c
int gpu_p2p_map_nvme_queues(struct gpu_p2p_nvme_queue_req* req) {
    // 1. Get GPU pages via nvidia_p2p_get_pages()
    nvidia_p2p_get_pages(req->p2p_token, req->va_space,
                         req->gpu_va, req->bytes, &page_table, ...);

    // 2. Map GPU pages for NVMe DMA
    nvidia_p2p_dma_map_pages(nvme_pci_dev, page_table, &dma_mapping);

    // 3. Return GPU-accessible addresses
    req->gpu_va_out = dma_mapping->entries[0].physical_address;

    return 0;
}
```

---

## **55.1.6 Build & Run**

### **Build**

```bash
cd /home/ormastes/dev/pub/cuda_exercise
rm -rf build && cmake -B build -G Ninja
ninja -C build

# Build kernel module
cd 50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.1_Host_Daemon_Doorbell/driver
make

# Load kernel modules
sudo insmod gpu_g2p_map_module_backend_nv.ko
sudo insmod gpu_g2p_map_module.ko
```

### **Run Daemon (Standalone)**

```bash
cd build/50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.1_Host_Daemon_Doorbell/daemon

# Standalone mode (simulates GPU updates)
./doorbell_daemon /dev/vfio/X 1

# Output:
# [DoorbellDaemon] Initialized for queue 1 (depth=64)
# [DoorbellDaemon] Monitoring GPU sq_tail at 0x7f1234567890
# [DoorbellDaemon] Poll interval: 10 us
# [DoorbellDaemon] Started polling thread
# Simulating GPU command submissions...
# GPU submitted command 1 (sq_tail=1)
# [DoorbellDaemon] MOCK: Would ring SQ doorbell with tail=1
# ...
```

### **Environment Variables**

```bash
export NVME_BDF="0000:41:00.0"   # NVMe device PCIe address
export NVME_NSID="1"             # Namespace ID
export NVME_LBA_SIZE="512"       # LBA size in bytes
export NVME_SLBA="1000000"       # Starting LBA for tests
```

---

## **55.1.7 Testing**

### **Unit Tests**

No hardware required - test logic and data structures.

```bash
# Run all unit tests
cd build
ctest -R "55_1.*test_.*" --output-on-failure

# Individual tests
./50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.1_Host_Daemon_Doorbell/test/unit/test_cuda_io_gpu_mem
./50.GPU-NVMe_Interaction/55.CUDA_GPU_Memory/55.1_Host_Daemon_Doorbell/test/unit/test_gpu_p2p_ioctl
```

**Coverage**:
- PRP list construction (single, multi-segment)
- GPU buffer allocation
- IOCTL request validation
- Queue structure initialization

### **Integration Tests**

Requires NVMe hardware + VFIO setup.

**Prerequisites**:
1. NVMe device bound to vfio-pci
2. Kernel modules loaded
3. Environment variables set
4. Root privileges

**Test**: `test/integration/test_daemon_assisted_io.cu`

```bash
sudo -E ./test/integration/test_daemon_assisted_io

# Workflow:
# 1. Setup GPU queue in GPU memory
# 2. Map queue for NVMe DMA (IOCTL)
# 3. Start doorbell daemon
# 4. Launch GPU kernel to submit read command
# 5. Daemon detects sq_tail change, rings doorbell
# 6. NVMe reads SQ, DMAs data to GPU buffer, writes CQ
# 7. GPU kernel polls CQ, validates data
# 8. Stop daemon
```

**Expected Output**:
```
[  RUN   ] DaemonAssistedIO.ReadWriteVerify
[DoorbellDaemon] Started polling thread
[GPU] Submitted read command (lba=1000000, cid=0)
[DoorbellDaemon] Rang doorbell (tail=1)
[GPU] CQ entry received (cid=0, status=SUCCESS)
[GPU] Data validation: PASS
[DoorbellDaemon] Stopped
[   OK  ] DaemonAssistedIO.ReadWriteVerify (42 ms)
```

---

## **55.1.8 Summary**

### **Key Takeaways**

1. **Universal Compatibility**: Works on all consumer hardware without GPU doorbell mapping
2. **Daemon Architecture**: Host process monitors GPU state and rings MMIO doorbells
3. **Low Overhead**: Configurable polling interval (10-100µs) balances latency vs CPU usage
4. **P2P Queues**: NVMe queues in GPU memory enable direct DMA to/from GPU buffers

### **Performance Metrics**

| Metric | Value | Notes |
|--------|-------|-------|
| **Command Latency** | 22-102µs | Depends on polling interval |
| **Polling Overhead** | 10-50µs | Daemon detects sq_tail change |
| **CPU Usage** | 1-10% | One daemon thread per queue |
| **Throughput** | ~40k IOPS | Batch multiple commands |

**Comparison to Module 55/56**:
- **Latency**: +10-50µs (daemon polling overhead)
- **Compatibility**: ✅ Better (no doorbell mapping required)
- **CPU Usage**: ✅ Higher (daemon thread)

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| Daemon not detecting commands | sq_tail not mapped to host | Use `cudaHostRegister()` for sq_tail |
| MMIO write fails | BAR0 not mapped | Check VFIO device mapping |
| High latency | Polling interval too large | Reduce to 10µs for low latency |
| High CPU usage | Polling interval too small | Increase to 50-100µs |

### **Next Steps**

- **For Production Use**: See [Module 53](../../53.NVMe_VFIO_Host_Layer/README.md) for the unified implementation supporting Modes 0-5
- **For Performance Data**: See [Module 53 Section 53.8](../../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing) for Mode 2 benchmarks
- 📚 Continue to [Part 55.2: DBC Shadow Doorbell](../55.2_DBC_Shadow_Doorbell/README.md) to understand Mode 3 concepts
- 📊 See [Part 55.4: Mode Comparison Guide](../55.4_Mode_Comparison_Guide/README.md) for comprehensive mode selection guidance

### **References**

- **Module 53**: [NVMe VFIO Host Layer](../../53.NVMe_VFIO_Host_Layer/README.md) - **PRIMARY IMPLEMENTATION** with Mode 0-5 support
- **Module 53.8**: [Performance Testing](../../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing) - Mode 2 benchmarks and comparisons
- [NVMe Specification 1.4](https://nvmexpress.org/specifications/) - Section 3.1.10 (Doorbells)
- [GPUDirect RDMA](https://docs.nvidia.com/cuda/gpudirect-rdma/) - P2P memory mapping
- [VFIO Documentation](https://www.kernel.org/doc/html/latest/driver-api/vfio.html) - User-space device access
- Module 55.2 (DBC Shadow Doorbell) - Mode 3 concepts
- Module 55.4 (Mode Comparison Guide) - Decision tree for mode selection
