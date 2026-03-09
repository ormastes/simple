# Performance Benchmark Setup Tasks Reference

This document lists all recommended setup tasks for comprehensive NVMe performance benchmarking, as would be needed for Module 57 (Performance Comparison GDS vs GPU) and similar benchmark suites.

---

## Currently Implemented Tasks

### ✅ NvmeSetupTask (Admin)
**Purpose**: Open NVMe device via VFIO and setup I/O queues
**Args**:
- `bdf` / `NVME_BDF`: PCI address (e.g., "0000:41:00.0")
- `sq_depth`: Submission queue depth (default: 16)
- `cq_depth`: Completion queue depth (default: 16)
- `lba_size` / `NVME_LBA_SIZE`: LBA size (default: 512)

**Results**:
- `nvme_device`: NvmeDevice*
- `iosq`: Queue* (I/O submission queue)
- `iocq`: Queue* (I/O completion queue)

**Usage**:
```cpp
helper.add_task(new NvmeSetupTask("0000:41:00.0", 32, 32, 512));
```

---

### ✅ HostMemoryFactoryTask (User)
**Purpose**: Create host pageable memory buffer pool
**Args**:
- `buf_size`: Buffer size in bytes (default: 4096)
- `count`: Number of buffers (default: 16)
- `nvme_device`: NvmeDevice* (from NvmeSetupTask)

**Results**:
- `host_pool`: HostPool*

**Usage**:
```cpp
helper.add_task(new HostMemoryFactoryTask(1048576, 16));  // 1MB x 16
```

---

### ✅ CudaHostMemoryFactoryTask (User)
**Purpose**: Create CUDA host-pinned memory buffer pool
**Args**: Same as HostMemoryFactoryTask
**Results**: `cuda_host_pool`: CudaHostPool*

---

### ✅ CudaGpuMemoryFactoryTask (User)
**Purpose**: Create CUDA GPU device memory buffer pool
**Args**: Same as HostMemoryFactoryTask
**Results**: `cuda_gpu_pool`: CudaGpuPool*

---

## Recommended Additional Tasks

### 🔧 Environment Detection Tasks

#### GpuDetectionTask (User)
**Purpose**: Detect and enumerate GPUs, check capabilities
**Args**:
- `min_compute_capability`: Minimum CUDA compute (default: "7.0")
- `require_p2p`: Require P2P support (default: true)

**Results**:
- `gpu_count`: int (number of GPUs)
- `gpu_info`: GpuFeatures[] (array of GPU capabilities)
- `selected_gpu_id`: int (auto-selected GPU for testing)

**Implementation Outline**:
```cpp
class GpuDetectionTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        cudaGetDeviceCount(&count);
        // Enumerate GPUs, check compute capability
        // Check P2P support via cudaDeviceCanAccessPeer()
        // Select best GPU
        return SetupResult("gpu_info", gpu_features);
    }
};
```

---

#### NvmeDetectionTask (User)
**Purpose**: Enumerate NVMe devices and check capabilities
**Args**:
- `min_capacity_gb`: Minimum capacity in GB (default: 10)
- `require_dbc`: Require doorbell buffer config support (default: false)

**Results**:
- `nvme_count`: int
- `nvme_devices`: NvmeDeviceInfo[]
- `selected_nvme_bdf`: string (auto-selected device)

**Implementation Outline**:
```cpp
class NvmeDetectionTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        // Parse /sys/bus/pci/devices/*/class for NVMe
        // For each device, check capacity, features
        // Select best device for testing
        return SetupResult("nvme_info", device_list);
    }
};
```

---

#### IommuCheckTask (User)
**Purpose**: Verify IOMMU is enabled and functional
**Args**: None
**Results**:
- `iommu_enabled`: bool
- `iommu_type`: string ("intel" or "amd")
- `vfio_available`: bool

**Implementation Outline**:
```cpp
class IommuCheckTask : public UserSetupTask {
    SetupResult setup(const SetupArgs&) override {
        // Check /proc/cmdline for iommu=on
        // Check /sys/kernel/iommu_groups/
        // Check for vfio-pci driver
        auto* result = new IommuStatus{enabled, type, vfio_ok};
        return SetupResult("iommu_status", result);
    }
};
```

---

### 🔧 Advanced Device Configuration Tasks

#### GpuP2PSetupTask (Admin)
**Purpose**: Map IO queues into GPU address space for P2P data-path; doorbells stay host/DBC-daemon (no GPU MMIO)
**Args**:
- `gpu_id`: GPU device ID (default: 0)
- `nvme_device`: NvmeDevice* (from NvmeSetupTask)

**Results**:
- `p2p_mapping`: P2PMapping* (IOVA mappings)
- `p2p_enabled`: bool

**Implementation Outline**:
```cpp
class GpuP2PSetupTask : public AdminSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        // Open /dev/gpu_p2p_wrapper or similar
        // Call ioctl to setup P2P mapping
        // Map queue memory to GPU; doorbells serviced by DBC daemon/shadow buffer
        return SetupResult("p2p_mapping", mapping);
    }
};
```

---

#### DbcDaemonTask / HostDbcDaemonTask (Admin)
**Purpose**: Start the DBC shadow-buffer daemon (alias names for the same launcher)
**Args**:
- `nvme_device`: NvmeDevice*
- `shadow_doorbell_buffer`: ShadowDoorbellBuffer*
- `mode`/`daemon_mode`: "shadow"/"host_daemon" (default: "shadow")

**Results**:
- `host_dbc_daemon` (primary handle)
- `dbc_daemon` (alias handle)

**Implementation Outline**:
```cpp
class DbcDaemonTask : public HostDbcDaemonTask { // Alias to shared launcher
    using HostDbcDaemonTask::HostDbcDaemonTask;
    std::vector<SetupResult> setup(const SetupArgs& args) override {
        auto res = HostDbcDaemonTask::setup(args);
        if (!res.empty()) {
            res.emplace_back("dbc_daemon", res.front().data, [](void*) {});
        }
        return res;
    }
};
```

---

### 🔧 Memory Factory Extensions

#### GdsMemoryFactoryTask (User)
**Purpose**: Setup GPUDirect Storage buffers
**Args**:
- `buf_size`: Buffer size
- `count`: Number of buffers
- `gpu_id`: GPU device ID

**Results**:
- `gds_buffers`: GdsBufferPool*

**Implementation Outline**:
```cpp
class GdsMemoryFactoryTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        // cuFileHandleRegister() for each buffer
        // Setup GDS file handles
        return SetupResult("gds_buffers", pool);
    }
};
```

---

#### ConsecutiveBufferTask (User)
**Purpose**: Allocate large consecutive buffer for sequential I/O
**Args**:
- `buffer_size`: Total buffer size (e.g., 128MB)
- `memory_type`: HOST, CUDA_HOST, or CUDA_GPU
- `nvme_device`: NvmeDevice*

**Results**:
- `consecutive_buffer`: Buffer*

**Implementation Outline**:
```cpp
class ConsecutiveBufferTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        Buffer* buf = host_create_consecutive_buffer(size);
        // Or cuda_host_create_consecutive_buffer()
        // Or cuda_gpu_create_consecutive_buffer()
        return SetupResult("consecutive_buffer", buf);
    }
};
```

---

### 🔧 Queue Configuration Tasks

#### MultiQueueSetupTask (User)
**Purpose**: Create multiple I/O queue pairs for multi-threaded benchmarks
**Args**:
- `num_queues`: Number of queue pairs (default: 4)
- `sq_depth`: Per-queue SQ depth (default: 16)
- `cq_depth`: Per-queue CQ depth (default: 16)
- `nvme_device`: NvmeDevice*

**Results**:
- `queue_array`: Queue** (array of queue pointers)
- `num_queues`: int

**Implementation Outline**:
```cpp
class MultiQueueSetupTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        Queue** queues = new Queue*[num_queues];
        for (int i = 0; i < num_queues; i++) {
            queues[i] = create_io_queue_pair(dev, depth);
        }
        return SetupResult("queue_array", queues);
    }
};
```

---

#### GpuQueueSetupTask (User)
**Purpose**: Allocate GPU-side queue memory and map to GPU address space
**Args**:
- `sq_depth`: Submission queue depth
- `cq_depth`: Completion queue depth
- `gpu_id`: GPU device ID
- `doorbell_mode`: MMIO, SHADOW, or DAEMON

**Results**:
- `gpu_queue`: GpuNvmeQueue*

**Implementation Outline**:
```cpp
class GpuQueueSetupTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        // Allocate GPU memory for SQ/CQ
        // Setup doorbell (MMIO BAR or shadow buffer)
        auto* queue = GpuNvmeQueue::create(...);
        return SetupResult("gpu_queue", queue);
    }
};
```

---

### 🔧 Benchmark Infrastructure Tasks

#### TestFileSetupTask (User)
**Purpose**: Create and initialize test data files
**Args**:
- `file_path`: Path to test file
- `file_size_mb`: Size in megabytes (default: 1024)
- `pattern_type`: "sequential", "random", "zeros" (default: "sequential")

**Results**:
- `test_file_path`: string
- `test_file_size`: size_t

**Implementation Outline**:
```cpp
class TestFileSetupTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        // Create file with specified size
        // Fill with pattern (sequential, random, etc.)
        // fsync() to ensure written
        auto* path_str = new std::string(file_path);
        return SetupResult("test_file_path", path_str);
    }
};
```

---

#### WarmupTask (User)
**Purpose**: Warm up caches and prime TLBs before benchmarking
**Args**:
- `warmup_iterations`: Number of warmup I/Os (default: 10)
- `nvme_device`: NvmeDevice*
- `buffer_pool`: Pool* (any type)

**Results**:
- `warmup_complete`: bool

**Implementation Outline**:
```cpp
class WarmupTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        // Perform several I/O operations
        // Read from different LBAs to prime caches
        // Discard results
        auto* done = new bool(true);
        return SetupResult("warmup_complete", done);
    }
};
```

---

#### StatCollectorTask (User)
**Purpose**: Setup performance counters and timing infrastructure
**Args**:
- `metrics`: List of metrics to collect (e.g., "latency,iops,bandwidth")

**Results**:
- `stat_collector`: StatCollector*

**Implementation Outline**:
```cpp
class StatCollectorTask : public UserSetupTask {
    SetupResult setup(const SetupArgs& args) override {
        auto* collector = new StatCollector();
        collector->register_metrics(metrics);
        collector->start();
        return SetupResult("stat_collector", collector, [](void* c) {
            auto* sc = static_cast<StatCollector*>(c);
            sc->stop();
            sc->print_summary();
            delete sc;
        });
    }
};
```

---

## Complete Benchmark Setup Example

```cpp
// Comprehensive setup for Mode 1-5 performance comparison
SetupHelper setup_mode_comparison() {
    SetupHelper helper;

    // === Phase 1: Environment Detection ===
    helper.add_task(new IommuCheckTask());
    helper.add_task(new GpuDetectionTask());
    helper.add_task(new NvmeDetectionTask());

    // === Phase 2: Device Initialization (Admin) ===
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new GpuP2PSetupTask());
    helper.add_task(new DbcDaemonTask());

    // === Phase 3: Memory Allocation ===
    // For Mode 1: GDS
    helper.add_task(new GdsMemoryFactoryTask(1048576, 32));

    // For Mode 2: Host Daemon + GPU Memory
    helper.add_task(new CudaGpuMemoryFactoryTask(1048576, 32));

    // For Mode 3: Host + Daemon + GPU Buffer
    helper.add_task(new HostMemoryFactoryTask(1048576, 32));

    // For Mode 4: DBC Shadow + GPU
    // (uses CudaGpuMemoryFactoryTask above)

    // For Mode 5: GPU Command + Daemon
    // (uses CudaGpuMemoryFactoryTask above)

    // === Phase 4: Queue Setup ===
    helper.add_task(new MultiQueueSetupTask(4));
    helper.add_task(new GpuQueueSetupTask());

    // === Phase 5: Test Infrastructure ===
    helper.add_task(new TestFileSetupTask(
        "/tmp/nvme_test_file.bin", 1024, "sequential"));
    helper.add_task(new WarmupTask(10));
    helper.add_task(new StatCollectorTask("latency,iops,bandwidth"));

    return helper;
}

// Usage
SetupHelper helper = setup_mode_comparison();
if (!helper.setup_all()) {
    fprintf(stderr, "Benchmark setup failed\n");
    return 1;
}

// Run benchmarks with all resources available
auto dev = helper.get<NvmeDevice*>("nvme_device");
auto gds_pool = helper.get<GdsBufferPool*>("gds_buffers");
auto stats = helper.get<StatCollector*>("stat_collector");

// Mode 1: GDS benchmark
run_gds_benchmark(dev, gds_pool, stats);

// Mode 2-5: Other benchmarks...

// Automatic cleanup
```

---

## Priority Implementation Order

For implementing these tasks, suggested priority:

### High Priority (Essential for basic benchmarking)
1. ✅ NvmeSetupTask - **Implemented**
2. ✅ HostMemoryFactoryTask - **Implemented**
3. ✅ CudaGpuMemoryFactoryTask - **Implemented**
4. TestFileSetupTask - Create test files
5. StatCollectorTask - Performance metrics

### Medium Priority (Important for comprehensive testing)
6. GpuDetectionTask - Auto-select GPU
7. NvmeDetectionTask - Auto-select NVMe
8. WarmupTask - Cache priming
9. ConsecutiveBufferTask - Large sequential I/O

### Low Priority (Advanced features)
10. GpuP2PSetupTask - P2P mapping
11. DbcDaemonTask - DBC support
12. GdsMemoryFactoryTask - GDS support
13. MultiQueueSetupTask - Multi-threaded tests
14. IommuCheckTask - Environment validation

---

## Summary

**Currently Implemented**: 4 tasks
**Recommended Additional**: 10 tasks
**Total Task Types**: 14 tasks

This comprehensive set of setup tasks would support:
- ✅ Module 53: Host I/O testing
- ✅ Module 54: CUDA host I/O testing
- ✅ Module 55/56: GPU I/O testing
- ✅ Module 57: Performance comparison benchmarks
- ✅ Module 58: Filesystem API testing

All tasks follow the same pattern: `SetupResult setup(const SetupArgs&)` with automatic RAII cleanup.
