# Module 53 Test Helper Library

**Location**: `test/helper/`
**Purpose**: Device selection and test setup infrastructure

## Documentation

- **[DeviceChooser](#devicechooser)** - Intelligent device selection
- **[SetupHelper](#setuphelper)** - Task-based test setup (14 tasks)
- **[P2P Setup Guide](P2P_SETUP_GUIDE.md)** - GPU-NVMe P2P configuration (2 levels)
- **[Testing Guide](README_TESTING.md)** - Running setup task tests

---

## DeviceChooser - Intelligent Device Selection

**Purpose**: Select best GPU/NVMe/Host combination for tests and benchmarks

---

## Overview

`DeviceChooser` is a test helper that automatically selects the best devices based on feature requirements and memory capacity. It uses the device detection system from `common/device/` to:

1. **Filter** devices by requirements (P2P, VFIO, shadow doorbell, etc.)
2. **Rank** devices by memory (highest first)
3. **Return** best matches for your test scenario

---

## Quick Start

### Basic Usage

```cpp
#include "helper/device_chooser.h"

// Detect all devices
auto features = detect_all_devices();

// Create chooser
DeviceChooser chooser(features);

// Select for P2P DMA
auto devices = chooser.select_for_p2p();

if (devices.gpu && devices.nvme) {
    printf("Using GPU %d with %s\n",
           devices.gpu->get_device_id(),
           devices.nvme->get_device_path().c_str());

    // Run your P2P test...
} else {
    printf("P2P not available\n");
}
```

### Preset Scenarios

```cpp
// P2P DMA (GPU ↔ NVMe)
auto p2p = chooser.select_for_p2p();

// Host DMA (VFIO)
auto host_dma = chooser.select_for_host_dma();

// GPU compute only
auto gpu_only = chooser.select_for_gpu_compute();

// Shadow doorbell testing
auto shadow_db = chooser.select_for_shadow_doorbell();
```

---

## Files

| File | Purpose |
|------|---------|
| `device_chooser.h` | API header |
| `device_chooser.cpp` | Implementation |
| `CMakeLists.txt` | Build configuration |
| `README.md` | This file |

---

## API Reference

### DeviceRequirements

Specifies which features are required.

```cpp
struct DeviceRequirements {
    // GPU requirements
    bool require_cuda;
    bool require_gpu_pinned_memory;  // Unified addressing
    bool require_gpu_p2p;            // GPU-NVMe P2P (FULL)
    size_t min_gpu_memory;

    // NVMe requirements
    bool require_nvme;
    bool require_shadow_doorbell;    // Shadow DB (PARTIAL or FULL)
    bool require_nvme_p2p;           // NVMe P2P (FULL)
    uint64_t min_nvme_capacity;

    // Host requirements
    bool require_vfio;               // VFIO (FULL)
    bool require_host_p2p;           // P2P infrastructure (FULL)
    bool require_iommu;
    uint64_t min_host_memory;
};
```

**Preset Factories:**
- `DeviceRequirements::for_p2p()` - GPU-NVMe P2P
- `DeviceRequirements::for_host_dma()` - Host VFIO
- `DeviceRequirements::for_gpu_compute()` - GPU only
- `DeviceRequirements::for_shadow_doorbell()` - Shadow DB

### SelectedDevices

Contains pointers to selected devices.

```cpp
struct SelectedDevices {
    const HostFeature* host;   // Always same (system-wide)
    const GpuFeature* gpu;     // Best GPU or nullptr
    const NvmeFeature* nvme;   // Best NVMe or nullptr

    bool all_requirements_met() const;
    string get_description() const;
    void print() const;
};
```

**Checking Results:**
```cpp
auto devices = chooser.select_for_p2p();

if (devices.gpu && devices.nvme) {
    // Both found - ready for P2P
} else if (!devices.gpu) {
    // No suitable GPU
} else if (!devices.nvme) {
    // No suitable NVMe
}
```

### DeviceChooser

Main selection engine.

```cpp
class DeviceChooser {
public:
    explicit DeviceChooser(const SystemFeatures& features);

    // Select best device combination
    SelectedDevices select(const DeviceRequirements& req) const;

    // Convenience methods
    SelectedDevices select_for_p2p() const;
    SelectedDevices select_for_host_dma() const;
    SelectedDevices select_for_gpu_compute() const;
    SelectedDevices select_for_shadow_doorbell() const;

    // Get all matching devices
    std::vector<size_t> get_matching_gpus(const DeviceRequirements& req) const;
    std::vector<size_t> get_matching_nvme(const DeviceRequirements& req) const;
};
```

---

## Usage Examples

### Example 1: P2P Benchmark

```cpp
#include "helper/device_chooser.h"

int main() {
    // Detect devices
    auto features = detect_all_devices();
    DeviceChooser chooser(features);

    // Select for P2P
    auto devices = chooser.select_for_p2p();

    if (!devices.gpu || !devices.nvme) {
        fprintf(stderr, "P2P not available\n");
        devices.print();
        return 1;
    }

    // Use selected devices
    int gpu_id = devices.gpu->get_device_id();
    const char* nvme_path = devices.nvme->get_device_path().c_str();

    printf("Running P2P benchmark:\n");
    printf("  GPU %d: %s\n", gpu_id, devices.gpu->get_name().c_str());
    printf("  NVMe: %s\n", nvme_path);

    // Your benchmark code here...

    return 0;
}
```

### Example 2: Custom Requirements

```cpp
// Need GPU with >= 8GB memory and NVMe with >= 500GB
DeviceRequirements req;
req.require_cuda = true;
req.require_nvme = true;
req.min_gpu_memory = 8ULL * 1024 * 1024 * 1024;       // 8 GB
req.min_nvme_capacity = 500ULL * 1024 * 1024 * 1024;  // 500 GB

auto devices = chooser.select(req);

if (devices.gpu && devices.nvme) {
    printf("Found suitable devices:\n");
    printf("  GPU: %.2f GB\n",
           devices.gpu->get_total_memory() / (1024.0*1024*1024));
    printf("  NVMe: %.2f GB\n",
           devices.nvme->get_capacity_bytes() / (1024.0*1024*1024));
} else {
    printf("Requirements not met\n");
}
```

### Example 3: GTest Integration

```cpp
#include <gtest/gtest.h>
#include "helper/device_chooser.h"

class P2PTest : public ::testing::Test {
protected:
    void SetUp() override {
        features_ = detect_all_devices();
        DeviceChooser chooser(features_);
        devices_ = chooser.select_for_p2p();

        ASSERT_TRUE(devices_.gpu != nullptr)
            << "No P2P-capable GPU found";
        ASSERT_TRUE(devices_.nvme != nullptr)
            << "No P2P-capable NVMe found";
    }

    SystemFeatures features_;
    SelectedDevices devices_;
};

TEST_F(P2PTest, BasicTransfer) {
    int gpu_id = devices_.gpu->get_device_id();
    const char* nvme_path = devices_.nvme->get_device_path().c_str();

    // Your P2P test...
}
```

### Example 4: Fallback Logic

```cpp
// Try P2P first, fallback to host DMA
auto devices = chooser.select_for_p2p();

if (!devices.gpu || !devices.nvme) {
    printf("P2P not available, falling back to host DMA\n");
    devices = chooser.select_for_host_dma();

    if (!devices.nvme) {
        fprintf(stderr, "No usable NVMe device\n");
        return 1;
    }
}

// Use devices...
```

### Example 5: All Matching Devices

```cpp
// Get all P2P-capable GPUs (sorted by memory)
auto gpu_indices = chooser.get_matching_gpus(DeviceRequirements::for_p2p());

printf("Found %zu P2P-capable GPUs:\n", gpu_indices.size());
for (size_t idx : gpu_indices) {
    const auto& gpu = features.gpus[idx];
    printf("  GPU %d: %s (%.2f GB)\n",
           gpu.get_device_id(),
           gpu.get_name().c_str(),
           gpu.get_total_memory() / (1024.0*1024*1024));
}

// Get all NVMe devices with shadow doorbell
auto nvme_indices = chooser.get_matching_nvme(
    DeviceRequirements::for_shadow_doorbell()
);

printf("Found %zu NVMe with shadow doorbell:\n", nvme_indices.size());
for (size_t idx : nvme_indices) {
    const auto& nvme = features.nvme_devs[idx];
    printf("  %s: %s\n",
           nvme.get_device_path().c_str(),
           support_level_str(nvme.get_shadow_doorbell_support()));
}
```

---

## Selection Algorithm

### Filtering

Devices are filtered by requirements:

| Requirement | Filter Condition |
|-------------|------------------|
| `require_cuda` | `gpu.has_cuda()` |
| `require_gpu_pinned_memory` | `gpu.has_unified_memory()` |
| `require_gpu_p2p` | `gpu.get_nvme_p2p_support() == FULL` |
| `min_gpu_memory` | `gpu.get_total_memory() >= min` |
| `require_shadow_doorbell` | `nvme.get_shadow_doorbell_support() >= PARTIAL` |
| `require_nvme_p2p` | `nvme.get_p2p_support() == FULL` |
| `min_nvme_capacity` | `nvme.get_capacity_bytes() >= min` |
| `require_vfio` | `host.get_vfio_support() == FULL` |
| `require_host_p2p` | `host.get_p2p_support() == FULL` |
| `require_iommu` | `host.has_iommu_enabled()` |

### Ranking

Matching devices are sorted by memory:

- **GPUs**: Descending by `get_total_memory()`
- **NVMe**: Descending by `get_capacity_bytes()`

The **highest-memory** device is returned.

### Example

System has:
- GPU 0: RTX 3090 (24 GB) - P2P support
- GPU 1: RTX 4090 (24 GB) - P2P support
- GPU 2: GTX 1080 (8 GB) - No P2P

For `select_for_p2p()`:
1. **Filter**: GPU 0 and GPU 1 match (GPU 2 rejected - no P2P)
2. **Sort**: Both have 24 GB (tie)
3. **Return**: GPU 0 (first in sorted order)

---

## Memory Capacity Detection

### GPU Memory

```cpp
auto devices = chooser.select_for_gpu_compute();
if (devices.gpu) {
    size_t mem_bytes = devices.gpu->get_total_memory();
    printf("GPU has %.2f GB\n", mem_bytes / (1024.0*1024*1024));
}
```

### NVMe Capacity

```cpp
auto devices = chooser.select_for_host_dma();
if (devices.nvme) {
    uint64_t capacity = devices.nvme->get_capacity_bytes();
    printf("NVMe has %.2f GB\n", capacity / (1024.0*1024*1024));
}
```

### Host Memory

```cpp
auto devices = chooser.select(DeviceRequirements());
if (devices.host) {
    uint64_t total = devices.host->get_total_memory();
    uint64_t avail = devices.host->get_available_memory();
    printf("Host RAM: %.2f GB total, %.2f GB available\n",
           total / (1024.0*1024*1024),
           avail / (1024.0*1024*1024));
}
```

---

## Demo Program

Run `device_chooser_demo` to see selection in action:

```bash
./device_chooser_demo
```

**Output shows:**
- P2P selection
- Host DMA selection
- GPU compute selection
- Shadow doorbell selection
- Custom requirements
- All matching devices

---

## Integration with Tests

### Recommended Pattern

```cpp
class MyHardwareTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Detect once per test class
        static SystemFeatures features = detect_all_devices();
        static DeviceChooser chooser(features);

        // Select for this test
        devices_ = chooser.select_for_p2p();  // or other scenario

        // Skip if requirements not met
        if (!devices_.gpu || !devices_.nvme) {
            GTEST_SKIP() << "P2P hardware not available";
        }
    }

    SelectedDevices devices_;
};
```

### CMake Integration

```cmake
# In test/CMakeLists.txt

add_executable(my_p2p_test my_p2p_test.cpp)

target_link_libraries(my_p2p_test PRIVATE
  device_chooser    # Device selection helper
  device_detector   # Device detection
  ${GTEST_BASIC_LIB}
)
```

---

## Build

### Library

```bash
cd build
ninja device_chooser
```

### Demo

```bash
ninja device_chooser_demo
./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/device_chooser_demo
```

---

## Dependencies

- `device_detector` (common/device/)
- `cuda_utils.h`
- Standard C++ (algorithm, vector, sstream)

---

## Benefits

✅ **Automatic Selection** - No manual device configuration
✅ **Memory Prioritization** - Always picks highest-memory device
✅ **Feature Filtering** - Ensures requirements are met
✅ **Test Skipping** - Easy to skip tests when hardware unavailable
✅ **Reusable** - Same helper for all test scenarios
✅ **Type-Safe** - Compile-time checking via const pointers

---

**Status**: ✅ Complete
**Testing**: Run `device_chooser_demo` for verification

---

## Setup Helper System

**File**: `setup_helper.h` / `setup_helper.cpp`

Task-based test setup system for automated resource initialization and cleanup.

### Overview

The Setup Helper provides a flexible, task-based approach to configuring complex test environments:
- **Modular Tasks**: Each setup step is encapsulated in a task (NVMe device, memory pools, etc.)
- **Automatic Cleanup**: RAII ensures resources are freed when tests complete
- **Dependency Management**: Tasks can access results from previous tasks
- **Privilege Awareness**: Separate user and admin tasks
- **Type-Safe Access**: Template-based result retrieval

### Architecture

```
SetupHelper (coordinator)
    ├── SetupTask (base class)
    │   ├── UserSetupTask (no sudo required)
    │   │   ├── HostMemoryFactoryTask
    │   │   ├── CudaHostMemoryFactoryTask
    │   │   └── CudaGpuMemoryFactoryTask
    │   └── AdminSetupTask (requires sudo)
    │       └── NvmeSetupTask (VFIO binding)
    └── SetupResult (resources + cleanup)
```

### Available Tasks

| Task | Type | Purpose | Result |
|------|------|---------|--------|
| `NvmeSetupTask` | Admin | Open NVMe device via VFIO | `nvme_device`, `iosq`, `iocq` |
| `HostMemoryFactoryTask` | User | Create host buffer pool | `host_pool` |
| `CudaHostMemoryFactoryTask` | User | Create CUDA host pool | `cuda_host_pool` |
| `CudaGpuMemoryFactoryTask` | User | Create CUDA GPU pool | `cuda_gpu_pool` |

### Quick Start

#### Method 1: Convenience Function
```cpp
#include "helper/setup_helper.h"

// Simplest approach - uses environment variables
SetupHelper helper = create_host_io_setup();

if (helper.setup_all()) {
    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");
    
    // Use resources...
}
// Automatic cleanup
```

#### Method 2: Manual Configuration
```cpp
SetupHelper helper;

// Load environment variables
auto env_args = load_env_args({"NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE"});
helper.set_global_args(env_args);

// Add tasks
helper.add_task(new NvmeSetupTask());
helper.add_task(new HostMemoryFactoryTask(4096, 16));

// Execute
if (helper.setup_all()) {
    // Access results...
}
```

#### Method 3: Custom Arguments
```cpp
SetupHelper helper;

// Override environment
helper.set_arg("bdf", "0000:41:00.0");
helper.set_arg("sq_depth", "32");
helper.set_arg("buf_size", "8192");
helper.set_arg("count", "8");

helper.add_task(new NvmeSetupTask());
helper.add_task(new HostMemoryFactoryTask());

helper.setup_all();
```

### Usage in Tests

#### GoogleTest Integration
```cpp
class MyTest : public ::testing::Test {
protected:
    SetupHelper helper;

    void SetUp() override {
        helper = create_host_io_setup(4096, 8);
        
        if (!helper.setup_all()) {
            GTEST_SKIP() << "Setup failed - check VFIO configuration";
        }
    }

    // No TearDown needed - automatic cleanup
};

TEST_F(MyTest, ReadWriteTest) {
    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");
    
    // Test code...
}
```

### Task Arguments

Each task accepts arguments via `SetupArgs` (map<string, string>):

**NvmeSetupTask**:
- `bdf` or `NVME_BDF`: PCI address (e.g., "0000:41:00.0")
- `sq_depth`: Submission queue depth (default: 16)
- `cq_depth`: Completion queue depth (default: 16)
- `lba_size` or `NVME_LBA_SIZE`: LBA size (default: 512)
- `nsid` or `NVME_NSID`: Namespace ID (default: 1)

**HostMemoryFactoryTask**:
- `buf_size`: Buffer size in bytes (default: 4096)
- `count`: Number of buffers (default: 16)
- `nvme_device`: NvmeDevice* from NvmeSetupTask (required)

**CudaHostMemoryFactoryTask**:
- Same as HostMemoryFactoryTask

**CudaGpuMemoryFactoryTask**:
- Same as HostMemoryFactoryTask

### Convenience Functions

```cpp
// Host I/O setup (Module 53)
SetupHelper create_host_io_setup(size_t buf_size = 4096, uint16_t count = 16);

// CUDA host I/O setup (Module 54)
SetupHelper create_cuda_host_io_setup(size_t buf_size = 4096, uint16_t count = 16);

// CUDA GPU I/O setup (Module 55/56)
SetupHelper create_cuda_gpu_io_setup(size_t buf_size = 4096, uint16_t count = 16);
```

### Example Program

Run the example to see all usage patterns:

```bash
# Setup environment
export NVME_BDF="0000:41:00.0"
export NVME_NSID="1"
export NVME_LBA_SIZE="512"

# Build and run
cd build
ninja setup_helper_example
sudo -E ./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/helper/setup_helper_example

# Run specific example
sudo -E ./path/to/setup_helper_example 1  # Example 1 only
```

### Creating Custom Tasks

Extend `UserSetupTask` or `AdminSetupTask`:

```cpp
class MyCustomTask : public UserSetupTask {
public:
    std::string get_name() const override { return "MyCustom"; }
    
    SetupResult setup(const SetupArgs& args) override {
        // 1. Get arguments
        auto buf_size = get_arg_int<size_t>(args, "buf_size", 4096);
        
        // 2. Initialize resource
        MyResource* resource = create_resource(buf_size);
        if (!resource) return SetupResult();
        
        // 3. Return with cleanup function
        return SetupResult("my_resource", resource, [](void* p) {
            destroy_resource(static_cast<MyResource*>(p));
        });
    }
};

// Usage
helper.add_task(new MyCustomTask());
```

### Performance Benchmark Setup Tasks

For comprehensive performance testing (like Module 57), you might need:

1. **Environment Detection Tasks**:
   - `GpuDetectionTask`: Detect available GPUs, check P2P support
   - `NvmeDetectionTask`: Detect NVMe devices, check capacity
   - `IommuCheckTask`: Verify IOMMU is enabled

2. **Device Configuration Tasks**:
   - `NvmeSetupTask`: ✅ Already implemented
   - `GpuP2PSetupTask`: Map IO queues for GPU P2P data path (doorbells stay host/DBC daemon)
   - `DbcDaemonTask` / `HostDbcDaemonTask`: Start DBC shadow-buffer daemon (same launcher; alias retained for compatibility)

3. **Memory Factory Tasks**:
   - `HostMemoryFactoryTask`: ✅ Already implemented
   - `CudaHostMemoryFactoryTask`: ✅ Already implemented
   - `CudaGpuMemoryFactoryTask`: ✅ Already implemented
   - `GdsMemoryFactoryTask`: GPUDirect Storage setup
   - `ConsecutiveBufferTask`: Large consecutive buffer allocation

4. **Queue Configuration Tasks**:
   - `HostQueueSetupTask`: Host-side I/O queues
   - `GpuQueueSetupTask`: GPU-side I/O queues
   - `MultiQueueSetupTask`: Multiple queue pairs

5. **Benchmark Configuration Tasks**:
   - `TestFileSetupTask`: Create/prepare test files
   - `WarmupTask`: Warm up caches
   - `StatCollectorTask`: Setup performance counters

### Benefits

✅ **Reusability**: Write setup once, use in all tests  
✅ **Maintainability**: Centralized resource management  
✅ **Safety**: RAII prevents resource leaks  
✅ **Flexibility**: Mix and match tasks as needed  
✅ **Error Handling**: Automatic rollback on failure  
✅ **Testability**: Isolated, unit-testable tasks  

### See Also

- `setup_helper.h`: Complete API documentation
- `setup_helper_example.cpp`: 6 usage examples
- `../system_test/test_host_io_system.cpp`: Real-world usage
