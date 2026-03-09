/**
 * @file setup_helper.h
 * @brief Test setup helper system for Module 53 tests
 *
 * Provides a flexible task-based setup system for NVMe I/O tests.
 * Supports both user-level and admin-level operations with automatic
 * cleanup and resource management.
 *
 * Design Pattern: Task-based setup with RAII
 * - SetupTask: Base class with virtual setup() method
 * - UserSetupTask: Tasks that don't require root privileges
 * - AdminSetupTask: Tasks that require sudo/root
 * - SetupHelper: Factory and coordinator for setup tasks
 *
 * Usage Example:
 * ```cpp
 * SetupHelper helper;
 *
 * // Add tasks
 * helper.add_task(new NvmeSetupTask("0000:41:00.0"));
 * helper.add_task(new HostMemoryFactoryTask(4096, 16));
 *
 * // Execute all tasks
 * if (helper.setup_all()) {
 *     // Get results
 *     NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
 *     HostPool* pool = helper.get<HostPool*>("host_pool");
 *
 *     // Use resources...
 * }
 * // Automatic cleanup when helper goes out of scope
 * ```
 */

#pragma once

#include <string>
#include <map>
#include <vector>
#include <memory>
#include <functional>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>

// Module 53 APIs
#include "mapper/mapper_host.h"
#include "memory/host_memory_buffer.h"
#include "memory/memory_pool.h"
#include "memory/buffer_factory.h"
#include "doorbell/dbc_setup.h"  // For nvme::ShadowDoorbellBuffer
#include "doorbell/shadow_db_controller_daemon.h"

#ifdef __CUDACC__
#include "memory/cuda_host_memory_buffer.h"
#include "memory/cuda_gpu_memory_buffer.h"
#endif

// ============================================================================
// Type Definitions
// ============================================================================

/// Setup arguments (key-value pairs)
using SetupArgs = std::map<std::string, std::string>;

/// Setup result (type-erased pointer with name)
struct SetupResult {
    std::string name;                          ///< Result identifier
    void* data{nullptr};                       ///< Type-erased data pointer
    std::function<void(void*)> cleanup;        ///< Custom cleanup function

    SetupResult() = default;
    SetupResult(const std::string& n, void* d, std::function<void(void*)> c = nullptr)
        : name(n), data(d), cleanup(c) {}

    ~SetupResult() {
        if (cleanup && data) {
            cleanup(data);
        }
    }

    // Move-only
    SetupResult(SetupResult&& other) noexcept
        : name(std::move(other.name)), data(other.data), cleanup(std::move(other.cleanup)) {
        other.data = nullptr;
    }

    SetupResult& operator=(SetupResult&& other) noexcept {
        if (this != &other) {
            if (cleanup && data) cleanup(data);
            name = std::move(other.name);
            data = other.data;
            cleanup = std::move(other.cleanup);
            other.data = nullptr;
        }
        return *this;
    }

    SetupResult(const SetupResult&) = delete;
    SetupResult& operator=(const SetupResult&) = delete;

    template<typename T>
    T get() const { return static_cast<T>(data); }
};

// ============================================================================
// Helper Data Structures
// ============================================================================

/**
 * @brief Simple statistics collector for benchmarking
 */
struct StatCollector {
    std::string metrics;
    bool running{false};

    void start() { running = true; }
    void stop() { running = false; }
    void print_summary() const {
        printf("Statistics Summary: %s (running=%d)\n", metrics.c_str(), running);
    }
};

// ============================================================================
// Base Setup Task
// ============================================================================

/**
 * @brief Base class for all setup tasks
 *
 * Derived classes implement setup() to perform specific initialization
 * and return a SetupResult with cleanup function.
 */
class SetupTask {
public:
    virtual ~SetupTask() = default;

    /// Execute the setup task
    /// @param args Setup arguments (key-value pairs)
    /// @return Vector of SetupResults (most tasks return 1, but some may return multiple)
    virtual std::vector<SetupResult> setup(const SetupArgs& args) = 0;

    /// Get task name for logging
    virtual std::string get_name() const = 0;

    /// Check if task requires admin privileges
    virtual bool requires_admin() const = 0;
};

// ============================================================================
// User-Level Setup Tasks (no sudo required)
// ============================================================================

/**
 * @brief Base class for user-level setup tasks
 */
class UserSetupTask : public SetupTask {
public:
    bool requires_admin() const override { return false; }
};

/**
 * @brief Host memory factory setup task
 *
 * Creates a host memory buffer pool using pageable memory.
 * Suitable for Module 53 host I/O tests.
 *
 * Args:
 *   - "buf_size": Buffer size in bytes (default: 4096)
 *   - "count": Number of buffers (default: 16)
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "host_pool": HostPool*
 */
class HostMemoryFactoryTask : public UserSetupTask {
private:
    size_t default_buf_size_;
    uint16_t default_count_;

public:
    HostMemoryFactoryTask(size_t buf_size = 4096, uint16_t count = 16)
        : default_buf_size_(buf_size), default_count_(count) {}

    std::string get_name() const override { return "HostMemoryFactory"; }

    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

#ifdef __CUDACC__
/**
 * @brief CUDA host memory factory setup task
 *
 * Creates a CUDA host-pinned memory buffer pool.
 * Suitable for Module 54 CUDA host I/O tests.
 *
 * Args:
 *   - "buf_size": Buffer size in bytes (default: 4096)
 *   - "count": Number of buffers (default: 16)
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "cuda_host_pool": CudaHostPool*
 */
class CudaHostMemoryFactoryTask : public UserSetupTask {
private:
    size_t default_buf_size_;
    uint16_t default_count_;

public:
    CudaHostMemoryFactoryTask(size_t buf_size = 4096, uint16_t count = 16)
        : default_buf_size_(buf_size), default_count_(count) {}

    std::string get_name() const override { return "CudaHostMemoryFactory"; }

    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief CUDA GPU memory factory setup task
 *
 * Creates a CUDA GPU device memory buffer pool.
 * Suitable for Module 55/56 GPU I/O tests.
 *
 * Args:
 *   - "buf_size": Buffer size in bytes (default: 4096)
 *   - "count": Number of buffers (default: 16)
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "cuda_gpu_pool": CudaGpuPool*
 */
class CudaGpuMemoryFactoryTask : public UserSetupTask {
private:
    size_t default_buf_size_;
    uint16_t default_count_;

public:
    CudaGpuMemoryFactoryTask(size_t buf_size = 4096, uint16_t count = 16)
        : default_buf_size_(buf_size), default_count_(count) {}

    std::string get_name() const override { return "CudaGpuMemoryFactory"; }

    std::vector<SetupResult> setup(const SetupArgs& args) override;
};
#endif // __CUDACC__

/**
 * @brief Test file setup task
 *
 * Creates and initializes test data files with specified patterns.
 * Useful for I/O benchmarks requiring pre-populated test data.
 *
 * Args:
 *   - "file_path": Path to test file (required)
 *   - "file_size_mb": Size in megabytes (default: 1024)
 *   - "pattern_type": "sequential"(0), "random"(1), "zeros"(2) (default: "sequential")
 *
 * Result:
 *   - "test_file_path": std::string* (path to created file)
 *   - "test_file_size": size_t* (file size in bytes)
 */
class TestFileSetupTask : public UserSetupTask {
private:
    std::string default_file_path_;
    size_t default_size_mb_;
    std::string default_pattern_;

public:
    TestFileSetupTask(const std::string& file_path = "/tmp/nvme_test_file.bin",
                      size_t size_mb = 1024,
                      const std::string& pattern = "sequential")
        : default_file_path_(file_path)
        , default_size_mb_(size_mb)
        , default_pattern_(pattern) {}

    std::string get_name() const override { return "TestFileSetup"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Performance statistics collector task
 *
 * Sets up performance counters and timing infrastructure for benchmarking.
 *
 * Args:
 *   - "metrics": Comma-separated list (e.g., "latency,iops,bandwidth")
 *
 * Result:
 *   - "stat_collector": StatCollector*
 */
class StatCollectorTask : public UserSetupTask {
private:
    std::string default_metrics_;

public:
    explicit StatCollectorTask(const std::string& metrics = "latency,iops,bandwidth")
        : default_metrics_(metrics) {}

    std::string get_name() const override { return "StatCollector"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief GPU detection task
 *
 * Detects and enumerates GPUs, checks capabilities.
 * Useful for auto-selecting GPUs for testing.
 *
 * Args:
 *   - "min_compute_capability": Minimum CUDA compute (default: "7.0")
 *   - "require_p2p": Require P2P support "true"/"false" (default: "true")
 *
 * Result:
 *   - "gpu_count": int*
 *   - "selected_gpu_id": int* (auto-selected GPU for testing)
 */
class GpuDetectionTask : public UserSetupTask {
private:
    std::string default_min_compute_;
    bool default_require_p2p_;

public:
    GpuDetectionTask(const std::string& min_compute = "7.0", bool require_p2p = true)
        : default_min_compute_(min_compute)
        , default_require_p2p_(require_p2p) {}

    std::string get_name() const override { return "GpuDetection"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief NVMe device detection task
 *
 * Enumerates NVMe devices and checks capabilities.
 * Can auto-select suitable device for testing.
 *
 * Args:
 *   - "min_capacity_gb": Minimum capacity in GB (default: 10)
 *   - "require_dbc": Require doorbell buffer config support (default: false)
 *
 * Result:
 *   - "nvme_count": int*
 *   - "selected_nvme_bdf": std::string* (auto-selected device BDF)
 */
class NvmeDetectionTask : public UserSetupTask {
private:
    uint32_t default_min_capacity_;
    bool default_require_dbc_;

public:
    NvmeDetectionTask(uint32_t min_capacity_gb = 10, bool require_dbc = false)
        : default_min_capacity_(min_capacity_gb)
        , default_require_dbc_(require_dbc) {}

    std::string get_name() const override { return "NvmeDetection"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Warmup task
 *
 * Warms up caches and primes TLBs before benchmarking.
 * Performs several dummy I/O operations to stabilize performance.
 *
 * Args:
 *   - "warmup_iterations": Number of warmup I/Os (default: 10)
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "warmup_complete": bool*
 */
class WarmupTask : public UserSetupTask {
private:
    int default_iterations_;

public:
    explicit WarmupTask(int iterations = 10)
        : default_iterations_(iterations) {}

    std::string get_name() const override { return "Warmup"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Consecutive buffer allocation task
 *
 * Allocates a large consecutive buffer for sequential I/O.
 * Useful for large sequential read/write benchmarks.
 *
 * Args:
 *   - "buffer_size": Total buffer size in bytes (default: 128MB)
 *   - "memory_type": "HOST", "CUDA_HOST", or "CUDA_GPU" (default: "HOST")
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "consecutive_buffer": DmaBuf*
 */
class ConsecutiveBufferTask : public UserSetupTask {
private:
    size_t default_size_;
    std::string default_mem_type_;

public:
    ConsecutiveBufferTask(size_t size = 128 * 1024 * 1024,
                          const std::string& mem_type = "HOST")
        : default_size_(size)
        , default_mem_type_(mem_type) {}

    std::string get_name() const override { return "ConsecutiveBuffer"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Multiple queue pair setup task
 *
 * Creates multiple I/O queue pairs for multi-threaded benchmarks.
 *
 * Args:
 *   - "num_queues": Number of queue pairs (default: 4)
 *   - "sq_depth": Per-queue SQ depth (default: 16)
 *   - "cq_depth": Per-queue CQ depth (default: 16)
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "queue_array": Queue*** (array of queue pointers)
 *   - "num_queues": int*
 */
class MultiQueueSetupTask : public UserSetupTask {
private:
    int default_num_queues_;
    uint16_t default_sq_depth_;
    uint16_t default_cq_depth_;

public:
    MultiQueueSetupTask(int num_queues = 4, uint16_t sq_depth = 16, uint16_t cq_depth = 16)
        : default_num_queues_(num_queues)
        , default_sq_depth_(sq_depth)
        , default_cq_depth_(cq_depth) {}

    std::string get_name() const override { return "MultiQueueSetup"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

// ============================================================================
// Admin-Level Setup Tasks (require sudo)
// ============================================================================

/**
 * @brief Base class for admin-level setup tasks
 */
class AdminSetupTask : public SetupTask {
public:
    bool requires_admin() const override { return true; }
};

/**
 * @brief VFIO binding metadata returned by VfioBindingTask
 */
struct VfioBindingInfo {
    std::string bdf;              ///< PCI device bound by the task
    bool bound_by_helper{false};  ///< True if task performed the binding
};

/**
 * @brief Ensure NVMe device is bound to vfio-pci
 *
 * Provides standalone binding so legacy tests can keep manual setup logic
 * while reusing the SetupTask workflow for privilege escalation.
 *
 * Args:
 *   - "bdf" or "NVME_BDF": Target PCI address
 *
 * Result:
 *   - "vfio_binding": VfioBindingInfo*
 */
class VfioBindingTask : public AdminSetupTask {
private:
    std::string default_bdf_;

public:
    explicit VfioBindingTask(std::string bdf = "")
        : default_bdf_(std::move(bdf)) {}

    std::string get_name() const override { return "VfioBinding"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief NVMe device setup task
 *
 * Opens NVMe device via VFIO and sets up I/O queues.
 * Requires VFIO driver binding (admin privileges).
 *
 * Args:
 *   - "bdf": PCI BDF address (e.g., "0000:41:00.0") - required or from NVME_BDF env
 *   - "sq_depth": Submission queue depth (default: 16)
 *   - "cq_depth": Completion queue depth (default: 16)
 *   - "lba_size": Logical block size (default: 512)
 *   - "nsid": Namespace ID (default: 1 or from NVME_NSID env)
 *
 * Result:
 *   - "nvme_device": NvmeDevice*
 *   - "iosq": Queue* (I/O submission queue)
 *   - "iocq": Queue* (I/O completion queue)
 */
class NvmeSetupTask : public AdminSetupTask {
private:
    std::string default_bdf_;
    uint16_t default_sq_depth_;
    uint16_t default_cq_depth_;
    uint32_t default_lba_size_;

public:
    NvmeSetupTask(const std::string& bdf = "",
                  uint16_t sq_depth = 16,
                  uint16_t cq_depth = 16,
                  uint32_t lba_size = 512)
        : default_bdf_(bdf)
        , default_sq_depth_(sq_depth)
        , default_cq_depth_(cq_depth)
        , default_lba_size_(lba_size) {}

    std::string get_name() const override { return "NvmeSetup"; }

    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

#ifdef __CUDACC__
/**
 * @brief GPU P2P setup task
 *
 * Maps IO queues into GPU VA for P2P DMA data path. Doorbells are serviced via
 * shadow buffer + daemon (GPU does not touch MMIO doorbells).
 * Requires admin privileges for IOMMU/VFIO operations.
 *
 * Args:
 *   - "gpu_id": GPU device ID (default: 0)
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *
 * Result:
 *   - "p2p_enabled": bool*
 */
class GpuP2PSetupTask : public AdminSetupTask {
private:
    int default_gpu_id_;

public:
    explicit GpuP2PSetupTask(int gpu_id = 0)
        : default_gpu_id_(gpu_id) {}

    std::string get_name() const override { return "GpuP2PSetup"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief GPUDirect Storage memory factory task
 *
 * Sets up GPUDirect Storage (GDS) buffers for high-performance I/O.
 * Requires cuFile library and GDS-capable drivers.
 *
 * Args:
 *   - "buf_size": Buffer size in bytes (default: 4096)
 *   - "count": Number of buffers (default: 16)
 *   - "gpu_id": GPU device ID (default: 0)
 *
 * Result:
 *   - "gds_buffers": void* (GDS buffer pool handle)
 */
class GdsMemoryFactoryTask : public AdminSetupTask {
private:
    size_t default_buf_size_;
    uint16_t default_count_;
    int default_gpu_id_;

public:
    GdsMemoryFactoryTask(size_t buf_size = 4096, uint16_t count = 16, int gpu_id = 0)
        : default_buf_size_(buf_size)
        , default_count_(count)
        , default_gpu_id_(gpu_id) {}

    std::string get_name() const override { return "GdsMemoryFactory"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};
#endif // __CUDACC__

/**
 * @brief Shadow doorbell buffer descriptor (Module 55.2)
 */
// ShadowDoorbellBuffer moved to production library
// Use nvme::ShadowDoorbellBuffer from dbc_setup.h
using ShadowDoorbellBuffer = nvme::ShadowDoorbellBuffer;

/**
 * @brief Host doorbell daemon setup task (Module 55.1)
 *
 * Launches the simple host daemon that polls SQ tail and rings MMIO doorbells directly.
 * Used for non-DBC flows (no shadow buffer), host queue, or host-built commands.
 *
 * Args:
 *   - "poll_interval_us": Polling interval in microseconds (default: 10)
 *
 * Result:
 *   - "host_doorbell_daemon": HostDoorbellDaemon*
 */
class HostDoorbellDaemonTask : public AdminSetupTask {
private:
    uint32_t default_poll_interval_us_;

public:
    explicit HostDoorbellDaemonTask(uint32_t poll_interval_us = 10)
        : default_poll_interval_us_(poll_interval_us) {}

    std::string get_name() const override { return "HostDoorbellDaemon"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Shadow doorbell buffer setup task (Module 55.2)
 *
 * Allocates the NVMe Doorbell Buffer Config "shadow doorbell" array in pinned, VFIO-mapped
 * host memory so GPU kernels (or the controller) can update/read doorbell values.
 *
 * Args:
 *   - "queue_count": Number of I/O queues (default: 1)
 *   - "use_eventidx": "1" to allocate optional event index buffer (default: 0)
 *
 * Results:
 *   - "shadow_doorbell_buffer": ShadowDoorbellBuffer*
 *   - (optional) "eventidx_buffer": ShadowDoorbellBuffer*
 */
class DbcShadowBufferTask : public AdminSetupTask {
private:
    uint16_t default_queue_count_;
    bool default_use_eventidx_;
    uint16_t default_queue_id_;

public:
    DbcShadowBufferTask(uint16_t queue_count = 1, bool use_eventidx = false, uint16_t queue_id = 1)
        : default_queue_count_(queue_count)
        , default_use_eventidx_(use_eventidx)
        , default_queue_id_(queue_id) {}

    std::string get_name() const override { return "DbcShadowBuffer"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Host-side shadow doorbell controller daemon
 *
 * Polls the shadow doorbell buffer and mirrors updates into MMIO doorbells for
 * one queue. Useful when hardware advertises DBC capability but does not
 * autonomously poll the shadow buffer (e.g., PM9A1 firmware) or for emulated
 * controllers.
 *
 * Args:
 *  - \"shadow_doorbell_buffer\": ShadowDoorbellBuffer* (required)
 *  - \"iosq_struct\": NvmeQueueStruct* (required for SQ doorbell pointer)
 *  - \"iocq_struct\": NvmeQueueStruct* (required for CQ doorbell pointer)
 *  - \"qid\": Queue identifier (default: 1)
 *  - \"doorbell_stride\": Doorbell stride in bytes (default: 4 << CAP.DSTRD, fallback 4)\n"
 *  - \"poll_interval_us\": Poll interval in microseconds (default: 10)\n"
 *
 * Result:\n"
 *  - \"shadow_db_controller_daemon\": ShadowDbControllerDaemon*\n"
 */
class ShadowDbControllerTask : public AdminSetupTask {
private:
    uint16_t default_qid_;
    uint32_t default_doorbell_stride_;
    uint32_t default_poll_interval_us_;

public:
    ShadowDbControllerTask(uint16_t qid = 1,
                           uint32_t doorbell_stride = 0,
                           uint32_t poll_interval_us = 10)
        : default_qid_(qid)
        , default_doorbell_stride_(doorbell_stride)
        , default_poll_interval_us_(poll_interval_us) {}

    std::string get_name() const override { return "ShadowDbController"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief Host DBC daemon launch task (Module 55.3)
 *
 * Launches the DBC shadow-buffer daemon (standard or realtime) that mirrors shadow
 * doorbell writes into MMIO doorbells.
 *
 * Args:
 *   - "daemon_mode": "standard" (default) or "realtime"
 *   - "shadow_doorbell_buffer": ShadowDoorbellBuffer* (required)
 *   - "queue_id": Queue identifier (default: 1)
 *   - "device_path": NVMe character device (default: /dev/nvme0)
 *
 * Result:
 *   - "host_dbc_daemon": DbcDaemonHandle* (contains PID + mode)
 */
class HostDbcDaemonTask : public AdminSetupTask {
private:
    std::string default_mode_;
    std::string default_device_path_;
    uint16_t default_queue_id_;

public:
    HostDbcDaemonTask(std::string mode = "standard",
                      std::string device_path = "/dev/nvme0",
                      uint16_t queue_id = 1)
        : default_mode_(std::move(mode))
        , default_device_path_(std::move(device_path))
        , default_queue_id_(queue_id) {}

    std::string get_name() const override { return "HostDbcDaemon"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

/**
 * @brief DBC daemon task (alias for HostDbcDaemonTask)
 *
 * Backward-compatible shim that starts the same DBC shadow-buffer daemon as
 * HostDbcDaemonTask. Kept to avoid breaking existing test harnesses.
 *
 * Args:
 *   - "nvme_device": NvmeDevice* from previous task (required)
 *   - "mode": "shadow" or "host_daemon" (default: "shadow")
 *
 * Result:
 *   - "dbc_daemon": void* (daemon handle)
 *   - "shadow_buffer": void* (shadow doorbell buffer)
 */
class DbcDaemonTask : public HostDbcDaemonTask {
public:
    using HostDbcDaemonTask::HostDbcDaemonTask;
    std::string get_name() const override { return "DbcDaemon"; }
    std::vector<SetupResult> setup(const SetupArgs& args) override;
};

// ============================================================================
// Setup Helper (Coordinator)
// ============================================================================

/**
 * @brief Coordinates multiple setup tasks with dependency management
 *
 * Manages task execution order, result storage, and cleanup.
 * Provides convenient access to setup results by name.
 *
 * Features:
 * - Automatic task ordering (admin tasks first)
 * - Result caching with type-safe access
 * - RAII cleanup of all resources
 * - Error reporting and rollback
 */
class SetupHelper {
private:
    std::vector<std::unique_ptr<SetupTask>> tasks_;
    std::map<std::string, SetupResult> results_;
    SetupArgs global_args_;
    bool setup_complete_{false};

public:
    const SetupArgs& get_global_args() const { return global_args_; }

public:
    SetupHelper() = default;
    ~SetupHelper() = default;

    // Non-copyable, move-only
    SetupHelper(const SetupHelper&) = delete;
    SetupHelper& operator=(const SetupHelper&) = delete;
    SetupHelper(SetupHelper&&) = default;
    SetupHelper& operator=(SetupHelper&&) = default;

    /**
     * @brief Add a setup task to the execution queue
     * @param task Task to add (transfers ownership)
     */
    void add_task(SetupTask* task) {
        tasks_.emplace_back(task);
    }

    /**
     * @brief Set global arguments available to all tasks
     * @param args Key-value arguments
     */
    void set_global_args(const SetupArgs& args) {
        global_args_ = args;
    }

    /**
     * @brief Add a single global argument
     * @param key Argument name
     * @param value Argument value
     */
    void set_arg(const std::string& key, const std::string& value) {
        global_args_[key] = value;
    }

    /**
     * @brief Execute all setup tasks in order
     * @return true if all tasks succeed, false otherwise
     *
     * Tasks are executed in order:
     * 1. Admin tasks first (require privileges)
     * 2. User tasks second (no special privileges)
     *
     * Results from earlier tasks are available to later tasks via args.
     */
    bool setup_all() {
        printf("=== SetupHelper: Executing %zu tasks ===\n", tasks_.size());

        // Sort tasks: admin first, then user
        std::stable_sort(tasks_.begin(), tasks_.end(),
            [](const auto& a, const auto& b) {
                return a->requires_admin() && !b->requires_admin();
            });

        // Execute tasks
        for (auto& task : tasks_) {
            printf("[SetupHelper] Executing task: %s (%s)\n",
                   task->get_name().c_str(),
                   task->requires_admin() ? "admin" : "user");

            // Merge global args with results from previous tasks
            SetupArgs task_args = global_args_;
            for (const auto& [name, result] : results_) {
                task_args[name] = std::to_string(reinterpret_cast<uintptr_t>(result.data));
            }

            // Execute task
            try {
                std::vector<SetupResult> results = task->setup(task_args);

                if (results.empty()) {
                    fprintf(stderr, "[SetupHelper] ERROR: Task %s failed (no results)\n",
                            task->get_name().c_str());
                    return false;
                }

                // Store all results from this task
                for (auto& result : results) {
                    if (result.data == nullptr) {
                        fprintf(stderr, "[SetupHelper] ERROR: Task %s returned null result '%s'\n",
                                task->get_name().c_str(), result.name.c_str());
                        return false;
                    }

                    printf("[SetupHelper] Task %s succeeded: %s = %p\n",
                           task->get_name().c_str(), result.name.c_str(), result.data);

                    results_[result.name] = std::move(result);
                }

            } catch (const std::exception& e) {
                fprintf(stderr, "[SetupHelper] ERROR: Task %s threw exception: %s\n",
                        task->get_name().c_str(), e.what());
                return false;
            }
        }

        setup_complete_ = true;
        printf("[SetupHelper] All %zu tasks completed successfully\n", tasks_.size());
        return true;
    }

    /**
     * @brief Get a setup result by name with type casting
     * @tparam T Result type (must be pointer type)
     * @param name Result identifier
     * @return Typed result pointer or nullptr if not found
     */
    template<typename T>
    T get(const std::string& name) const {
        auto it = results_.find(name);
        if (it == results_.end()) {
            fprintf(stderr, "[SetupHelper] WARNING: Result '%s' not found\n", name.c_str());
            return nullptr;
        }
        return it->second.get<T>();
    }

    /**
     * @brief Check if a result exists
     * @param name Result identifier
     * @return true if result exists
     */
    bool has(const std::string& name) const {
        return results_.find(name) != results_.end();
    }

    /**
     * @brief Check if setup was completed successfully
     * @return true if setup_all() succeeded
     */
    bool is_complete() const {
        return setup_complete_;
    }

    /**
     * @brief Print all setup results (for debugging)
     */
    void print_results() const {
        printf("\n=== SetupHelper Results ===\n");
        for (const auto& [name, result] : results_) {
            printf("  %-20s = %p\n", name.c_str(), result.data);
        }
        printf("==========================\n\n");
    }
};

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * @brief Load environment variables into SetupArgs
 * @param keys List of environment variable names to load
 * @return SetupArgs with loaded values
 */
inline SetupArgs load_env_args(const std::vector<std::string>& keys) {
    SetupArgs args;
    for (const auto& key : keys) {
        const char* value = std::getenv(key.c_str());
        if (value) {
            args[key] = value;
        }
    }
    return args;
}

/**
 * @brief Create standard NVMe test setup helper
 *
 * Sets up:
 * - NVMe device (from NVME_BDF env)
 * - Host memory pool
 *
 * @param pool_buf_size Buffer size for pool
 * @param pool_count Number of buffers in pool
 * @return Configured SetupHelper
 */
inline SetupHelper create_host_io_setup(size_t pool_buf_size = 4096, uint16_t pool_count = 16) {
    SetupHelper helper;

    // Load environment variables
    auto env_args = load_env_args({"NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE", "NVME_SLBA"});
    helper.set_global_args(env_args);

    // Add tasks
    helper.add_task(new VfioBindingTask());
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new HostMemoryFactoryTask(pool_buf_size, pool_count));

    return helper;
}

#ifdef __CUDACC__
/**
 * @brief Create CUDA host I/O test setup helper
 *
 * Sets up:
 * - NVMe device (from NVME_BDF env)
 * - CUDA host memory pool
 *
 * @param pool_buf_size Buffer size for pool
 * @param pool_count Number of buffers in pool
 * @return Configured SetupHelper
 */
inline SetupHelper create_cuda_host_io_setup(size_t pool_buf_size = 4096, uint16_t pool_count = 16) {
    SetupHelper helper;

    auto env_args = load_env_args({"NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE", "NVME_SLBA"});
    helper.set_global_args(env_args);

    helper.add_task(new VfioBindingTask());
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new CudaHostMemoryFactoryTask(pool_buf_size, pool_count));

    return helper;
}

/**
 * @brief Create CUDA GPU I/O test setup helper
 *
 * Sets up:
 * - NVMe device (from NVME_BDF env)
 * - CUDA GPU memory pool
 *
 * @param pool_buf_size Buffer size for pool
 * @param pool_count Number of buffers in pool
 * @return Configured SetupHelper
 */
inline SetupHelper create_cuda_gpu_io_setup(size_t pool_buf_size = 4096, uint16_t pool_count = 16) {
    SetupHelper helper;

    auto env_args = load_env_args({"NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE", "NVME_SLBA"});
    helper.set_global_args(env_args);

    helper.add_task(new VfioBindingTask());
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new CudaGpuMemoryFactoryTask(pool_buf_size, pool_count));

    return helper;
}
#endif // __CUDACC__
