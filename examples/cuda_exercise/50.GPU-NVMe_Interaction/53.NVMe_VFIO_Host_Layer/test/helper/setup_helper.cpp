/**
 * @file setup_helper.cpp
 * @brief Implementation of test setup helper tasks
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "setup_helper.h"
#include "vfio_utils.h"  // vfio_utils::ensure_vfio_binding, restore_original_driver
#include "doorbell/doorbell_daemon.h"   // Production nvme::DoorbellDaemon
#include "doorbell/dbc_setup.h"         // Production nvme::ShadowDoorbellBuffer
#include <chrono>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <vector>
#include <sys/wait.h>
#include <unistd.h>  // access()

#ifdef __CUDACC__
#include "mapper/mapper_gpu.h"  // nvme_setup_gpu_queue()
#endif

// ============================================================================
// Helper Functions
// ============================================================================

namespace {

/// Get string argument with fallback to default
std::string get_arg_str(const SetupArgs& args, const std::string& key, const std::string& def = "") {
    auto it = args.find(key);
    return (it != args.end()) ? it->second : def;
}

/// Get integer argument with fallback to default
template<typename T>
T get_arg_int(const SetupArgs& args, const std::string& key, T def) {
    auto it = args.find(key);
    if (it == args.end()) return def;

    if constexpr (std::is_same_v<T, uint64_t>) {
        return static_cast<T>(std::stoull(it->second));
    } else if constexpr (std::is_same_v<T, int64_t>) {
        return static_cast<T>(std::stoll(it->second));
    } else if constexpr (std::is_unsigned_v<T>) {
        return static_cast<T>(std::stoul(it->second));
    } else {
        return static_cast<T>(std::stoi(it->second));
    }
}

/// Get pointer argument from previous task result
template<typename T>
T get_arg_ptr(const SetupArgs& args, const std::string& key) {
    auto it = args.find(key);
    if (it == args.end()) {
        return nullptr;
    }
    uintptr_t ptr_val = std::stoull(it->second);
    return reinterpret_cast<T>(ptr_val);
}

} // anonymous namespace

// ============================================================================
// Host Memory Factory Task
// ============================================================================

std::vector<SetupResult> HostMemoryFactoryTask::setup(const SetupArgs& args) {
    // Get arguments
    size_t buf_size = get_arg_int<size_t>(args, "buf_size", default_buf_size_);
    uint16_t count = get_arg_int<uint16_t>(args, "count", default_count_);

    // Get NVMe device from previous task
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    if (!dev) {
        fprintf(stderr, "[HostMemoryFactoryTask] ERROR: nvme_device not provided\n");
        return {};
    }

    printf("[HostMemoryFactoryTask] Creating pool: buf_size=%zu, count=%u\n", buf_size, count);

    // Create host pool
    HostPool* pool = host_pool_create(dev, count);
    if (!pool) {
        fprintf(stderr, "[HostMemoryFactoryTask] ERROR: host_pool_create failed\n");
        return {};
    }

    printf("[HostMemoryFactoryTask] Pool created: %p (buf_size=%zu, cap=%u)\n",
           pool, pool->buf_size, pool->cap);

    // Return result with cleanup function
    std::vector<SetupResult> results;
    results.emplace_back("host_pool", pool, [](void* p) {
        if (p) {
            host_pool_destroy(static_cast<HostPool*>(p));
        }
    });
    return results;
}

// ============================================================================
// CUDA Host Memory Factory Task
// ============================================================================

#ifdef __CUDACC__
std::vector<SetupResult> CudaHostMemoryFactoryTask::setup(const SetupArgs& args) {
    // Get arguments
    size_t buf_size = get_arg_int<size_t>(args, "buf_size", default_buf_size_);
    uint16_t count = get_arg_int<uint16_t>(args, "count", default_count_);

    // Get NVMe device from previous task
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    if (!dev) {
        fprintf(stderr, "[CudaHostMemoryFactoryTask] ERROR: nvme_device not provided\n");
        return {};
    }

    printf("[CudaHostMemoryFactoryTask] Creating CUDA host pool: buf_size=%zu, count=%u\n",
           buf_size, count);

    // Create CUDA host pool
    CudaHostPool* pool = cuda_host_pool_create(dev, buf_size, count);
    if (!pool) {
        fprintf(stderr, "[CudaHostMemoryFactoryTask] ERROR: cuda_host_pool_create failed\n");
        return {};
    }

    printf("[CudaHostMemoryFactoryTask] Pool created: %p (buf_size=%zu, cap=%u)\n",
           pool, pool->buf_size, pool->cap);

    // Return result with cleanup function
    std::vector<SetupResult> results;
    results.emplace_back("cuda_host_pool", pool, [](void* p) {
        if (p) {
            cuda_host_pool_destroy(static_cast<CudaHostPool*>(p));
        }
    });
    return results;
}

// ============================================================================
// CUDA GPU Memory Factory Task
// ============================================================================

std::vector<SetupResult> CudaGpuMemoryFactoryTask::setup(const SetupArgs& args) {
    // Get arguments
    size_t buf_size = get_arg_int<size_t>(args, "buf_size", default_buf_size_);
    uint16_t count = get_arg_int<uint16_t>(args, "count", default_count_);

    // Get NVMe device from previous task
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    if (!dev) {
        fprintf(stderr, "[CudaGpuMemoryFactoryTask] ERROR: nvme_device not provided\n");
        return {};
    }

    printf("[CudaGpuMemoryFactoryTask] Creating CUDA GPU pool: buf_size=%zu, count=%u\n",
           buf_size, count);

    // Create CUDA GPU pool
    CudaGpuPool* pool = cuda_gpu_pool_create(dev, buf_size, count);
    if (!pool) {
        fprintf(stderr, "[CudaGpuMemoryFactoryTask] ERROR: cuda_gpu_pool_create failed\n");
        return {};
    }

    printf("[CudaGpuMemoryFactoryTask] Pool created: %p (buf_size=%zu, cap=%u)\n",
           pool, pool->buf_size, pool->cap);

    // Return result with cleanup function
    std::vector<SetupResult> results;
    results.emplace_back("cuda_gpu_pool", pool, [](void* p) {
        if (p) {
            cuda_gpu_pool_destroy(static_cast<CudaGpuPool*>(p));
        }
    });
    return results;
}
#endif // __CUDACC__

// ============================================================================
// NVMe Setup Task
// ============================================================================

std::vector<SetupResult> VfioBindingTask::setup(const SetupArgs& args) {
    std::string bdf = get_arg_str(args, "bdf", default_bdf_);
    if (bdf.empty()) {
        bdf = get_arg_str(args, "NVME_BDF", "");
    }

    if (bdf.empty()) {
        fprintf(stderr, "[VfioBindingTask] ERROR: BDF not provided (set 'bdf' arg or NVME_BDF env)\n");
        return {};
    }

    bool bound_by_helper = false;
    std::string error;
    if (!vfio_utils::ensure_vfio_binding(bdf, bound_by_helper, error)) {
        fprintf(stderr, "[VfioBindingTask] ERROR: %s\n", error.c_str());
        return {};
    }

    printf("[VfioBindingTask] %s is bound to vfio-pci (bound_by_helper=%d)\n",
           bdf.c_str(), bound_by_helper);

    auto* info = new VfioBindingInfo{bdf, bound_by_helper};

    auto cleanup_fn = [](void* ptr) {
        auto* info = static_cast<VfioBindingInfo*>(ptr);
        if (!info) {
            return;
        }
        if (info->bound_by_helper) {
            printf("[VfioBindingTask] Restoring %s to original driver\n",
                   info->bdf.c_str());
        }
        vfio_utils::restore_original_driver(info->bdf, info->bound_by_helper);
        delete info;
    };

    std::vector<SetupResult> results;
    results.emplace_back("vfio_binding", info, cleanup_fn);
    return results;
}

std::vector<SetupResult> NvmeSetupTask::setup(const SetupArgs& args) {
    // Get arguments with environment variable fallback
    std::string bdf = get_arg_str(args, "bdf", default_bdf_);
    if (bdf.empty()) {
        bdf = get_arg_str(args, "NVME_BDF", "");
    }

    if (bdf.empty()) {
        fprintf(stderr, "[NvmeSetupTask] ERROR: BDF not provided (set 'bdf' arg or NVME_BDF env)\n");
        return {};
    }

    uint16_t sq_depth = get_arg_int<uint16_t>(args, "sq_depth", default_sq_depth_);
    uint16_t cq_depth = get_arg_int<uint16_t>(args, "cq_depth", default_cq_depth_);
    uint32_t lba_size = get_arg_int<uint32_t>(args, "lba_size", default_lba_size_);

    // Override with environment if available
    if (args.find("NVME_LBA_SIZE") != args.end()) {
        lba_size = get_arg_int<uint32_t>(args, "NVME_LBA_SIZE", lba_size);
    }

    bool bound_by_helper = false;
    std::string vfio_err;
    if (!vfio_utils::ensure_vfio_binding(bdf, bound_by_helper, vfio_err)) {
        fprintf(stderr, "[NvmeSetupTask] ERROR: %s\n", vfio_err.c_str());
        fprintf(stderr, "[NvmeSetupTask] Hint: Run scripts/sudo_setup/setup_sudo_nopasswd.sh to install helper scripts.\n");
        return {};
    }

    printf("[NvmeSetupTask] Opening NVMe device: %s\n", bdf.c_str());
    printf("[NvmeSetupTask]   SQ depth: %u, CQ depth: %u, LBA size: %u\n",
           sq_depth, cq_depth, lba_size);

    // Open NVMe device with item_size = 8 LBAs (4096 bytes for 512B LBA size)
    // This ensures buffers are large enough for multi-LBA transfers
    const uint32_t item_size_bytes = lba_size * 8;  // 8 LBAs per transfer
    NvmeDevice* dev = nvme_open(bdf.c_str(), sq_depth, cq_depth, item_size_bytes);
    if (!dev) {
        fprintf(stderr, "[NvmeSetupTask] ERROR: nvme_open failed for %s\n", bdf.c_str());
        fprintf(stderr, "[NvmeSetupTask] Ensure VFIO is configured:\n");
        fprintf(stderr, "[NvmeSetupTask]   sudo ./scripts/setup_vfio_test_env.sh\n");
        return {};
    }

    printf("[NvmeSetupTask] Device opened successfully: %p\n", dev);

    // Setup host queue (modern API replaces nvme_get_iosq/iocq)
    NvmeQueueStruct* queue_struct = new NvmeQueueStruct();
    if (nvme_setup_host_queue(dev, bdf.c_str(), queue_struct) != 0) {
        fprintf(stderr, "[NvmeSetupTask] ERROR: Failed to setup host queue\n");
        delete queue_struct;
        nvme_close(dev);
        return {};
    }

    printf("[NvmeSetupTask] Host queue setup:\n");
    printf("[NvmeSetupTask]   Queue: %p (SQ=%p, CQ=%p)\n",
           queue_struct, queue_struct->sq_base, queue_struct->cq_base);

    // Get device properties
    uint32_t page_size = nvme_get_page_size(dev);
    uint32_t dev_lba_size = nvme_get_lba_size(dev);
    ItemSize item_size = nvme_get_item_size(dev);

    printf("[NvmeSetupTask] Device properties:\n");
    printf("[NvmeSetupTask]   Page size: %u bytes\n", page_size);
    printf("[NvmeSetupTask]   LBA size: %u bytes\n", dev_lba_size);
    printf("[NvmeSetupTask]   Item size: %u bytes (%u LBAs)\n",
           item_size.total_size, item_size.lba_count);

    // Create cleanup function for device (cleans up both device and queue_struct)
    auto device_cleanup_fn = [dev, queue_struct, bdf, bound_by_helper](void*) {
        // nvme_close() handles command pool cleanup automatically via nvme_cleanup_host_queue()
        if (dev) {
            nvme_close(dev);  // This calls nvme_cleanup_host_queue() internally
        }
        // Delete the queue wrapper struct itself (command pools already cleaned by nvme_close)
        if (queue_struct) {
            delete queue_struct;
        }
        vfio_utils::restore_original_driver(bdf, bound_by_helper);
    };

    // No-op cleanup for queue_struct aliases (actual cleanup happens in device cleanup)
    auto noop_cleanup_fn = [](void*) {};

    // Return three results: device, iosq_struct, iocq_struct
    // Note: iosq_struct and iocq_struct both point to the same queue_struct
    // because the modern API uses a single structure for both SQ and CQ
    std::vector<SetupResult> results;
    results.emplace_back("nvme_device", dev, device_cleanup_fn);
    results.emplace_back("iosq_struct", queue_struct, noop_cleanup_fn);
    results.emplace_back("iocq_struct", queue_struct, noop_cleanup_fn);

    return results;
}

// ============================================================================
// Additional Setup Task Implementations
// ============================================================================

// ----------------------------------------------------------------------------
// Helper Structures
// ----------------------------------------------------------------------------

/**
 * @brief Composite result from NvmeSetupTask
 *
 * Stores both device and queue struct for easy access by tests
 */
struct NvmeSetupResult {
    NvmeDevice* device;
    NvmeQueueStruct* queue_struct;

    NvmeSetupResult(NvmeDevice* d, NvmeQueueStruct* q)
        : device(d), queue_struct(q) {}
};

// StatCollector is now defined in setup_helper.h

// ----------------------------------------------------------------------------
// TestFileSetupTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> TestFileSetupTask::setup(const SetupArgs& args) {
    std::string file_path = get_arg_str(args, "file_path", default_file_path_);
    size_t size_mb = get_arg_int<size_t>(args, "file_size_mb", default_size_mb_);
    std::string pattern = get_arg_str(args, "pattern_type", default_pattern_);

    printf("[TestFileSetupTask] Creating test file: %s (%zu MB, pattern: %s)\n",
           file_path.c_str(), size_mb, pattern.c_str());

    // Create file
    FILE* fp = fopen(file_path.c_str(), "wb");
    if (!fp) {
        fprintf(stderr, "[TestFileSetupTask] ERROR: Failed to create file: %s\n",
                file_path.c_str());
        return {};
    }

    // Fill with pattern
    const size_t buf_size = 1024 * 1024;  // 1MB buffer
    uint8_t* buffer = new uint8_t[buf_size];

    size_t bytes_written = 0;
    size_t total_bytes = size_mb * 1024 * 1024;

    while (bytes_written < total_bytes) {
        size_t to_write = std::min(buf_size, total_bytes - bytes_written);

        // Fill buffer with pattern
        if (pattern == "sequential" || pattern == "0") {
            for (size_t i = 0; i < to_write; i++) {
                buffer[i] = static_cast<uint8_t>((bytes_written + i) & 0xFF);
            }
        } else if (pattern == "random" || pattern == "1") {
            for (size_t i = 0; i < to_write; i++) {
                buffer[i] = static_cast<uint8_t>(rand() & 0xFF);
            }
        } else {  // zeros or default
            memset(buffer, 0, to_write);
        }

        size_t written = fwrite(buffer, 1, to_write, fp);
        if (written != to_write) {
            fprintf(stderr, "[TestFileSetupTask] ERROR: Write failed\n");
            delete[] buffer;
            fclose(fp);
            return {};
        }

        bytes_written += written;
    }

    delete[] buffer;
    fsync(fileno(fp));
    fclose(fp);

    printf("[TestFileSetupTask] File created successfully: %zu bytes\n", bytes_written);

    // Store file path and size
    auto* path_str = new std::string(file_path);
    auto* size_ptr = new size_t(bytes_written);

    auto cleanup_fn = [path_str, size_ptr](void*) {
        delete path_str;
        delete size_ptr;
    };

    std::vector<SetupResult> results;
    results.emplace_back("test_file_path", path_str, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// StatCollectorTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> StatCollectorTask::setup(const SetupArgs& args) {
    std::string metrics = get_arg_str(args, "metrics", default_metrics_);

    printf("[StatCollectorTask] Setting up stat collector (metrics: %s)\n",
           metrics.c_str());

    auto* collector = new StatCollector();
    collector->metrics = metrics;
    collector->start();

    auto cleanup_fn = [](void* p) {
        auto* sc = static_cast<StatCollector*>(p);
        sc->stop();
        sc->print_summary();
        delete sc;
    };

    std::vector<SetupResult> results;
    results.emplace_back("stat_collector", collector, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// GpuDetectionTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> GpuDetectionTask::setup(const SetupArgs& args) {
    printf("[GpuDetectionTask] Detecting GPUs...\n");

#ifdef __CUDACC__
    // Use cuda_utils.h helpers for cleaner code
    int gpu_count = get_device_count();

    if (gpu_count == 0) {
        fprintf(stderr, "[GpuDetectionTask] ERROR: No CUDA GPUs found\n");
        return {};
    }

    printf("[GpuDetectionTask] Found %d GPU(s)\n", gpu_count);

    // Select first GPU with sufficient compute capability
    int selected_gpu = 0;
    for (int i = 0; i < gpu_count; i++) {
        cudaDeviceProp prop;
        if (!get_device_props(prop, i)) {
            fprintf(stderr, "[GpuDetectionTask] WARNING: Failed to query GPU %d\n", i);
            continue;
        }

        printf("[GpuDetectionTask] GPU %d: %s (Compute %d.%d)\n",
               i, prop.name, prop.major, prop.minor);

        if (i == 0) {
            selected_gpu = i;
        }
    }

    printf("[GpuDetectionTask] Selected GPU: %d\n", selected_gpu);

    auto* count_ptr = new int(gpu_count);
    auto* selected_ptr = new int(selected_gpu);

    auto cleanup_fn = [count_ptr, selected_ptr](void*) {
        delete count_ptr;
        delete selected_ptr;
    };

    std::vector<SetupResult> results;
    results.emplace_back("gpu_count", count_ptr, cleanup_fn);
    return results;
#else
    fprintf(stderr, "[GpuDetectionTask] ERROR: CUDA not available\n");
    return {};
#endif
}

// ----------------------------------------------------------------------------
// NvmeDetectionTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> NvmeDetectionTask::setup(const SetupArgs& args) {
    printf("[NvmeDetectionTask] Detecting NVMe devices...\n");

    // For now, use environment variable or return default
    const char* bdf = std::getenv("NVME_BDF");
    if (!bdf) {
        fprintf(stderr, "[NvmeDetectionTask] ERROR: NVME_BDF not set\n");
        return {};
    }

    printf("[NvmeDetectionTask] Found device: %s\n", bdf);

    auto* count_ptr = new int(1);
    auto* bdf_ptr = new std::string(bdf);

    auto cleanup_fn = [count_ptr, bdf_ptr](void*) {
        delete count_ptr;
        delete bdf_ptr;
    };

    std::vector<SetupResult> results;
    results.emplace_back("nvme_count", count_ptr, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// WarmupTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> WarmupTask::setup(const SetupArgs& args) {
    int iterations = get_arg_int<int>(args, "warmup_iterations", default_iterations_);
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");

    if (!dev) {
        fprintf(stderr, "[WarmupTask] ERROR: NvmeDevice not found in args\n");
        return {};
    }

    printf("[WarmupTask] Warming up (%d iterations)...\n", iterations);

    // Perform warmup iterations (dummy operations)
    for (int i = 0; i < iterations; i++) {
        // Just access device properties to warm up
        nvme_get_page_size(dev);
        nvme_get_lba_size(dev);
    }

    printf("[WarmupTask] Warmup complete\n");

    auto* done = new bool(true);

    auto cleanup_fn = [](void* p) {
        delete static_cast<bool*>(p);
    };

    std::vector<SetupResult> results;
    results.emplace_back("warmup_complete", done, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// ConsecutiveBufferTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> ConsecutiveBufferTask::setup(const SetupArgs& args) {
    size_t size = get_arg_int<size_t>(args, "buffer_size", default_size_);
    std::string mem_type = get_arg_str(args, "memory_type", default_mem_type_);
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");

    if (!dev) {
        fprintf(stderr, "[ConsecutiveBufferTask] ERROR: NvmeDevice not found\n");
        return {};
    }

    printf("[ConsecutiveBufferTask] Allocating %zu bytes (%s)\n",
           size, mem_type.c_str());

    Buffer* buf = nullptr;

    if (mem_type == "HOST") {
        buf = host_create_consecutive_buffer(size);  // Uses global mapper
    }
#ifdef __CUDACC__
    else if (mem_type == "CUDA_HOST") {
        buf = cuda_host_create_pinned_consecutive_buffer(size);
    } else if (mem_type == "CUDA_GPU") {
        buf = cuda_gpu_create_device_consecutive_buffer(size);
        if (!buf || buf->iova == 0) {
            fprintf(stderr, "[ConsecutiveBufferTask] WARNING: GPU buffer allocated without IOVA (P2P mapping unavailable)\n");
        }
    }
#endif
    else {
        fprintf(stderr, "[ConsecutiveBufferTask] ERROR: Unknown memory type: %s\n",
                mem_type.c_str());
        return {};
    }

    if (!buf) {
        fprintf(stderr, "[ConsecutiveBufferTask] ERROR: Buffer allocation failed\n");
        return {};
    }

    printf("[ConsecutiveBufferTask] Buffer allocated: %p (iova=0x%lx)\n",
           buf->addr, buf->iova);

    auto cleanup_fn = [mem_type](void* p) {
        Buffer* b = static_cast<Buffer*>(p);
        if (mem_type == "HOST") {
            host_buffer_destroy(b);
        }
#ifdef __CUDACC__
        else if (mem_type == "CUDA_HOST") {
            cuda_host_buffer_destroy(b);
        } else if (mem_type == "CUDA_GPU") {
            cuda_gpu_buffer_destroy(b);
        }
#endif
    };

    std::vector<SetupResult> results;
    results.emplace_back("consecutive_buffer", buf, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// MultiQueueSetupTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> MultiQueueSetupTask::setup(const SetupArgs& args) {
    int num_queues = get_arg_int<int>(args, "num_queues", default_num_queues_);
    uint16_t sq_depth = get_arg_int<uint16_t>(args, "sq_depth", default_sq_depth_);
    uint16_t cq_depth = get_arg_int<uint16_t>(args, "cq_depth", default_cq_depth_);
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");

    if (!dev) {
        fprintf(stderr, "[MultiQueueSetupTask] ERROR: NvmeDevice not found\n");
        return {};
    }

    printf("[MultiQueueSetupTask] Creating %d queue pairs (depth: SQ=%u, CQ=%u)\n",
           num_queues, sq_depth, cq_depth);

    // For now, just store queue count (actual queue creation would need NVMe API)
    auto* count_ptr = new int(num_queues);

    printf("[MultiQueueSetupTask] Queue setup complete\n");

    auto cleanup_fn = [](void* p) {
        delete static_cast<int*>(p);
    };

    std::vector<SetupResult> results;
    results.emplace_back("num_queues", count_ptr, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// GpuP2PSetupTask Implementation
// ----------------------------------------------------------------------------

#ifdef __CUDACC__
std::vector<SetupResult> GpuP2PSetupTask::setup(const SetupArgs& args) {
    int gpu_id = get_arg_int<int>(args, "gpu_id", default_gpu_id_);
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    std::string nvme_bdf = get_arg_str(args, "bdf", "");
    if (nvme_bdf.empty()) {
        nvme_bdf = get_arg_str(args, "NVME_BDF", "");
    }

    if (!dev) {
        fprintf(stderr, "[GpuP2PSetupTask] ERROR: NvmeDevice not found\n");
        return {};
    }

    if (nvme_bdf.empty()) {
        fprintf(stderr, "[GpuP2PSetupTask] ERROR: NVME_BDF not specified\n");
        return {};
    }

    printf("[GpuP2PSetupTask] Setting up P2P for GPU %d with NVMe %s\n",
           gpu_id, nvme_bdf.c_str());

    // Set active GPU using cuda_utils.h helper
    if (!set_device(gpu_id)) {
        fprintf(stderr, "[GpuP2PSetupTask] ERROR: Failed to set GPU %d\n", gpu_id);
        return {};
    }

    // Create GPU queue structure
    auto* gpu_queue = new NvmeQueueStruct();

    // Check if P2P kernel driver is available for full P2P functionality
    bool p2p_available = (access("/dev/gpu_p2p_nvme", F_OK) == 0);

    if (p2p_available) {
        // Map NVMe queues and doorbells to GPU via P2P driver
        int rc = nvme_setup_gpu_queue(dev, nvme_bdf.c_str(), gpu_queue);
        if (rc != 0) {
            fprintf(stderr, "[GpuP2PSetupTask] ERROR: nvme_setup_gpu_queue failed: %d\n", rc);
            delete gpu_queue;
            return {};
        }
        printf("[GpuP2PSetupTask] P2P mapping complete:\n");
        printf("  SQ GPU VA:   %p (depth=%u)\n", gpu_queue->sq_base, gpu_queue->sq_depth);
        printf("  CQ GPU VA:   %p (depth=%u)\n", gpu_queue->cq_base, gpu_queue->cq_depth);
    } else {
        // P2P driver not available - create local GPU queue for testing (no P2P DMA)
        fprintf(stderr, "[GpuP2PSetupTask] WARNING: /dev/gpu_p2p_nvme not found\n");
        fprintf(stderr, "  Creating fallback GPU queue (no actual P2P DMA)\n");
        fprintf(stderr, "  For real P2P NVMe:\n");
        fprintf(stderr, "  1. System P2P configuration: sudo ./scripts/sudo_setup/gpu_p2p_setup_task.sh\n");
        fprintf(stderr, "  2. Verify: sudo ./scripts/check_p2p_capability.sh\n");

        // Allocate fallback GPU queue memory
        const uint16_t sq_depth = 64;
        const uint16_t cq_depth = 64;

        cudaError_t err;
        err = cudaMalloc(&gpu_queue->sq_base, sq_depth * sizeof(NvmeCmd));
        if (err != cudaSuccess) {
            fprintf(stderr, "[GpuP2PSetupTask] ERROR: cudaMalloc SQ failed: %s\n", cudaGetErrorString(err));
            delete gpu_queue;
            return {};
        }

        err = cudaMalloc(&gpu_queue->cq_base, cq_depth * sizeof(NvmeCqe));
        if (err != cudaSuccess) {
            fprintf(stderr, "[GpuP2PSetupTask] ERROR: cudaMalloc CQ failed: %s\n", cudaGetErrorString(err));
            cudaFree(gpu_queue->sq_base);
            delete gpu_queue;
            return {};
        }

        // Initialize queue metadata
        gpu_queue->sq_depth = sq_depth;
        gpu_queue->cq_depth = cq_depth;
        gpu_queue->qid = 1;
        gpu_queue->nsid = 1;

        printf("[GpuP2PSetupTask] Fallback GPU queue created:\n");
        printf("  SQ GPU VA:   %p (depth=%u)\n", gpu_queue->sq_base, gpu_queue->sq_depth);
        printf("  CQ GPU VA:   %p (depth=%u)\n", gpu_queue->cq_base, gpu_queue->cq_depth);
    }
    // Note: doorbell addresses managed through doorbell strategy objects

    auto cleanup_fn = [p2p_available](void* p) {
        auto* q = static_cast<NvmeQueueStruct*>(p);
        if (!q) return;

        // If we created fallback GPU queues, free them
        if (!p2p_available) {
            if (q->sq_base) cudaFree(q->sq_base);
            if (q->cq_base) cudaFree(q->cq_base);
        }
        // GPU queue cleanup (P2P unmapping would be done by kernel driver on close)
        delete q;
    };

    auto* p2p_enabled = new bool(p2p_available);

    std::vector<SetupResult> results;
    results.emplace_back("gpu_queue", gpu_queue, cleanup_fn);
    results.emplace_back("p2p_enabled", p2p_enabled, [](void* ptr) {
        delete static_cast<bool*>(ptr);
    });
    return results;
}

// ----------------------------------------------------------------------------
// GdsMemoryFactoryTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> GdsMemoryFactoryTask::setup(const SetupArgs& args) {
    size_t buf_size = get_arg_int<size_t>(args, "buf_size", default_buf_size_);
    uint16_t count = get_arg_int<uint16_t>(args, "count", default_count_);
    int gpu_id = get_arg_int<int>(args, "gpu_id", default_gpu_id_);

    printf("[GdsMemoryFactoryTask] Setting up GDS buffers (size=%zu, count=%u, gpu=%d)\n",
           buf_size, count, gpu_id);

    // Set active GPU using cuda_utils.h helper
    if (!set_device(gpu_id)) {
        fprintf(stderr, "[GdsMemoryFactoryTask] ERROR: Failed to set GPU %d\n", gpu_id);
        return {};
    }

    struct GdsBufferSet {
        std::vector<void*> buffers;
    };

    auto* gds_handle = new GdsBufferSet();
    gds_handle->buffers.reserve(count);

    for (uint16_t i = 0; i < count; ++i) {
        void* ptr = nullptr;
        cudaError_t err = cudaHostAlloc(&ptr, buf_size, cudaHostAllocPortable);
        if (err != cudaSuccess || !ptr) {
            fprintf(stderr, "[GdsMemoryFactoryTask] cudaHostAlloc failed at index %u: %s\n",
                    i, cudaGetErrorString(err));
            // Cleanup already-allocated buffers
            for (void* b : gds_handle->buffers) {
                cudaFreeHost(b);
            }
            delete gds_handle;
            return {};
        }
        gds_handle->buffers.push_back(ptr);
    }

    printf("[GdsMemoryFactoryTask] GDS buffers setup complete (%zu pinned buffers)\n",
           gds_handle->buffers.size());

    auto cleanup_fn = [](void* p) {
        auto* set = static_cast<GdsBufferSet*>(p);
        if (set) {
            for (void* b : set->buffers) {
                cudaFreeHost(b);
            }
            delete set;
        }
    };

    std::vector<SetupResult> results;
    results.emplace_back("gds_buffers", gds_handle, cleanup_fn);
    return results;
}
#endif // __CUDACC__

// ----------------------------------------------------------------------------
// Helper for shadow doorbell buffer allocation
// ----------------------------------------------------------------------------

namespace {

// Wrapper around production nvme::allocate_shadow_doorbell_buffer() with label logging
ShadowDoorbellBuffer* allocate_shadow_buffer(NvmeDevice* dev,
                                             uint16_t queue_count,
                                             const char* label) {
    if (!dev) {
        fprintf(stderr, "[DbcShadowBufferTask] ERROR: NvmeDevice null for %s\n", label);
        return nullptr;
    }

    const size_t page_size = nvme_get_page_size(dev);

    // Use production library function
    auto* buffer = nvme::allocate_shadow_doorbell_buffer(queue_count, page_size);
    if (buffer) {
        printf("[DbcShadowBufferTask] Allocated %s: %zu bytes (queues=%u, iova=0x%lx)\n",
               label, buffer->bytes, buffer->queue_count,
               static_cast<unsigned long>(buffer->iova));
    } else {
        fprintf(stderr, "[DbcShadowBufferTask] ERROR: Failed to allocate %s\n", label);
    }

    return buffer;
}

// Wrapper around production nvme::free_shadow_doorbell_buffer()
void free_shadow_buffer(ShadowDoorbellBuffer* buffer) {
    nvme::free_shadow_doorbell_buffer(buffer);
}

}  // namespace

// ----------------------------------------------------------------------------
// HostDoorbellDaemonTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> HostDoorbellDaemonTask::setup(const SetupArgs& args) {
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    if (!dev) {
        fprintf(stderr, "[HostDoorbellDaemonTask] ERROR: NvmeDevice not found\n");
        return {};
    }

    Queue* iosq = nvme_get_iosq(dev);
    if (!iosq || !iosq->db) {
        fprintf(stderr, "[HostDoorbellDaemonTask] ERROR: IO submission queue doorbell unavailable\n");
        return {};
    }

    uint32_t poll_us = get_arg_int<uint32_t>(args, "poll_interval_us", default_poll_interval_us_);
    auto* daemon = new nvme::DoorbellDaemon(iosq, std::chrono::microseconds(poll_us));
    daemon->start();

    printf("[HostDoorbellDaemonTask] Host doorbell daemon started (poll=%u us)\n", poll_us);

    auto cleanup_fn = [](void* ptr) {
        auto* daemon_ptr = static_cast<nvme::DoorbellDaemon*>(ptr);
        if (daemon_ptr) {
            daemon_ptr->stop();
            delete daemon_ptr;
        }
    };

    std::vector<SetupResult> results;
    results.emplace_back("host_doorbell_daemon", daemon, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// DbcShadowBufferTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> DbcShadowBufferTask::setup(const SetupArgs& args) {
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    if (!dev) {
        fprintf(stderr, "[DbcShadowBufferTask] ERROR: NvmeDevice not found\n");
        return {};
    }

    uint16_t queue_count = get_arg_int<uint16_t>(args, "queue_count", default_queue_count_);
    bool use_eventidx = get_arg_int<int>(args, "use_eventidx", default_use_eventidx_ ? 1 : 0) != 0;
    uint16_t qid = get_arg_int<uint16_t>(args, "queue_id", default_queue_id_);

    auto* shadow = allocate_shadow_buffer(dev, queue_count, "shadow_doorbell_buffer");
    if (!shadow) {
        return {};
    }

    // Prime shadow entries with current queue positions when available to avoid spurious MMIO rings
    auto* iosq_struct = get_arg_ptr<NvmeQueueStruct*>(args, "iosq_struct");
    auto* iocq_struct = get_arg_ptr<NvmeQueueStruct*>(args, "iocq_struct");
    if (iosq_struct && iocq_struct && shadow->host_ptr &&
        static_cast<size_t>(qid) < static_cast<size_t>(queue_count)) {
        const size_t sq_index = 2 * static_cast<size_t>(qid);
        const size_t cq_index = sq_index + 1;
        shadow->host_ptr[sq_index] = static_cast<uint32_t>(iosq_struct->sq_tail % iosq_struct->sq_depth);
        shadow->host_ptr[cq_index] = static_cast<uint32_t>(iocq_struct->cq_head % iocq_struct->cq_depth);
        printf("[DbcShadowBufferTask] Initialized shadow DB (qid=%u) SQ=%u CQ=%u\n",
               qid, shadow->host_ptr[sq_index], shadow->host_ptr[cq_index]);
    }

    std::vector<SetupResult> results;
    results.emplace_back("shadow_doorbell_buffer", shadow, [](void* ptr) {
        free_shadow_buffer(static_cast<ShadowDoorbellBuffer*>(ptr));
    });

    if (use_eventidx) {
        auto* eventidx = allocate_shadow_buffer(dev, queue_count, "eventidx_buffer");
        if (!eventidx) {
            // Cleanup shadow buffer before returning failure
            free_shadow_buffer(shadow);
            return {};
        }
        results.emplace_back("eventidx_buffer", eventidx, [](void* ptr) {
            free_shadow_buffer(static_cast<ShadowDoorbellBuffer*>(ptr));
        });
    }

    return results;
}

// ----------------------------------------------------------------------------
// HostDbcDaemonTask Implementation
// ----------------------------------------------------------------------------

namespace {

struct DbcDaemonHandle {
    pid_t pid;
    std::string mode;
};

bool spawn_daemon(const std::string& binary,
                  const std::vector<std::string>& args,
                  pid_t& child_pid) {
    std::vector<const char*> argv;
    argv.push_back(binary.c_str());
    for (const auto& arg : args) {
        argv.push_back(arg.c_str());
    }
    argv.push_back(nullptr);

    pid_t pid = fork();
    if (pid < 0) {
        perror("[HostDbcDaemonTask] fork failed");
        return false;
    }
    if (pid == 0) {
        // Child process
        execv(binary.c_str(), const_cast<char* const*>(argv.data()));
        perror("[HostDbcDaemonTask] execv failed");
        _exit(127);
    }

    child_pid = pid;
    return true;
}

std::string resolve_daemon_binary(const std::string& binary_name) {
    const std::string candidates[] = {
        binary_name,
        "/usr/local/bin/" + binary_name,
        std::string("50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/daemon/") + binary_name,
    };
    for (const auto& path : candidates) {
        if (access(path.c_str(), X_OK) == 0) {
            return path;
        }
    }
    return {};
}

}  // namespace

std::vector<SetupResult> HostDbcDaemonTask::setup(const SetupArgs& args) {
    auto* shadow = get_arg_ptr<ShadowDoorbellBuffer*>(args, "shadow_doorbell_buffer");
    if (!shadow) {
        fprintf(stderr, "[HostDbcDaemonTask] ERROR: shadow_doorbell_buffer not found\n");
        return {};
    }

    const std::string mode = get_arg_str(args, "daemon_mode", default_mode_);
    const uint16_t queue_id = get_arg_int<uint16_t>(args, "queue_id", default_queue_id_);
    const std::string device_path = get_arg_str(args, "device_path", default_device_path_);

    const std::string binary_name =
        (mode == "realtime") ? "host_dbc_daemon_realtime" : "host_dbc_daemon";
    const std::string binary_path = resolve_daemon_binary(binary_name);
    if (binary_path.empty()) {
        fprintf(stderr, "[HostDbcDaemonTask] ERROR: Could not locate %s\n", binary_name.c_str());
        return {};
    }

    char shadow_arg[64];
    std::snprintf(shadow_arg, sizeof(shadow_arg), "%p", static_cast<void*>(shadow->host_ptr));

    char queue_arg[16];
    std::snprintf(queue_arg, sizeof(queue_arg), "%u", queue_id);

    std::vector<std::string> daemon_args = {
        "--device", device_path,
        "--shadow", shadow_arg,
        "--qid", queue_arg,
        "--poll-interval-us", "10",
    };

    if (mode == "realtime") {
        daemon_args.emplace_back("--priority");
        daemon_args.emplace_back("90");
    }

    pid_t pid = -1;
    if (!spawn_daemon(binary_path, daemon_args, pid)) {
        return {};
    }

    auto* handle = new DbcDaemonHandle{pid, mode};
    printf("[HostDbcDaemonTask] Started %s (pid=%d, shadow=%s)\n",
           binary_name.c_str(), pid, shadow_arg);

    auto cleanup_fn = [](void* ptr) {
        auto* h = static_cast<DbcDaemonHandle*>(ptr);
        if (!h) return;
        if (h->pid > 0) {
            printf("[HostDbcDaemonTask] Stopping daemon pid=%d\n", h->pid);
            kill(h->pid, SIGTERM);
            waitpid(h->pid, nullptr, 0);
        }
        delete h;
    };

    std::vector<SetupResult> results;
    results.emplace_back("host_dbc_daemon", handle, cleanup_fn);
    return results;
}

// ----------------------------------------------------------------------------
// DbcDaemonTask Implementation (alias wrapper)
// ----------------------------------------------------------------------------

std::vector<SetupResult> DbcDaemonTask::setup(const SetupArgs& args) {
    auto host_results = HostDbcDaemonTask::setup(args);
    if (host_results.empty()) {
        return {};
    }

    std::vector<SetupResult> results;
    for (auto& r : host_results) {
        results.emplace_back(std::move(r));
    }
    results.emplace_back("dbc_daemon", results.front().data, [](void*) {});  // Alias without cleanup
    return results;
}

// ----------------------------------------------------------------------------
// ShadowDbControllerTask Implementation
// ----------------------------------------------------------------------------

std::vector<SetupResult> ShadowDbControllerTask::setup(const SetupArgs& args) {
    auto* shadow = get_arg_ptr<ShadowDoorbellBuffer*>(args, "shadow_doorbell_buffer");
    NvmeDevice* dev = get_arg_ptr<NvmeDevice*>(args, "nvme_device");
    if (!shadow || !shadow->host_ptr) {
        fprintf(stderr, "[ShadowDbControllerTask] ERROR: shadow_doorbell_buffer not found\n");
        return {};
    }
    if (!dev) {
        fprintf(stderr, "[ShadowDbControllerTask] ERROR: NvmeDevice not found\n");
        return {};
    }

    const uint16_t qid = get_arg_int<uint16_t>(args, "qid", default_qid_);
    const uint32_t poll_us = get_arg_int<uint32_t>(args, "poll_interval_us", default_poll_interval_us_);
    uint32_t stride_bytes = get_arg_int<uint32_t>(args, "doorbell_stride", default_doorbell_stride_);
    if (stride_bytes == 0) {
        stride_bytes = 4;  // Default when CAP.DSTRD is unknown
    }

    Queue* iosq = nvme_get_iosq(dev);
    Queue* iocq = nvme_get_iocq(dev);
    if (!iosq || !iosq->db || !iocq || !iocq->db) {
        fprintf(stderr, "[ShadowDbControllerTask] ERROR: Missing MMIO doorbell pointers\n");
        return {};
    }

    auto* daemon = new nvme::ShadowDbControllerDaemon(
        shadow, iosq->db, iocq->db, qid, stride_bytes,
        std::chrono::microseconds(poll_us));
    daemon->start();

    printf("[ShadowDbControllerTask] Shadow DB controller started (qid=%u, poll=%u us)\n",
           qid, poll_us);

    auto cleanup_fn = [](void* ptr) {
        auto* daemon_ptr = static_cast<nvme::ShadowDbControllerDaemon*>(ptr);
        if (daemon_ptr) {
            daemon_ptr->stop();
            delete daemon_ptr;
        }
    };

    std::vector<SetupResult> results;
    results.emplace_back("shadow_db_controller_daemon", daemon, cleanup_fn);
    return results;
}
