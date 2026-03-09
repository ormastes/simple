/**
 * @file setup_helper_example.cpp
 * @brief Example demonstrating SetupHelper usage patterns
 *
 * This example shows different ways to use the SetupHelper system
 * for configuring NVMe I/O tests. It demonstrates:
 * - Manual task configuration
 * - Convenience factory functions
 * - Result access
 * - Resource cleanup
 *
 * Usage:
 *   export NVME_BDF="0000:41:00.0"
 *   export NVME_NSID="1"
 *   export NVME_LBA_SIZE="512"
 *   sudo -E ./setup_helper_example
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "setup_helper.h"
#include "io/host_io_host_mem.h"
#include <cstdio>

// ============================================================================
// Example 1: Manual Task Configuration
// ============================================================================

void example_manual_setup() {
    printf("\n╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Example 1: Manual Task Configuration                         ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    // Create setup helper
    SetupHelper helper;

    // Load environment variables
    auto env_args = load_env_args({"NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE"});
    helper.set_global_args(env_args);

    // Add tasks manually
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new HostMemoryFactoryTask(4096, 8));  // 8 buffers of 4KB each

    // Execute all tasks
    if (!helper.setup_all()) {
        fprintf(stderr, "Setup failed!\n");
        return;
    }

    // Access results
    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");

    printf("\nResults:\n");
    printf("  NVMe Device: %p\n", dev);
    printf("  Host Pool:   %p (cap=%u, buf_size=%zu)\n", pool, pool->cap, pool->buf_size);

    // Use resources (example: acquire and release buffer)
    printf("\nTesting buffer acquisition:\n");
    DmaBuf* buf = host_pool_acquire(pool);
    if (buf) {
        printf("  ✓ Buffer acquired: %p (iova=0x%lx, bytes=%zu)\n",
               buf->addr, buf->iova, buf->bytes);
        host_pool_release(pool, buf);
        printf("  ✓ Buffer released\n");
    }

    printf("\n✓ Example 1 complete (resources will be cleaned up automatically)\n");
    // Automatic cleanup when helper goes out of scope
}

// ============================================================================
// Example 2: Convenience Factory Function
// ============================================================================

void example_convenience_setup() {
    printf("\n╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Example 2: Convenience Factory Function                      ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    // Use convenience function (much simpler!)
    SetupHelper helper = create_host_io_setup(8192, 4);  // 4 buffers of 8KB each

    if (!helper.setup_all()) {
        fprintf(stderr, "Setup failed!\n");
        return;
    }

    // Access and use resources
    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");

    printf("\nConvenience setup completed:\n");
    printf("  NVMe Device: %p\n", dev);
    printf("  Host Pool:   %p (cap=%u, buf_size=%zu)\n", pool, pool->cap, pool->buf_size);

    printf("\n✓ Example 2 complete\n");
}

// ============================================================================
// Example 3: Custom Task Configuration
// ============================================================================

void example_custom_setup() {
    printf("\n╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Example 3: Custom Task Configuration                         ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    SetupHelper helper;

    // Set custom arguments (override environment)
    helper.set_arg("bdf", "0000:41:00.0");  // Explicit BDF
    helper.set_arg("sq_depth", "32");        // Custom queue depth
    helper.set_arg("cq_depth", "32");
    helper.set_arg("lba_size", "512");

    // Add tasks with custom settings
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new HostMemoryFactoryTask(16384, 2));  // 2 buffers of 16KB

    if (!helper.setup_all()) {
        fprintf(stderr, "Setup failed!\n");
        return;
    }

    // Print all results
    helper.print_results();

    printf("\n✓ Example 3 complete\n");
}

// ============================================================================
// Example 4: Multiple Memory Types (if CUDA available)
// ============================================================================

#ifdef __CUDACC__
void example_cuda_setup() {
    printf("\n╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Example 4: CUDA Memory Setup                                 ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    SetupHelper helper;

    // Load environment
    auto env_args = load_env_args({"NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE"});
    helper.set_global_args(env_args);

    // Add NVMe setup
    helper.add_task(new NvmeSetupTask());

    // Add multiple memory factories
    helper.add_task(new HostMemoryFactoryTask(4096, 8));
    helper.add_task(new CudaHostMemoryFactoryTask(4096, 8));
    helper.add_task(new CudaGpuMemoryFactoryTask(4096, 8));

    if (!helper.setup_all()) {
        fprintf(stderr, "Setup failed!\n");
        return;
    }

    // Access all pools
    HostPool* host_pool = helper.get<HostPool*>("host_pool");
    CudaHostPool* cuda_host_pool = helper.get<CudaHostPool*>("cuda_host_pool");
    CudaGpuPool* cuda_gpu_pool = helper.get<CudaGpuPool*>("cuda_gpu_pool");

    printf("\nMultiple memory types configured:\n");
    printf("  Host Pool:      %p (cap=%u)\n", host_pool, host_pool->cap);
    printf("  CUDA Host Pool: %p (cap=%u)\n", cuda_host_pool, cuda_host_pool->cap);
    printf("  CUDA GPU Pool:  %p (cap=%u)\n", cuda_gpu_pool, cuda_gpu_pool->cap);

    printf("\n✓ Example 4 complete\n");
}
#endif

// ============================================================================
// Example 5: Error Handling
// ============================================================================

void example_error_handling() {
    printf("\n╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Example 5: Error Handling                                    ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    SetupHelper helper;

    // Intentionally don't set BDF to trigger error
    helper.add_task(new NvmeSetupTask());

    printf("Attempting setup without BDF (should fail)...\n\n");

    if (!helper.setup_all()) {
        printf("\n✓ Error correctly detected and handled\n");
        printf("  Hint: Set NVME_BDF environment variable\n");
    } else {
        printf("\nUnexpected success!\n");
    }
}

// ============================================================================
// Example 6: Checking Results
// ============================================================================

void example_result_checking() {
    printf("\n╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Example 6: Result Checking                                   ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    SetupHelper helper = create_host_io_setup();

    if (!helper.setup_all()) {
        fprintf(stderr, "Setup failed!\n");
        return;
    }

    // Check if specific results exist
    printf("Checking for results:\n");
    printf("  nvme_device exists? %s\n", helper.has("nvme_device") ? "YES" : "NO");
    printf("  host_pool exists?   %s\n", helper.has("host_pool") ? "YES" : "NO");
    printf("  foo exists?         %s\n", helper.has("foo") ? "YES" : "NO");

    // Safe access with null check
    if (helper.has("nvme_device")) {
        NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
        printf("\nNVMe device properties:\n");
        printf("  Page size: %zu bytes\n", nvme_get_page_size(dev));
        printf("  LBA size:  %u bytes\n", nvme_get_lba_size(dev));
    }

    printf("\n✓ Example 6 complete\n");
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char** argv) {
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  SetupHelper Usage Examples                                   ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");

    // Check if running as root
    if (geteuid() != 0) {
        printf("\n⚠️  WARNING: Not running as root\n");
        printf("   Some examples may fail (VFIO requires privileges)\n");
        printf("   Run with: sudo -E %s\n\n", argv[0]);
    }

    // Check environment
    const char* bdf = std::getenv("NVME_BDF");
    if (!bdf || strlen(bdf) == 0) {
        printf("\n⚠️  WARNING: NVME_BDF not set\n");
        printf("   Most examples will fail\n");
        printf("   Set environment: export NVME_BDF=\"0000:41:00.0\"\n\n");
    } else {
        printf("\nEnvironment: NVME_BDF=%s\n", bdf);
    }

    // Run examples
    int example = 0;
    if (argc > 1) {
        example = std::atoi(argv[1]);
    }

    if (example == 0 || example == 1) example_manual_setup();
    if (example == 0 || example == 2) example_convenience_setup();
    if (example == 0 || example == 3) example_custom_setup();
#ifdef __CUDACC__
    if (example == 0 || example == 4) example_cuda_setup();
#endif
    if (example == 0 || example == 5) example_error_handling();
    if (example == 0 || example == 6) example_result_checking();

    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  All Examples Complete                                        ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    printf("\n");

    return 0;
}
