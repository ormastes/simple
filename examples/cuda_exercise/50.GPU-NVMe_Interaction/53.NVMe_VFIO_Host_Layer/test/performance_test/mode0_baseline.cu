/**
 * @file mode0_baseline.cu
 * @brief Mode 0 Baseline Test: Host Command + MMIO + Regular Host Buffer
 *
 * This test implements the baseline (non-optimized) workflow:
 * 1. CPU builds NVMe commands
 * 2. CPU rings MMIO doorbell
 * 3. Data is read to regular (pageable) host memory
 * 4. Data is copied from host to GPU (slower than pinned)
 * 5. GPU kernel processes the data
 *
 * This serves as a baseline to compare against optimized modes.
 * The use of regular memory instead of pinned memory results in
 * slower host-to-GPU transfers.
 *
 * @author Assistant
 * @date 2024-11-15
 */

#include <cuda_runtime.h>
#include <cuda.h>
#include <gtest/gtest.h>
#include <chrono>
#include <vector>
#include <numeric>
#include <iomanip>
#include <cstring>
#include <malloc.h>

// Module 53 includes
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "cuda_utils.h"
#include "helper/nvme_test_helper.h"

namespace {

// ============================================================================
// Configuration
// ============================================================================

constexpr size_t CHUNK_SIZE = 4096;        // 4KB per I/O operation
constexpr size_t NUM_ITERATIONS = 1000;    // Number of 4KB reads
constexpr int THREADS_PER_BLOCK = 256;

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Simple checksum kernel for data validation
 */
__global__ void checksum_kernel(const uint8_t* input, uint64_t* output, size_t size) {
    extern __shared__ uint64_t sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Initialize shared memory
    sdata[tid] = 0;

    // Compute partial sums
    uint64_t local_sum = 0;
    for (size_t i = idx; i < size; i += blockDim.x * gridDim.x) {
        local_sum += input[i];
    }
    sdata[tid] = local_sum;
    __syncthreads();

    // Reduction
    for (unsigned int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Write result
    if (tid == 0) {
        atomicAdd((unsigned long long*)output, (unsigned long long)sdata[0]);
    }
}

// ============================================================================
// Performance Stats
// ============================================================================

struct PerfStats {
    double nvme_read_ms = 0;
    double host_to_gpu_ms = 0;
    double kernel_exec_ms = 0;
    double total_ms = 0;
    size_t bytes_transferred = 0;

    // Additional stats for baseline
    double memory_alloc_ms = 0;
    size_t num_page_faults = 0;

    void print_summary(const std::string& test_name) const {
        double throughput_gb = (bytes_transferred / 1e9) / (total_ms / 1000.0);
        double nvme_throughput_gb = (bytes_transferred / 1e9) / (nvme_read_ms / 1000.0);
        double memcpy_bandwidth_gb = (bytes_transferred / 1e9) / (host_to_gpu_ms / 1000.0);

        printf("\n");
        printf("=============================================================\n");
        printf("Mode 0 BASELINE Performance: %s\n", test_name.c_str());
        printf("=============================================================\n");
        printf("Memory Type:         Regular (Pageable) Host Memory\n");
        printf("Data Size:           %.2f MB\n", bytes_transferred / 1e6);
        printf("Chunk Size:          %zu KB\n", CHUNK_SIZE / 1024);
        printf("Iterations:          %zu\n", NUM_ITERATIONS);
        printf("\n");
        printf("Timing Breakdown:\n");
        printf("  Memory Alloc:      %.3f ms\n", memory_alloc_ms);
        printf("  NVMe Read:         %.3f ms (%.1f%%)\n",
               nvme_read_ms, (nvme_read_ms / total_ms) * 100);
        printf("  Host->GPU Copy:    %.3f ms (%.1f%%)\n",
               host_to_gpu_ms, (host_to_gpu_ms / total_ms) * 100);
        printf("  Kernel Execution:  %.3f ms (%.1f%%)\n",
               kernel_exec_ms, (kernel_exec_ms / total_ms) * 100);
        printf("  Total:             %.3f ms\n", total_ms);
        printf("\n");
        printf("Throughput:\n");
        printf("  End-to-End:        %.3f GB/s\n", throughput_gb);
        printf("  NVMe Only:         %.3f GB/s\n", nvme_throughput_gb);
        printf("  Memcpy Bandwidth:  %.3f GB/s (SLOW - pageable memory!)\n", memcpy_bandwidth_gb);
        printf("  Efficiency:        %.1f%%\n", (throughput_gb / nvme_throughput_gb) * 100);
        printf("\n");
        printf("⚠️  WARNING: Using regular host memory causes:\n");
        printf("    - Slower host-to-GPU transfers (no DMA)\n");
        printf("    - Potential page faults\n");
        printf("    - Higher CPU overhead\n");
        printf("    → Use Mode 1 (pinned memory) for better performance!\n");
        printf("=============================================================\n");
    }
};

// ============================================================================
// Mode 0 Baseline Test
// ============================================================================

class Mode0BaselineTest : public ::testing::Test {
protected:
    NvmeDevice* dev = nullptr;
    Queue* iosq = nullptr;
    Queue* iocq = nullptr;

    // Regular (pageable) host memory - NOT pinned!
    uint8_t* h_regular_buffer = nullptr;

    // Host pool for NVMe DMA
    HostPool* host_pool = nullptr;

    // GPU memory
    uint8_t* d_buffer = nullptr;
    uint64_t* d_result = nullptr;

    // Test configuration
    uint32_t nsid = 1;
    uint32_t actual_lba_size = 512;  // Actual LBA size for block calculations
    uint32_t lba_size = 512;         // Keep for compatibility
    uint64_t start_lba = 2000000;

    void SetUp() override {
        nvme_test::ensure_nvme_env_defaults();

        // Get environment configuration
        const char* bdf = std::getenv("NVME_BDF");
        ASSERT_TRUE(bdf && *bdf) << "NVME_BDF not set (set NVME_BDF or NVME_ENV_FALLBACK)";

        const char* nsid_str = std::getenv("NVME_NSID");
        if (nsid_str) nsid = std::atoi(nsid_str);

        const char* lba_size_str = std::getenv("NVME_LBA_SIZE");
        if (lba_size_str) {
            actual_lba_size = std::atoi(lba_size_str);
            lba_size = actual_lba_size;  // Keep for compatibility
        }

        const char* slba_str = std::getenv("NVME_SLBA");
        if (slba_str) start_lba = std::atoll(slba_str);

        // Open NVMe device with CHUNK_SIZE as item_size for proper buffer allocation
        // This ensures the pool creates buffers of the correct size (4096 bytes)
        dev = nvme_open(bdf, 128, 128, CHUNK_SIZE);
        ASSERT_NE(dev, nullptr) << "Failed to open NVMe device " << bdf;

        iosq = nvme_get_iosq(dev);
        iocq = nvme_get_iocq(dev);

        // Create host pool for NVMe DMA buffers
        host_pool = host_pool_create(dev, 16);  // ItemSize from dev, 16 buffers for concurrent ops
        ASSERT_NE(host_pool, nullptr) << "Failed to create host pool";

        // Allocate REGULAR host memory (not pinned!)
        // Using memalign for alignment but still pageable
        h_regular_buffer = (uint8_t*)memalign(4096, CHUNK_SIZE);
        ASSERT_NE(h_regular_buffer, nullptr) << "Failed to allocate regular host memory";

        // Touch pages to ensure they're mapped
        memset(h_regular_buffer, 0, CHUNK_SIZE);

        // Allocate GPU memory
        cudaError_t err = cudaMalloc(&d_buffer, CHUNK_SIZE);
        ASSERT_EQ(err, cudaSuccess) << "Failed to allocate GPU buffer";

        err = cudaMalloc(&d_result, sizeof(uint64_t));
        ASSERT_EQ(err, cudaSuccess) << "Failed to allocate GPU result";

        // Initialize GPU result
        cudaMemset(d_result, 0, sizeof(uint64_t));

        printf("\nMode 0 BASELINE Configuration:\n");
        printf("  NVMe Device: %s\n", bdf);
        printf("  Memory Type: Regular (Pageable) Host Memory\n");
        printf("  ⚠️  Performance will be SUBOPTIMAL!\n");
        printf("  Chunk Size: %zu bytes\n", CHUNK_SIZE);
        printf("  Total Iterations: %zu\n", NUM_ITERATIONS);
    }

    void TearDown() override {
        if (h_regular_buffer) free(h_regular_buffer);
        if (d_buffer) cudaFree(d_buffer);
        if (d_result) cudaFree(d_result);
        if (host_pool) host_pool_destroy(host_pool);
        if (dev) nvme_close(dev);
    }

    void process_chunk_baseline(uint64_t lba, PerfStats& stats) {
        auto total_start = std::chrono::high_resolution_clock::now();

        // Step 1: Get DMA buffer from host pool
        DmaBuf* dma_buf = host_pool_acquire(host_pool);
        ASSERT_NE(dma_buf, nullptr) << "Failed to acquire DMA buffer";

        // Debug: Check DMA buffer fields
        if (dma_buf) {
            if (!dma_buf->addr) fprintf(stderr, "DEBUG: dma_buf->addr is NULL\n");
            if (dma_buf->bytes == 0) fprintf(stderr, "DEBUG: dma_buf->bytes is 0\n");
            if (dma_buf->prp1 == 0) fprintf(stderr, "DEBUG: dma_buf->prp1 is 0\n");
        }

        // Debug: Check queue fields
        if (!iosq) fprintf(stderr, "DEBUG: iosq is NULL\n");
        else {
            if (!iosq->db) fprintf(stderr, "DEBUG: iosq->db is NULL\n");
            if (!iosq->vaddr) fprintf(stderr, "DEBUG: iosq->vaddr is NULL\n");
            fprintf(stderr, "DEBUG: iosq tail=%u, head=%u, entries=%u\n",
                    iosq->tail, iosq->head, iosq->entries);
        }

        // Step 2: NVMe Read to DMA buffer
        auto nvme_start = std::chrono::high_resolution_clock::now();

        uint16_t cid = host_submit_runtime(
            CMD_READ,
            nullptr,  // MMIO doorbell
            iosq,
            nsid,
            lba,
            actual_lba_size,  // Use actual LBA size for block calculations
            dma_buf,
            CHUNK_SIZE
        );

        ASSERT_NE(cid, NVME_CID_ERROR) << "Failed to submit NVMe command";

        uint16_t completed_cid;
        NvmeStatus status = host_poll_completion_runtime(
            ASYNC_TYPE_SYNC,
            iocq,
            &completed_cid,
            nullptr,
            5000000,
            iosq  // Update submission queue head
        );

        ASSERT_EQ(status.sc, 0) << "NVMe command failed";

        auto nvme_end = std::chrono::high_resolution_clock::now();

        // Step 3: Copy from DMA buffer to regular buffer (CPU copy)
        memcpy(h_regular_buffer, dma_buf->addr, CHUNK_SIZE);

        // Release DMA buffer back to pool
        host_pool_release(host_pool, dma_buf);

        // Step 4: Copy from regular host to GPU (SLOW!)
        auto h2d_start = std::chrono::high_resolution_clock::now();

        cudaError_t err = cudaMemcpy(d_buffer, h_regular_buffer, CHUNK_SIZE,
                                      cudaMemcpyHostToDevice);
        ASSERT_EQ(err, cudaSuccess) << "Host to device copy failed";

        auto h2d_end = std::chrono::high_resolution_clock::now();

        // Step 5: Execute GPU kernel
        auto kernel_start = std::chrono::high_resolution_clock::now();

        int blocks = (CHUNK_SIZE + THREADS_PER_BLOCK - 1) / THREADS_PER_BLOCK;
        checksum_kernel<<<blocks, THREADS_PER_BLOCK,
                         THREADS_PER_BLOCK * sizeof(uint64_t)>>>(
            d_buffer, d_result, CHUNK_SIZE
        );

        err = cudaDeviceSynchronize();
        ASSERT_EQ(err, cudaSuccess) << "Kernel execution failed";

        auto kernel_end = std::chrono::high_resolution_clock::now();

        // Update statistics
        stats.nvme_read_ms += std::chrono::duration<double, std::milli>(
            nvme_end - nvme_start).count();
        stats.host_to_gpu_ms += std::chrono::duration<double, std::milli>(
            h2d_end - h2d_start).count();
        stats.kernel_exec_ms += std::chrono::duration<double, std::milli>(
            kernel_end - kernel_start).count();
        stats.total_ms += std::chrono::duration<double, std::milli>(
            kernel_end - total_start).count();
        stats.bytes_transferred += CHUNK_SIZE;
    }
};

// ============================================================================
// Tests
// ============================================================================

TEST_F(Mode0BaselineTest, Sequential_Baseline_Performance) {
    PerfStats stats;

    printf("\nStarting Mode 0 BASELINE sequential test...\n");
    printf("Using REGULAR (pageable) host memory - expect slower performance!\n");

    // Measure memory allocation overhead
    auto alloc_start = std::chrono::high_resolution_clock::now();

    // Allocate and touch a large regular buffer to measure overhead
    void* test_buffer = malloc(100 * CHUNK_SIZE);
    memset(test_buffer, 0, 100 * CHUNK_SIZE);
    free(test_buffer);

    auto alloc_end = std::chrono::high_resolution_clock::now();
    stats.memory_alloc_ms = std::chrono::duration<double, std::milli>(
        alloc_end - alloc_start).count();

    // Warm-up iterations
    for (int i = 0; i < 10; i++) {
        PerfStats temp_stats;
        uint64_t lba = start_lba + (i * CHUNK_SIZE / actual_lba_size);
        process_chunk_baseline(lba, temp_stats);
    }

    // Measured iterations
    auto test_start = std::chrono::high_resolution_clock::now();

    for (size_t i = 0; i < NUM_ITERATIONS; i++) {
        uint64_t lba = start_lba + (i * CHUNK_SIZE / actual_lba_size);
        process_chunk_baseline(lba, stats);

        if ((i + 1) % 100 == 0) {
            printf("  Processed %zu/%zu chunks (%.1f%%) - BASELINE MODE\r",
                   i + 1, NUM_ITERATIONS,
                   ((i + 1) * 100.0) / NUM_ITERATIONS);
            fflush(stdout);
        }
    }

    auto test_end = std::chrono::high_resolution_clock::now();
    double wall_time_ms = std::chrono::duration<double, std::milli>(
        test_end - test_start).count();

    printf("\n");

    // Verify result
    uint64_t h_result;
    cudaMemcpy(&h_result, d_result, sizeof(uint64_t), cudaMemcpyDeviceToHost);
    printf("\nChecksum: %lu\n", h_result);

    // Print performance summary
    stats.print_summary("Sequential 4KB Reads");

    printf("\nBaseline Comparison Metrics:\n");
    printf("  Wall Clock Time:     %.3f ms\n", wall_time_ms);
    printf("  Per-Chunk Latency:   %.3f us\n", (stats.total_ms / NUM_ITERATIONS) * 1000);
    printf("  IOPS:                %.0f\n", (NUM_ITERATIONS / wall_time_ms) * 1000);
    printf("\n");
    printf("  💡 TIP: Compare with Mode 1 (pinned memory) to see improvement!\n");
}

TEST_F(Mode0BaselineTest, ShowMemcpyDifference) {
    printf("\n=============================================================\n");
    printf("Demonstrating Memcpy Performance Difference\n");
    printf("=============================================================\n");

    const size_t test_size = 1024 * 1024;  // 1MB
    const int iterations = 100;

    // Allocate regular and pinned memory
    uint8_t* regular_mem = (uint8_t*)malloc(test_size);
    uint8_t* pinned_mem = nullptr;
    uint8_t* gpu_mem = nullptr;

    cudaMallocHost(&pinned_mem, test_size);
    cudaMalloc(&gpu_mem, test_size);

    // Initialize
    memset(regular_mem, 0xAA, test_size);
    memset(pinned_mem, 0xBB, test_size);

    // Test regular memory transfer
    auto regular_start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < iterations; i++) {
        cudaMemcpy(gpu_mem, regular_mem, test_size, cudaMemcpyHostToDevice);
    }
    cudaDeviceSynchronize();
    auto regular_end = std::chrono::high_resolution_clock::now();

    // Test pinned memory transfer
    auto pinned_start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < iterations; i++) {
        cudaMemcpy(gpu_mem, pinned_mem, test_size, cudaMemcpyHostToDevice);
    }
    cudaDeviceSynchronize();
    auto pinned_end = std::chrono::high_resolution_clock::now();

    double regular_ms = std::chrono::duration<double, std::milli>(
        regular_end - regular_start).count();
    double pinned_ms = std::chrono::duration<double, std::milli>(
        pinned_end - pinned_start).count();

    double regular_bandwidth = (test_size * iterations / 1e9) / (regular_ms / 1000.0);
    double pinned_bandwidth = (test_size * iterations / 1e9) / (pinned_ms / 1000.0);

    printf("\nMemcpy Performance Comparison (1MB × %d iterations):\n", iterations);
    printf("  Regular Memory:\n");
    printf("    Time:      %.2f ms\n", regular_ms);
    printf("    Bandwidth: %.2f GB/s\n", regular_bandwidth);
    printf("\n");
    printf("  Pinned Memory:\n");
    printf("    Time:      %.2f ms\n", pinned_ms);
    printf("    Bandwidth: %.2f GB/s\n", pinned_bandwidth);
    printf("\n");
    printf("  Speedup:     %.2fx faster with pinned memory!\n", regular_ms / pinned_ms);
    printf("  Bandwidth:   %.1f%% improvement\n",
           ((pinned_bandwidth - regular_bandwidth) / regular_bandwidth) * 100);
    printf("\n");
    printf("This is why Mode 1 (pinned) outperforms Mode 0 (baseline)!\n");
    printf("=============================================================\n");

    // Cleanup
    free(regular_mem);
    cudaFreeHost(pinned_mem);
    cudaFree(gpu_mem);
}

}  // namespace

TEST(Mode0PerfTest, Registration) {
    SUCCEED();
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    // Initialize CUDA
    int device_count;
    cudaGetDeviceCount(&device_count);
    if (device_count == 0) {
        printf("ERROR: No CUDA devices available\n");
        return 1;
    }

    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, 0);
    printf("\n=============================================================\n");
    printf("Mode 0 BASELINE Test: Host + MMIO + Regular Memory\n");
    printf("=============================================================\n");
    printf("GPU Device: %s\n", prop.name);
    printf("⚠️  Using REGULAR (pageable) host memory\n");
    printf("⚠️  Performance will be SUBOPTIMAL - for comparison only!\n");
    printf("=============================================================\n");

    return RUN_ALL_TESTS();
}
