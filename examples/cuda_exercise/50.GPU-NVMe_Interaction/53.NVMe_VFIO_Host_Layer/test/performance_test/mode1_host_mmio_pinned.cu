/**
 * @file mode1_host_mmio_pinned.cu
 * @brief DEPRECATED: Mode 1 Performance Test - MMIO Doorbell Support Removed
 * 
 * @deprecated This test is deprecated and should not be used.
 * MMIO doorbell access has been removed because GPU kernels cannot access MMIO registers.
 * Use DBC (Doorbell Buffer Config) mechanisms instead:
 * - DBC Shadow: Hardware-based doorbell buffering
 * - DBC Daemon: Software daemon for doorbell mirroring
 *
 * @note This file is retained for reference but will not compile with current codebase.
 *
 * Original workflow (no longer supported):
 * 1. CPU builds NVMe commands
 * 2. CPU rings MMIO doorbell  ← NOT SUPPORTED BY GPU
 * 3. Data is read to pinned host memory
 * 4. Data is copied from host to GPU
 * 5. GPU kernel processes the data
 *
 * This represents the traditional approach where NVMe I/O is CPU-driven
 * and data must be staged through host memory before GPU processing.
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
constexpr size_t TOTAL_SIZE = CHUNK_SIZE * NUM_ITERATIONS;  // Total data size

// GPU kernel threads configuration
constexpr int THREADS_PER_BLOCK = 256;

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Compute sum kernel for address calculation
 *
 * Sums the data read from NVMe to compute the next LBA address.
 * This prevents async prefetching and ensures fair performance comparison.
 */
__global__ void compute_sum_kernel(const uint8_t* input, uint64_t* output, size_t size) {
    extern __shared__ uint64_t sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Initialize shared memory
    sdata[tid] = 0;

    // Each thread processes multiple elements to compute partial sum
    uint64_t local_sum = 0;
    for (size_t i = idx; i < size; i += blockDim.x * gridDim.x) {
        local_sum += input[i];
    }
    sdata[tid] = local_sum;
    __syncthreads();

    // Reduction in shared memory
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

/**
 * @brief More complex kernel - XOR transformation
 *
 * Performs XOR transformation with pattern detection.
 * This represents more realistic workload than simple checksum.
 */
__global__ void transform_data_kernel(uint8_t* data, size_t size, uint8_t pattern) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        // XOR with pattern and rotate bits
        uint8_t val = data[idx];
        val ^= pattern;
        val = (val << 1) | (val >> 7);  // Rotate left by 1
        data[idx] = val;
    }
}

// ============================================================================
// Performance Measurement
// ============================================================================

struct PerfStats {
    double nvme_read_ms = 0;
    double host_to_gpu_ms = 0;
    double kernel_exec_ms = 0;
    double total_ms = 0;
    size_t bytes_transferred = 0;

    void print_summary(const std::string& test_name) const {
        double throughput_gb = (bytes_transferred / 1e9) / (total_ms / 1000.0);
        double nvme_throughput_gb = (bytes_transferred / 1e9) / (nvme_read_ms / 1000.0);

        printf("\n");
        printf("=============================================================\n");
        printf("Mode 1 Performance: %s\n", test_name.c_str());
        printf("=============================================================\n");
        printf("Data Size:           %.2f MB\n", bytes_transferred / 1e6);
        printf("Chunk Size:          %zu KB\n", CHUNK_SIZE / 1024);
        printf("Iterations:          %zu\n", NUM_ITERATIONS);
        printf("\n");
        printf("Timing Breakdown:\n");
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
        printf("  Efficiency:        %.1f%%\n", (throughput_gb / nvme_throughput_gb) * 100);
        printf("=============================================================\n");
    }
};

// ============================================================================
// Mode 1 Test Implementation
// ============================================================================

class Mode1PerfTest : public ::testing::Test {
protected:
    NvmeDevice* dev = nullptr;
    Queue* iosq = nullptr;
    Queue* iocq = nullptr;

    // Pinned host memory for NVMe reads
    uint8_t* h_pinned_buffer = nullptr;
    uint64_t pinned_iova_ = 0;  // IOVA address for pinned memory

    // GPU memory for processing
    uint8_t* d_buffer = nullptr;
    uint64_t* d_sum_result = nullptr;

    // Test configuration
    uint32_t nsid = 1;
    uint32_t lba_size = 512;
    uint64_t start_lba = 2000000;  // Safe test area

    void SetUp() override {
        nvme_test::ensure_nvme_env_defaults();

        // Get environment configuration
        const char* bdf = std::getenv("NVME_BDF");
        ASSERT_TRUE(bdf && *bdf) << "NVME_BDF not set (set NVME_BDF or NVME_ENV_FALLBACK)";

        const char* nsid_str = std::getenv("NVME_NSID");
        if (nsid_str) nsid = std::atoi(nsid_str);

        const char* lba_size_str = std::getenv("NVME_LBA_SIZE");
        if (lba_size_str) lba_size = std::atoi(lba_size_str);

        const char* slba_str = std::getenv("NVME_SLBA");
        if (slba_str) start_lba = std::atoll(slba_str);

        // Open NVMe device with CHUNK_SIZE as item_size for proper buffer allocation
        // This ensures proper buffer sizes for DMA operations
        dev = nvme_open(bdf, 128, 128, CHUNK_SIZE);
        ASSERT_NE(dev, nullptr) << "Failed to open NVMe device " << bdf;

        iosq = nvme_get_iosq(dev);
        iocq = nvme_get_iocq(dev);

        // Allocate pinned host memory (for NVMe DMA)
        cudaError_t err = cudaMallocHost(&h_pinned_buffer, CHUNK_SIZE);
        ASSERT_EQ(err, cudaSuccess) << "Failed to allocate pinned host memory";

        // Map pinned memory to IOVA for NVMe DMA
        int ret = host_map_iova(h_pinned_buffer, CHUNK_SIZE, &pinned_iova_);
        ASSERT_EQ(ret, 0) << "Failed to map pinned memory to IOVA";

        // Allocate GPU memory
        err = cudaMalloc(&d_buffer, CHUNK_SIZE);
        ASSERT_EQ(err, cudaSuccess) << "Failed to allocate GPU buffer";

        err = cudaMalloc(&d_sum_result, sizeof(uint64_t));
        ASSERT_EQ(err, cudaSuccess) << "Failed to allocate GPU sum result";

        // Initialize GPU result
        cudaMemset(d_sum_result, 0, sizeof(uint64_t));

        // Pre-write non-zero patterns to NVMe test area
        printf("Pre-writing test patterns to NVMe...\n");
        const int test_patterns = 1000;  // Write patterns for test LBAs
        for (int i = 0; i < test_patterns; i++) {
            // Fill buffer with pattern based on LBA
            for (size_t j = 0; j < CHUNK_SIZE; j++) {
                h_pinned_buffer[j] = (uint8_t)((i + j) & 0xFF);
            }

            // Write to NVMe (each write covers CHUNK_SIZE/lba_size blocks)
            uint64_t lba = start_lba + i * (CHUNK_SIZE / lba_size);
            DmaBuf host_buf;
            host_buf.addr = h_pinned_buffer;
            host_buf.bytes = CHUNK_SIZE;
            host_buf.prp1 = pinned_iova_;  // Use IOVA for DMA
            host_buf.prp2 = 0;

            uint16_t cid = host_submit_runtime(
                CMD_WRITE,
                nullptr,
                iosq,
                nsid,
                lba,
                lba_size,
                &host_buf,
                CHUNK_SIZE
            );
            ASSERT_NE(cid, NVME_CID_ERROR) << "Failed to submit write command";

            uint16_t completed_cid;
            NvmeStatus status = host_poll_completion_runtime(
                ASYNC_TYPE_SYNC,
                iocq,
                &completed_cid,
                nullptr,
                5000000,
                iosq  // Update submission queue head
            );
            ASSERT_EQ(status.sc, 0) << "Write command failed";
        }

        printf("\nMode 1 Test Configuration:\n");
        printf("  NVMe Device: %s\n", bdf);
        printf("  Namespace ID: %u\n", nsid);
        printf("  LBA Size: %u bytes\n", lba_size);
        printf("  Start LBA: %lu\n", start_lba);
        printf("  Chunk Size: %zu bytes\n", CHUNK_SIZE);
        printf("  Total Iterations: %zu\n", NUM_ITERATIONS);
    }

    void TearDown() override {
        if (h_pinned_buffer && pinned_iova_) {
            host_unmap_iova(h_pinned_buffer, CHUNK_SIZE, pinned_iova_);
        }
        if (h_pinned_buffer) cudaFreeHost(h_pinned_buffer);
        if (d_buffer) cudaFree(d_buffer);
        if (d_sum_result) cudaFree(d_sum_result);
        if (dev) nvme_close(dev);
    }

    /**
     * @brief Execute Mode 1 workflow for one chunk
     *
     * 1. Build NVMe READ command (CPU)
     * 2. Submit with MMIO doorbell (CPU)
     * 3. Poll for completion (CPU)
     * 4. Copy data from pinned host to GPU
     * 5. Execute GPU kernel to compute sum
     * @return Next LBA based on sum
     */
    uint64_t process_chunk(uint64_t lba, PerfStats& stats) {
        auto total_start = std::chrono::high_resolution_clock::now();

        // Step 1-3: NVMe Read to pinned host memory
        auto nvme_start = std::chrono::high_resolution_clock::now();

        // Create DMA buffer descriptor for pinned memory
        DmaBuf host_buf;
        host_buf.addr = h_pinned_buffer;
        host_buf.bytes = CHUNK_SIZE;
        host_buf.prp1 = pinned_iova_;  // Use IOVA for DMA
        host_buf.prp2 = 0;  // Single page

        // Submit NVMe READ command with MMIO doorbell
        uint16_t cid = host_submit_runtime(
            CMD_READ,
            nullptr,  // Use default MMIO doorbell
            iosq,
            nsid,
            lba,
            lba_size,
            &host_buf,
            CHUNK_SIZE
        );

        if (cid == NVME_CID_ERROR) {
            ADD_FAILURE() << "Failed to submit NVMe command";
            return 0;
        }

        // Poll for completion (pass iosq to update submission queue head)
        uint16_t completed_cid;
        NvmeStatus status = host_poll_completion_runtime(
            ASYNC_TYPE_SYNC,
            iocq,
            &completed_cid,
            nullptr,
            5000000,  // 5 second timeout
            iosq      // Pass submission queue to update its head
        );

        if (status.sc != 0) {
            ADD_FAILURE() << "NVMe command failed with status " << status.sc;
            return 0;
        }

        auto nvme_end = std::chrono::high_resolution_clock::now();

        // Step 4: Copy from pinned host to GPU
        auto h2d_start = std::chrono::high_resolution_clock::now();

        cudaError_t err = cudaMemcpy(d_buffer, h_pinned_buffer, CHUNK_SIZE,
                                      cudaMemcpyHostToDevice);
        if (err != cudaSuccess) {
            ADD_FAILURE() << "Host to device copy failed";
            return 0;
        }

        auto h2d_end = std::chrono::high_resolution_clock::now();

        // Step 5: Execute GPU kernel to compute sum
        auto kernel_start = std::chrono::high_resolution_clock::now();

        // Reset sum result
        cudaMemset(d_sum_result, 0, sizeof(uint64_t));

        int blocks = (CHUNK_SIZE + THREADS_PER_BLOCK - 1) / THREADS_PER_BLOCK;
        compute_sum_kernel<<<blocks, THREADS_PER_BLOCK,
                             THREADS_PER_BLOCK * sizeof(uint64_t)>>>(
            d_buffer, d_sum_result, CHUNK_SIZE
        );

        err = cudaDeviceSynchronize();
        if (err != cudaSuccess) {
            ADD_FAILURE() << "Kernel execution failed";
            return 0;
        }

        // Get sum result
        uint64_t host_sum;
        err = cudaMemcpy(&host_sum, d_sum_result, sizeof(uint64_t),
                        cudaMemcpyDeviceToHost);
        if (err != cudaSuccess) {
            ADD_FAILURE() << "Failed to copy sum result";
            return 0;
        }

        auto kernel_end = std::chrono::high_resolution_clock::now();
        auto total_end = kernel_end;

        // Update statistics
        stats.nvme_read_ms += std::chrono::duration<double, std::milli>(
            nvme_end - nvme_start).count();
        stats.host_to_gpu_ms += std::chrono::duration<double, std::milli>(
            h2d_end - h2d_start).count();
        stats.kernel_exec_ms += std::chrono::duration<double, std::milli>(
            kernel_end - kernel_start).count();
        stats.total_ms += std::chrono::duration<double, std::milli>(
            total_end - total_start).count();
        stats.bytes_transferred += CHUNK_SIZE;

        // Return next LBA based on sum (modulo 1000 to stay in test area)
        return (host_sum % 1000);
    }
};

// ============================================================================
// Performance Tests
// ============================================================================

TEST_F(Mode1PerfTest, Sequential_4KB_Reads_With_Processing) {
    PerfStats stats;

    printf("\nStarting Mode 1 sequential read test...\n");

    // Warm-up iterations
    uint64_t next_lba_offset = 0;
    for (int i = 0; i < 10; i++) {
        PerfStats temp_stats;
        uint64_t lba = start_lba + next_lba_offset;
        next_lba_offset = process_chunk(lba, temp_stats);
    }

    // Measured iterations
    auto test_start = std::chrono::high_resolution_clock::now();

    // Reset for main benchmark
    next_lba_offset = 0;
    for (size_t i = 0; i < NUM_ITERATIONS; i++) {
        // Use computed LBA from previous iteration's sum
        uint64_t lba = start_lba + next_lba_offset;
        next_lba_offset = process_chunk(lba, stats);

        // Progress reporting every 100 iterations
        if ((i + 1) % 100 == 0) {
            printf("  Processed %zu/%zu chunks (%.1f%%)\r",
                   i + 1, NUM_ITERATIONS,
                   ((i + 1) * 100.0) / NUM_ITERATIONS);
            fflush(stdout);
        }
    }

    auto test_end = std::chrono::high_resolution_clock::now();
    double wall_time_ms = std::chrono::duration<double, std::milli>(
        test_end - test_start).count();

    printf("\n");

    // Print performance summary
    stats.print_summary("Sequential 4KB Reads");

    // Additional metrics
    printf("\nAdditional Metrics:\n");
    printf("  Wall Clock Time:   %.3f ms\n", wall_time_ms);
    printf("  Per-Chunk Latency: %.3f us\n", (stats.total_ms / NUM_ITERATIONS) * 1000);
    printf("  IOPS:              %.0f\n", (NUM_ITERATIONS / wall_time_ms) * 1000);
}

TEST_F(Mode1PerfTest, Random_4KB_Reads_With_Transform) {
    PerfStats stats;

    printf("\nStarting Mode 1 random read test with transform...\n");

    // Use different kernel for variety
    const uint8_t xor_pattern = 0xA5;

    // Random LBA sequence (pick from pre-written locations)
    std::vector<uint64_t> lba_sequence(NUM_ITERATIONS);
    for (size_t i = 0; i < NUM_ITERATIONS; i++) {
        // Pick random index from the 1000 pre-written locations
        // Each pre-write covered CHUNK_SIZE/lba_size blocks
        uint32_t random_index = rand() % 1000;
        uint64_t offset = random_index * (CHUNK_SIZE / lba_size);
        lba_sequence[i] = start_lba + offset;
    }

    auto test_start = std::chrono::high_resolution_clock::now();

    for (size_t i = 0; i < NUM_ITERATIONS; i++) {
        auto iter_start = std::chrono::high_resolution_clock::now();

        // NVMe read to pinned host
        auto nvme_start = std::chrono::high_resolution_clock::now();

        DmaBuf host_buf;
        host_buf.addr = h_pinned_buffer;
        host_buf.bytes = CHUNK_SIZE;
        host_buf.prp1 = pinned_iova_;  // Use IOVA for DMA
        host_buf.prp2 = 0;

        uint16_t cid = host_submit_runtime(
            CMD_READ,
            nullptr,
            iosq,
            nsid,
            lba_sequence[i],
            lba_size,
            &host_buf,
            CHUNK_SIZE
        );

        ASSERT_NE(cid, NVME_CID_ERROR);

        uint16_t completed_cid;
        NvmeStatus status = host_poll_completion_runtime(
            ASYNC_TYPE_SYNC,
            iocq,
            &completed_cid,
            nullptr,
            5000000,
            iosq  // Update submission queue head
        );

        ASSERT_EQ(status.sc, 0);

        auto nvme_end = std::chrono::high_resolution_clock::now();

        // Host to GPU copy
        auto h2d_start = std::chrono::high_resolution_clock::now();
        cudaMemcpy(d_buffer, h_pinned_buffer, CHUNK_SIZE, cudaMemcpyHostToDevice);
        auto h2d_end = std::chrono::high_resolution_clock::now();

        // GPU transform kernel
        auto kernel_start = std::chrono::high_resolution_clock::now();

        int blocks = (CHUNK_SIZE + THREADS_PER_BLOCK - 1) / THREADS_PER_BLOCK;
        transform_data_kernel<<<blocks, THREADS_PER_BLOCK>>>(
            d_buffer, CHUNK_SIZE, xor_pattern
        );
        cudaDeviceSynchronize();

        auto kernel_end = std::chrono::high_resolution_clock::now();

        // Update stats
        stats.nvme_read_ms += std::chrono::duration<double, std::milli>(
            nvme_end - nvme_start).count();
        stats.host_to_gpu_ms += std::chrono::duration<double, std::milli>(
            h2d_end - h2d_start).count();
        stats.kernel_exec_ms += std::chrono::duration<double, std::milli>(
            kernel_end - kernel_start).count();
        stats.total_ms += std::chrono::duration<double, std::milli>(
            kernel_end - iter_start).count();
        stats.bytes_transferred += CHUNK_SIZE;

        if ((i + 1) % 100 == 0) {
            printf("  Processed %zu/%zu chunks (%.1f%%)\r",
                   i + 1, NUM_ITERATIONS,
                   ((i + 1) * 100.0) / NUM_ITERATIONS);
            fflush(stdout);
        }
    }

    auto test_end = std::chrono::high_resolution_clock::now();
    double wall_time_ms = std::chrono::duration<double, std::milli>(
        test_end - test_start).count();

    printf("\n");

    // Print performance summary
    stats.print_summary("Random 4KB Reads with Transform");

    printf("\nRandom Access Metrics:\n");
    printf("  Wall Clock Time:   %.3f ms\n", wall_time_ms);
    printf("  Random IOPS:       %.0f\n", (NUM_ITERATIONS / wall_time_ms) * 1000);
    printf("  Avg Latency:       %.3f us\n", (wall_time_ms / NUM_ITERATIONS) * 1000);
}

}  // namespace

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
    printf("Mode 1 Performance Test: Host + MMIO + Pinned Memory\n");
    printf("=============================================================\n");
    printf("GPU Device: %s\n", prop.name);
    printf("Compute Capability: %d.%d\n", prop.major, prop.minor);
    printf("Global Memory: %.1f GB\n", prop.totalGlobalMem / 1e9);
    printf("Memory Bus Width: %d bits\n", prop.memoryBusWidth);
    printf("=============================================================\n");

    return RUN_ALL_TESTS();
}
