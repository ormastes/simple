/**
 * Multi-Stream Overlap Demonstration (Part 22)
 *
 * Demonstrates overlapping kernel execution with memory transfers using
 * multiple CUDA streams for maximum GPU utilization.
 *
 * This example showcases:
 * - Creating and managing multiple streams
 * - Pinned memory allocation for async transfers
 * - Overlapping H2D, kernel execution, and D2H operations
 * - Proper error handling for stream operations
 * - Synchronization and cleanup
 *
 * Based on the canonical CUDA streams overlap pattern.
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>

/**
 * Compute-intensive kernel for demonstrating overlap
 * Each thread performs iterative calculations to keep GPU busy
 * while other streams handle memory transfers.
 */
__global__ void init_array(int *g_data, int *factor, int num_iterations) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    for (int i = 0; i < num_iterations; i++) {
        g_data[idx] += *factor;
    }
}

/**
 * Helper macro for CUDA error checking with line number reporting
 */
#define CHECK_CUDA(call) do { \
    cudaError_t err = call; \
    if (err != cudaSuccess) { \
        fprintf(stderr, "CUDA error at %s:%d - %s\n", __FILE__, __LINE__, \
                cudaGetErrorString(err)); \
        exit(EXIT_FAILURE); \
    } \
} while(0)

int main() {
    printf("=== Multi-Stream Overlap Demonstration ===\n\n");

    // Configuration
    const int num_streams = 4;          // Number of concurrent streams
    const int num_elements = 1024 * 1024; // 1M elements per stream
    const int num_iterations = 100;     // Kernel workload iterations

    // Query device capabilities
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));
    printf("Device: %s\n", prop.name);
    printf("Concurrent Kernels: %s\n",
           prop.concurrentKernels ? "YES" : "NO");
    printf("Async Engine Count: %d\n", prop.asyncEngineCount);
    printf("Compute Capability: %d.%d\n\n", prop.major, prop.minor);

    // Allocate host arrays (pinned memory required for async transfers)
    int *h_data[num_streams];
    printf("Allocating pinned host memory for %d streams...\n", num_streams);
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaMallocHost((void **)&h_data[i],
                                  num_elements * sizeof(int)));

        // Initialize with test pattern
        for (int j = 0; j < num_elements; j++) {
            h_data[i][j] = j;
        }
    }

    // Allocate device arrays (one per stream for concurrent processing)
    int *d_data[num_streams];
    printf("Allocating device memory for %d streams...\n", num_streams);
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaMalloc((void **)&d_data[i],
                             num_elements * sizeof(int)));
    }

    // Allocate and initialize factor (shared across all kernels)
    int *h_factor;
    CHECK_CUDA(cudaMallocHost((void **)&h_factor, sizeof(int)));
    *h_factor = 2;

    int *d_factor;
    CHECK_CUDA(cudaMalloc((void **)&d_factor, sizeof(int)));
    CHECK_CUDA(cudaMemcpy(d_factor, h_factor, sizeof(int),
                         cudaMemcpyHostToDevice));

    // Create CUDA streams
    cudaStream_t streams[num_streams];
    printf("Creating %d CUDA streams...\n\n", num_streams);
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaStreamCreate(&streams[i]));
    }

    // Create events for timing
    cudaEvent_t start, stop;
    CHECK_CUDA(cudaEventCreate(&start));
    CHECK_CUDA(cudaEventCreate(&stop));

    // Launch kernel configuration
    dim3 block(256);
    dim3 grid((num_elements + block.x - 1) / block.x);

    printf("Launching overlapped operations on %d streams:\n", num_streams);
    printf("  Grid: %d blocks × %d threads = %d total threads\n\n",
           grid.x, block.x, grid.x * block.x);

    // Record start time
    CHECK_CUDA(cudaEventRecord(start));

    // Execute operations with overlap
    // Each stream performs: H2D transfer → Kernel → D2H transfer
    // Different streams execute concurrently
    for (int i = 0; i < num_streams; i++) {
        printf("Stream %d: Queuing H2D → Kernel → D2H\n", i);

        // Async Host-to-Device transfer
        CHECK_CUDA(cudaMemcpyAsync(d_data[i], h_data[i],
                                   num_elements * sizeof(int),
                                   cudaMemcpyHostToDevice, streams[i]));

        // Kernel launch in stream
        init_array<<<grid, block, 0, streams[i]>>>(
            d_data[i], d_factor, num_iterations);

        // Check for kernel launch errors
        CHECK_CUDA(cudaGetLastError());

        // Async Device-to-Host transfer
        CHECK_CUDA(cudaMemcpyAsync(h_data[i], d_data[i],
                                   num_elements * sizeof(int),
                                   cudaMemcpyDeviceToHost, streams[i]));
    }

    printf("\nAll operations queued. Streams executing concurrently...\n\n");

    // Synchronize all streams and measure time
    printf("Synchronizing streams:\n");
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaStreamSynchronize(streams[i]));
        printf("  Stream %d: Completed\n", i);
    }

    // Record stop time
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));

    // Calculate elapsed time
    float milliseconds = 0;
    CHECK_CUDA(cudaEventElapsedTime(&milliseconds, start, stop));

    printf("\n=== Results ===\n");
    printf("Total execution time: %.2f ms\n", milliseconds);
    printf("Time per stream (amortized): %.2f ms\n",
           milliseconds / num_streams);

    // Verify correctness (check first and last element of each stream)
    printf("\nVerifying results:\n");
    bool all_correct = true;
    for (int i = 0; i < num_streams; i++) {
        int expected = 0 + (*h_factor * num_iterations);
        int last_expected = (num_elements - 1) +
                           (*h_factor * num_iterations);

        if (h_data[i][0] != expected ||
            h_data[i][num_elements-1] != last_expected) {
            printf("  Stream %d: FAILED (got %d, expected %d)\n",
                   i, h_data[i][0], expected);
            all_correct = false;
        } else {
            printf("  Stream %d: PASSED\n", i);
        }
    }

    printf("\nOverall: %s\n", all_correct ? "✓ ALL TESTS PASSED" : "✗ TESTS FAILED");

    // Cleanup: Destroy streams
    printf("\nCleaning up resources...\n");
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaStreamDestroy(streams[i]));
    }

    // Cleanup: Free host memory
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaFreeHost(h_data[i]));
    }
    CHECK_CUDA(cudaFreeHost(h_factor));

    // Cleanup: Free device memory
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaFree(d_data[i]));
    }
    CHECK_CUDA(cudaFree(d_factor));

    // Cleanup: Destroy events
    CHECK_CUDA(cudaEventDestroy(start));
    CHECK_CUDA(cudaEventDestroy(stop));

    printf("Done.\n");

    return 0;
}
