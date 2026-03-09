/**
 * Overlap Transfer and Compute Demonstration (Part 22)
 *
 * Demonstrates the fundamental pattern of hiding memory transfer latency
 * by overlapping H2D/D2H transfers with kernel execution using streams.
 *
 * Configuration with concrete numbers:
 * - 2 streams for double-buffering pattern
 * - 16 chunks of 262,144 elements each (2^18)
 * - Total data: 4,194,304 elements (16 chunks × 262,144)
 * - Each chunk: 1 MB (262,144 floats × 4 bytes)
 *
 * Double-buffering timeline (2 streams, first 4 chunks):
 * Time →    0ms      20ms     40ms     60ms     80ms
 * Stream 0: [H2D][Kernel][D2H]
 *                                [H2D][Kernel][D2H]
 *                                Chunk 2 starts ──┘
 *
 * Stream 1:      [H2D][Kernel][D2H]
 *                              [H2D][Kernel][D2H]
 *                              Chunk 3 starts ──┘
 *
 * Key insight: While Stream 0 processes chunk 0, Stream 1 begins chunk 1
 * This overlaps Stream 0's D2H with Stream 1's H2D transfer
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>
#include <chrono>

// Configuration: 16 chunks of 262,144 elements (1 MB) each
#define CHUNK_SIZE (1<<18)  // 262,144 elements per chunk
#define NCHUNKS 16          // Total chunks to process
#define NSTREAMS 2          // Double buffering with 2 streams

/**
 * Compute-intensive kernel for demonstrating overlap
 * Performs 100 iterations of trigonometric operations per element
 *
 * Example: With 256 threads/block and 1024 blocks:
 *   Total threads = 256 × 1,024 = 262,144 threads (matches CHUNK_SIZE)
 *   Each thread: 100 iterations × 2 ops (sin + cos) = 200 FLOPs
 *   Total per chunk: 262,144 threads × 200 FLOPs = 52.4M FLOPs
 *
 * This kernel is intentionally compute-heavy to:
 * 1. Make kernel execution time >> transfer time
 * 2. Demonstrate overlap benefits clearly
 * 3. Simulate real-world compute workloads
 */
__global__ void process_data(float* data, int size, float factor) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        float val = data[idx];
        // Heavy computation: 100 iterations allow memory transfers to overlap
        for (int i = 0; i < 100; i++) {
            val = sinf(val) * factor + cosf(val);
        }
        data[idx] = val;
    }
}

static void check_cuda_error(cudaError_t error, const char* function) {
    if (error != cudaSuccess) {
        fprintf(stderr, "CUDA error in %s: %s\n", function, cudaGetErrorString(error));
        exit(1);
    }
}

void init_data(float* data, int size) {
    for (int i = 0; i < size; i++) {
        data[i] = (float)(i % 1000) / 1000.0f;
    }
}

int main() {
    printf("Overlap Transfer and Compute Example\n");
    printf("=====================================\n\n");

    const int total_size = CHUNK_SIZE * NCHUNKS;

    // Allocate pinned host memory
    float *h_data;
    check_cuda_error(cudaMallocHost(&h_data, total_size * sizeof(float)), "cudaMallocHost");
    init_data(h_data, total_size);

    // Allocate device memory
    float *d_data;
    check_cuda_error(cudaMalloc(&d_data, CHUNK_SIZE * NSTREAMS * sizeof(float)), "cudaMalloc");

    // Create streams
    cudaStream_t streams[NSTREAMS];
    for (int i = 0; i < NSTREAMS; i++) {
        check_cuda_error(cudaStreamCreate(&streams[i]), "cudaStreamCreate");
    }

    int threads = 256;
    int blocks = (CHUNK_SIZE + threads - 1) / threads;

    auto start = std::chrono::high_resolution_clock::now();

    /**
     * Double-buffering pattern with 2 streams processing 16 chunks:
     *
     * Stream assignment (chunk % NSTREAMS):
     *   Chunks 0, 2, 4, 6, 8, 10, 12, 14 → Stream 0 (8 chunks)
     *   Chunks 1, 3, 5, 7, 9, 11, 13, 15 → Stream 1 (8 chunks)
     *
     * Overlap pattern:
     *   - While Stream 0 transfers chunk 0 (H2D), Stream 1 is idle
     *   - While Stream 0 processes chunk 0 (Kernel), Stream 1 transfers chunk 1 (H2D)
     *   - While Stream 0 transfers chunk 0 (D2H), Stream 1 processes chunk 1 (Kernel)
     *   - While Stream 0 transfers chunk 2 (H2D), Stream 1 transfers chunk 1 (D2H)
     *   ↓ Streams now alternate continuously
     *
     * Memory layout on device:
     *   d_data[0 .. CHUNK_SIZE-1]           → Buffer for Stream 0
     *   d_data[CHUNK_SIZE .. 2*CHUNK_SIZE-1] → Buffer for Stream 1
     *
     * Each buffer: 262,144 floats = 1 MB
     * Total device memory: 2 MB (2 buffers)
     */
    for (int chunk = 0; chunk < NCHUNKS; chunk++) {
        int stream_id = chunk % NSTREAMS;  // Alternates: 0, 1, 0, 1, 0, 1, ...
        int offset = chunk * CHUNK_SIZE;    // Offset in host array

        // Stage 1: Async H2D transfer (1 MB per chunk)
        // Transfers 262,144 floats = 1,048,576 bytes asynchronously
        // Stream 0 and Stream 1 can transfer simultaneously via different DMA engines
        check_cuda_error(cudaMemcpyAsync(&d_data[stream_id * CHUNK_SIZE], &h_data[offset],
                                        CHUNK_SIZE * sizeof(float),
                                        cudaMemcpyHostToDevice, streams[stream_id]),
                        "cudaMemcpyAsync H2D");

        // Stage 2: Kernel execution
        // 1,024 blocks × 256 threads = 262,144 threads total
        // Each thread performs 100 iterations of sin/cos (200 FLOPs)
        // Total: 52.4M FLOPs per chunk
        // This compute-heavy kernel allows overlap with transfers
        process_data<<<blocks, threads, 0, streams[stream_id]>>>
            (&d_data[stream_id * CHUNK_SIZE], CHUNK_SIZE, 1.5f);

        // Stage 3: Async D2H transfer (1 MB per chunk)
        // Transfers results back to host asynchronously
        // Can overlap with H2D transfer and kernel execution in other stream
        check_cuda_error(cudaMemcpyAsync(&h_data[offset], &d_data[stream_id * CHUNK_SIZE],
                                        CHUNK_SIZE * sizeof(float),
                                        cudaMemcpyDeviceToHost, streams[stream_id]),
                        "cudaMemcpyAsync D2H");
    }

    // Wait for all streams to complete
    for (int i = 0; i < NSTREAMS; i++) {
        check_cuda_error(cudaStreamSynchronize(streams[i]), "cudaStreamSynchronize");
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

    printf("SUCCESS: Processed %d chunks using %d streams\n", NCHUNKS, NSTREAMS);
    printf("Total time: %ld ms\n", duration.count());
    printf("Per chunk: %.2f ms\n", (float)duration.count() / NCHUNKS);

    // Cleanup
    for (int i = 0; i < NSTREAMS; i++) {
        cudaStreamDestroy(streams[i]);
    }

    cudaFree(d_data);
    cudaFreeHost(h_data);

    return 0;
}
