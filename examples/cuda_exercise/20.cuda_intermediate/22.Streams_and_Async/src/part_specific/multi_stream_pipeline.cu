/**
 * Multi-Stream Pipeline Pattern (Part 22)
 *
 * Demonstrates three-stage pipeline with concurrent stream execution:
 * Stage 1: Preprocess data (H2D transfer + sqrt transformation)
 * Stage 2: Transform data (complex trigonometric operations)
 * Stage 3: Reduce data (parallel reduction to single value)
 *
 * Configuration with concrete numbers:
 * - 4 streams processing 64 segments concurrently
 * - Each segment: 65,536 elements (2^16)
 * - Total data: 4,194,304 elements (64 segments × 65,536)
 * - Each stream processes: 16 segments (64 / 4)
 *
 * Pipeline timeline example (first 4 segments):
 * Time →   0ms        20ms       40ms       60ms       80ms
 * Stream 0: [H2D+S1] [S2----] [S3]
 * Stream 1:           [H2D+S1] [S2----] [S3]
 * Stream 2:                     [H2D+S1] [S2----] [S3]
 * Stream 3:                               [H2D+S1] [S2----] [S3]
 *
 * Where: H2D=Host-to-Device, S1=Stage1, S2=Stage2, S3=Stage3
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>

// Configuration: 64 segments of 65,536 elements each
#define SEGMENT_SIZE (1<<16)  // 65,536 elements per segment
#define NUM_SEGMENTS 64        // Total segments to process
#define NUM_STREAMS 4          // Concurrent streams for overlap

/**
 * Stage 1: Preprocessing kernel
 * Applies sqrt transformation to input data
 * Example: With 256 threads/block and 256 blocks:
 *   Total threads = 256 × 256 = 65,536 threads (matches SEGMENT_SIZE)
 *   Each thread processes exactly 1 element
 */
__global__ void stage1_preprocess(float* data, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        data[idx] = sqrtf(fabs(data[idx])) + 1.0f;
    }
}

/**
 * Stage 2: Transform kernel (compute-intensive)
 * Applies 50 iterations of trigonometric operations
 * Example: With 256 threads/block and 256 blocks:
 *   - Each thread performs 50 sin/cos operations
 *   - Total operations per segment: 65,536 threads × 50 iterations = 3.2M operations
 *   - This is intentionally compute-heavy to demonstrate overlap with transfers
 */
__global__ void stage2_transform(float* input, float* output, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        float val = input[idx];
        // Heavy computation: 50 iterations of sin/cos
        // Allows memory transfers in other streams to overlap with this kernel
        for (int i = 0; i < 50; i++) {
            val = sinf(val) * 2.0f + cosf(val);
        }
        output[idx] = val;
    }
}

/**
 * Stage 3: Parallel reduction kernel
 * Reduces segment data to single value using shared memory
 * Example: With 256 threads/block and 256 blocks processing 65,536 elements:
 *   - Each block reduces 256 elements to 1
 *   - 256 blocks produce 256 partial sums
 *   - Final atomic add combines all 256 partial sums
 *
 * Reduction steps within each block:
 *   Iteration 1: 256 threads → 128 sums (threads 0-127 add from 128-255)
 *   Iteration 2: 128 threads → 64 sums
 *   Iteration 3: 64 threads → 32 sums
 *   Iteration 4: 32 threads → 16 sums
 *   Iteration 5: 16 threads → 8 sums
 *   Iteration 6: 8 threads → 4 sums
 *   Iteration 7: 4 threads → 2 sums
 *   Iteration 8: 2 threads → 1 sum (stored in sdata[0])
 */
__global__ void stage3_reduce(float* input, float* output, int size) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + tid;

    // Load data into shared memory
    sdata[tid] = (idx < size) ? input[idx] : 0.0f;
    __syncthreads();

    // Parallel reduction in shared memory
    // Each iteration halves the number of active threads
    for (int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Thread 0 atomically adds block's result to global output
    if (tid == 0) {
        atomicAdd(output, sdata[0]);
    }
}

class StreamPipeline {
private:
    int numStreams;
    std::vector<cudaStream_t> streams;
    std::vector<cudaEvent_t> events;

public:
    StreamPipeline(int n) : numStreams(n) {
        streams.resize(numStreams);
        events.resize(numStreams * 3);

        for (int i = 0; i < numStreams; i++) {
            cudaStreamCreate(&streams[i]);
        }

        for (int i = 0; i < numStreams * 3; i++) {
            cudaEventCreate(&events[i]);
        }
    }

    ~StreamPipeline() {
        for (auto& stream : streams) {
            cudaStreamDestroy(stream);
        }
        for (auto& event : events) {
            cudaEventDestroy(event);
        }
    }

    cudaStream_t getStream(int idx) {
        return streams[idx % numStreams];
    }

    cudaEvent_t getEvent(int streamIdx, int stage) {
        return events[streamIdx * 3 + stage];
    }

    void synchronize_all() {
        for (auto& stream : streams) {
            cudaStreamSynchronize(stream);
        }
    }
};

int main() {
    printf("Multi-Stream Pipeline Example\n");
    printf("==============================\n\n");

    const int total_size = SEGMENT_SIZE * NUM_SEGMENTS;

    // Allocate pinned host memory
    float *h_input, *h_output;
    cudaMallocHost(&h_input, total_size * sizeof(float));
    cudaMallocHost(&h_output, NUM_SEGMENTS * sizeof(float));

    // Initialize input data
    for (int i = 0; i < total_size; i++) {
        h_input[i] = (float)(i % 1000) / 1000.0f - 0.5f;
    }

    // Allocate device memory
    float *d_input, *d_temp, *d_output, *d_result;
    cudaMalloc(&d_input, SEGMENT_SIZE * NUM_STREAMS * sizeof(float));
    cudaMalloc(&d_temp, SEGMENT_SIZE * NUM_STREAMS * sizeof(float));
    cudaMalloc(&d_output, NUM_STREAMS * sizeof(float));
    cudaMalloc(&d_result, sizeof(float));
    cudaMemset(d_result, 0, sizeof(float));

    StreamPipeline pipeline(NUM_STREAMS);

    int threads = 256;
    int blocks = (SEGMENT_SIZE + threads - 1) / threads;

    /**
     * Multi-stage pipeline execution with concrete numbers:
     *
     * Processing 64 segments with 4 streams:
     *   Segment 0 → Stream 0, Segment 1 → Stream 1, Segment 2 → Stream 2, Segment 3 → Stream 3
     *   Segment 4 → Stream 0 (reuse), Segment 5 → Stream 1 (reuse), ...
     *
     * Each segment flows through 3 stages in order:
     *   1. H2D transfer (65,536 floats = 262 KB) + Stage 1 kernel
     *   2. Stage 2 kernel (compute-intensive, enables overlap)
     *   3. Stage 3 kernel (reduction)
     *
     * Stream reuse pattern (seg % NUM_STREAMS):
     *   seg 0, 4, 8, 12, ... → Stream 0
     *   seg 1, 5, 9, 13, ... → Stream 1
     *   seg 2, 6, 10, 14, ... → Stream 2
     *   seg 3, 7, 11, 15, ... → Stream 3
     *
     * At steady state (after initial ramp-up), all 4 streams are active:
     *   Stream 0: Processing segment 4 while Stream 1 processes segment 5, etc.
     *   This creates pipeline parallelism where different segments are
     *   at different stages simultaneously.
     */
    for (int seg = 0; seg < NUM_SEGMENTS; seg++) {
        int stream_id = seg % NUM_STREAMS;  // Round-robin: 0, 1, 2, 3, 0, 1, 2, 3, ...
        cudaStream_t stream = pipeline.getStream(stream_id);
        int offset = seg * SEGMENT_SIZE;      // Offset in host array
        int d_offset = stream_id * SEGMENT_SIZE;  // Each stream has dedicated device buffer

        // Stage 1: Copy H2D and preprocess
        // Transfers 262 KB (65,536 floats × 4 bytes) asynchronously
        cudaMemcpyAsync(&d_input[d_offset], &h_input[offset],
                       SEGMENT_SIZE * sizeof(float),
                       cudaMemcpyHostToDevice, stream);
        stage1_preprocess<<<blocks, threads, 0, stream>>>(&d_input[d_offset], SEGMENT_SIZE);

        // Stage 2: Transform (compute-intensive)
        // 256 blocks × 256 threads = 65,536 threads total
        // Each thread: 50 iterations × 2 ops (sin + cos) = 100 FLOPs
        // Total: 6.5M FLOPs per segment
        stage2_transform<<<blocks, threads, 0, stream>>>
            (&d_input[d_offset], &d_temp[d_offset], SEGMENT_SIZE);

        // Stage 3: Reduce to single value
        // 256 blocks reduce 256 elements each to 256 partial sums
        // Final atomic add combines all partial sums
        size_t shmem = threads * sizeof(float);  // 256 × 4 bytes = 1 KB shared memory
        stage3_reduce<<<blocks, threads, shmem, stream>>>
            (&d_temp[d_offset], d_result, SEGMENT_SIZE);
    }

    pipeline.synchronize_all();

    // Copy final result back
    float final_result;
    cudaMemcpy(&final_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);

    printf("SUCCESS: Processed %d segments using %d-stream pipeline\n",
           NUM_SEGMENTS, NUM_STREAMS);
    printf("Final reduced value: %f\n", final_result);

    // Cleanup
    cudaFree(d_input);
    cudaFree(d_temp);
    cudaFree(d_output);
    cudaFree(d_result);
    cudaFreeHost(h_input);
    cudaFreeHost(h_output);

    return 0;
}
