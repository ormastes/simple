/**
 * Unit tests for stream-optimized kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"  // From GTestBasicLib, via CMake
#include "kernels/matrix_multiply_streams.cu"
#include "kernels/vector_ops_streams.cu"

// Test fixture
class StreamKernelsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        // Create multiple streams for testing
        num_streams = 4;
        streams = new cudaStream_t[num_streams];
        for (int i = 0; i < num_streams; i++) {
            CHECK_CUDA(cudaStreamCreate(&streams[i]));
        }

        // Create events
        CHECK_CUDA(cudaEventCreate(&start_event));
        CHECK_CUDA(cudaEventCreate(&stop_event));
    }

    void TearDown() override {
        for (int i = 0; i < num_streams; i++) {
            cudaStreamDestroy(streams[i]);
        }
        delete[] streams;

        cudaEventDestroy(start_event);
        cudaEventDestroy(stop_event);

        GpuTest::TearDown();
    }

    int num_streams;
    cudaStream_t* streams;
    cudaEvent_t start_event, stop_event;
};

// =============================================================================
// Matrix Multiplication Tests
// =============================================================================

TEST_F(StreamKernelsTest, MatMulTiledStream) {
    const int M = 128, N = 128, K = 128;
    const int TILE_SIZE = 16;

    float *h_A, *h_B, *h_C_ref, *h_C_test;
    float *d_A, *d_B, *d_C;

    size_t size_A = M * K * sizeof(float);
    size_t size_B = K * N * sizeof(float);
    size_t size_C = M * N * sizeof(float);

    // Allocate pinned memory for async transfers
    CHECK_CUDA(cudaMallocHost(&h_A, size_A));
    CHECK_CUDA(cudaMallocHost(&h_B, size_B));
    CHECK_CUDA(cudaMallocHost(&h_C_ref, size_C));
    CHECK_CUDA(cudaMallocHost(&h_C_test, size_C));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = (float)(i % 10) * 0.1f;
    for (int i = 0; i < K * N; i++) h_B[i] = (float)(i % 10) * 0.1f;

    // Device memory
    CHECK_CUDA(cudaMalloc(&d_A, size_A));
    CHECK_CUDA(cudaMalloc(&d_B, size_B));
    CHECK_CUDA(cudaMalloc(&d_C, size_C));

    // Process tiles concurrently in different streams
    dim3 block(TILE_SIZE, TILE_SIZE);
    int tiles_per_dim = (M + TILE_SIZE - 1) / TILE_SIZE;

    for (int tile_row = 0; tile_row < tiles_per_dim; tile_row++) {
        for (int tile_col = 0; tile_col < tiles_per_dim; tile_col++) {
            int stream_id = (tile_row * tiles_per_dim + tile_col) % num_streams;

            // Async copy
            CHECK_CUDA(cudaMemcpyAsync(d_A, h_A, size_A, cudaMemcpyHostToDevice, streams[stream_id]));
            CHECK_CUDA(cudaMemcpyAsync(d_B, h_B, size_B, cudaMemcpyHostToDevice, streams[stream_id]));

            // Launch kernel
            matmul_tiled_stream<TILE_SIZE><<<1, block, 0, streams[stream_id]>>>(
                d_A, d_B, d_C, M, N, K,
                tile_row * TILE_SIZE, tile_col * TILE_SIZE
            );
            CHECK_KERNEL_LAUNCH();
        }
    }

    // Wait for all streams
    for (int i = 0; i < num_streams; i++) {
        CHECK_CUDA(cudaStreamSynchronize(streams[i]));
    }

    CHECK_CUDA(cudaMemcpy(h_C_test, d_C, size_C, cudaMemcpyDeviceToHost));

    // Verify (basic check - at least some non-zero values)
    bool has_nonzero = false;
    for (int i = 0; i < M * N; i++) {
        if (h_C_test[i] != 0.0f) {
            has_nonzero = true;
            break;
        }
    }
    EXPECT_TRUE(has_nonzero);

    // Cleanup
    cudaFreeHost(h_A);
    cudaFreeHost(h_B);
    cudaFreeHost(h_C_ref);
    cudaFreeHost(h_C_test);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

// =============================================================================
// Vector Operation Tests
// =============================================================================

TEST_F(StreamKernelsTest, VectorAddChunked) {
    const int N = 1024 * num_streams;
    const int chunk_size = N / num_streams;

    float *h_a, *h_b, *h_c;
    float *d_a, *d_b, *d_c;

    // Allocate pinned memory
    CHECK_CUDA(cudaMallocHost(&h_a, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_b, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_c, N * sizeof(float)));

    // Initialize
    for (int i = 0; i < N; i++) {
        h_a[i] = (float)i;
        h_b[i] = (float)(i * 2);
    }

    CHECK_CUDA(cudaMalloc(&d_a, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_b, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_c, N * sizeof(float)));

    // Process chunks in parallel
    for (int i = 0; i < num_streams; i++) {
        int offset = i * chunk_size;

        CHECK_CUDA(cudaMemcpyAsync(&d_a[offset], &h_a[offset],
                                  chunk_size * sizeof(float),
                                  cudaMemcpyHostToDevice, streams[i]));
        CHECK_CUDA(cudaMemcpyAsync(&d_b[offset], &h_b[offset],
                                  chunk_size * sizeof(float),
                                  cudaMemcpyHostToDevice, streams[i]));

        dim3 block(256);
        dim3 grid((chunk_size + block.x - 1) / block.x);
        vector_add_chunk<<<grid, block, 0, streams[i]>>>(d_a, d_b, d_c, chunk_size, offset);

        CHECK_CUDA(cudaMemcpyAsync(&h_c[offset], &d_c[offset],
                                  chunk_size * sizeof(float),
                                  cudaMemcpyDeviceToHost, streams[i]));
    }

    // Synchronize all streams
    CHECK_CUDA(cudaDeviceSynchronize());

    // Verify
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_c[i], h_a[i] + h_b[i]);
    }

    cudaFreeHost(h_a);
    cudaFreeHost(h_b);
    cudaFreeHost(h_c);
    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
}

TEST_F(StreamKernelsTest, PipelineReduction) {
    const int N = 1024 * num_streams;
    const int chunk_size = N / num_streams;

    float *h_input, *d_input;
    float *d_partial_sums, *d_result;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_partial_sums, num_streams * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_result, sizeof(float)));

    // Initialize
    float expected_sum = 0.0f;
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
        expected_sum += h_input[i];
    }

    CHECK_CUDA(cudaMemset(d_partial_sums, 0, num_streams * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_result, 0, sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    // Stage 1: Parallel partial reductions
    for (int i = 0; i < num_streams; i++) {
        int offset = i * chunk_size;
        dim3 block(256);
        dim3 grid((chunk_size + block.x - 1) / block.x);

        reduction_stage1<<<grid, block, block.x * sizeof(float), streams[i]>>>(
            d_input, &d_partial_sums[i], chunk_size, offset
        );
    }

    // Synchronize before stage 2
    CHECK_CUDA(cudaDeviceSynchronize());

    // Stage 2: Final reduction
    dim3 block(256);
    dim3 grid(1);
    reduction_stage2<<<grid, block, 0, streams[0]>>>(d_partial_sums, d_result, num_streams);

    float h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost));

    EXPECT_NEAR(h_result, expected_sum, 1e-2f);

    cudaFreeHost(h_input);
    cudaFree(d_input);
    cudaFree(d_partial_sums);
    cudaFree(d_result);
}

TEST_F(StreamKernelsTest, EventBasedProducerConsumer) {
    const int N = 1024;

    float *d_intermediate, *d_output;
    float *h_output;

    CHECK_CUDA(cudaMalloc(&d_intermediate, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, N * sizeof(float)));

    cudaEvent_t producer_done;
    CHECK_CUDA(cudaEventCreate(&producer_done));

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    // Producer in stream 0
    vector_producer<<<grid, block, 0, streams[0]>>>(d_intermediate, N, 0, 1.0f);
    CHECK_CUDA(cudaEventRecord(producer_done, streams[0]));

    // Consumer in stream 1 waits for producer
    CHECK_CUDA(cudaStreamWaitEvent(streams[1], producer_done));
    vector_consumer<<<grid, block, 0, streams[1]>>>(d_intermediate, d_output, N, 0);

    CHECK_CUDA(cudaMemcpyAsync(h_output, d_output, N * sizeof(float),
                              cudaMemcpyDeviceToHost, streams[1]));
    CHECK_CUDA(cudaStreamSynchronize(streams[1]));

    // Verify some output exists
    bool has_output = false;
    for (int i = 0; i < N; i++) {
        if (h_output[i] > 0.0f) {
            has_output = true;
            break;
        }
    }
    EXPECT_TRUE(has_output);

    cudaEventDestroy(producer_done);
    cudaFree(d_intermediate);
    cudaFree(d_output);
    cudaFreeHost(h_output);
}

TEST_F(StreamKernelsTest, ConcurrentExecution) {
    const int N = 1024;

    float *d_data[4];
    for (int i = 0; i < 4; i++) {
        CHECK_CUDA(cudaMalloc(&d_data[i], N * sizeof(float)));
        CHECK_CUDA(cudaMemset(d_data[i], 0, N * sizeof(float)));
    }

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    // Launch kernels in different streams concurrently
    CHECK_CUDA(cudaEventRecord(start_event));

    for (int i = 0; i < 4; i++) {
        vector_scale_graph<<<grid, block, 0, streams[i % num_streams]>>>(
            d_data[i], N, (float)(i + 1)
        );
    }

    CHECK_CUDA(cudaEventRecord(stop_event));
    CHECK_CUDA(cudaEventSynchronize(stop_event));

    float elapsed_ms;
    CHECK_CUDA(cudaEventElapsedTime(&elapsed_ms, start_event, stop_event));

    std::cout << "Concurrent execution time: " << elapsed_ms << " ms\n";

    for (int i = 0; i < 4; i++) {
        cudaFree(d_data[i]);
    }
}
