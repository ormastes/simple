/**
 * @file test_pipeline.cu
 * @brief Unit tests for pipeline scheduling and double-buffering
 *
 * Validates that the double-buffer pipeline correctly overlaps
 * loading and computation, and that the accumulate kernel produces
 * expected results.
 */

#include <gtest/gtest.h>
#include "common/pipeline.h"
#include <vector>
#include <cmath>

class PipelineTest : public ::testing::Test {
protected:
    static constexpr int N = 1024;
    static constexpr size_t BUFFER_SIZE = N * sizeof(float);
};

/// Test double-buffer pipeline initialization and cleanup
TEST_F(PipelineTest, InitAndDestroy) {
    llm::DoublePipeline pipeline;
    pipeline.init(BUFFER_SIZE);

    EXPECT_NE(pipeline.buffers[0], nullptr);
    EXPECT_NE(pipeline.buffers[1], nullptr);
    EXPECT_EQ(pipeline.active_buffer, 0);
    EXPECT_EQ(pipeline.buffer_size, BUFFER_SIZE);

    pipeline.destroy();
}

/// Test buffer swap alternates active buffer
TEST_F(PipelineTest, BufferSwap) {
    llm::DoublePipeline pipeline;
    pipeline.init(BUFFER_SIZE);

    float* compute_0 = pipeline.get_compute_buffer();
    float* load_0 = pipeline.get_load_buffer();

    EXPECT_NE(compute_0, load_0);
    EXPECT_EQ(pipeline.active_buffer, 0);

    pipeline.swap();
    EXPECT_EQ(pipeline.active_buffer, 1);

    // After swap, what was the load buffer is now the compute buffer
    EXPECT_EQ(pipeline.get_compute_buffer(), load_0);
    EXPECT_EQ(pipeline.get_load_buffer(), compute_0);

    pipeline.destroy();
}

/// Test pipeline step loads data and computes correctly
TEST_F(PipelineTest, PipelineStepExecution) {
    llm::DoublePipeline pipeline;
    pipeline.init(BUFFER_SIZE);

    // Prepare host data
    std::vector<float> h_data(N, 1.0f);
    void* h_pinned;
    cudaMallocHost(&h_pinned, BUFFER_SIZE);
    memcpy(h_pinned, h_data.data(), BUFFER_SIZE);

    // Initialize compute buffer with known values
    cudaMemset(pipeline.get_compute_buffer(), 0, BUFFER_SIZE);

    // Run a pipeline step: load into inactive, compute on active
    llm::pipeline_step(pipeline, h_pinned, BUFFER_SIZE, N, 2.0f);
    pipeline.synchronize();

    // After step + swap, the previously loaded buffer is now the compute buffer
    // Verify loaded data
    std::vector<float> h_result(N);
    cudaMemcpy(h_result.data(), pipeline.get_compute_buffer(), BUFFER_SIZE, cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; ++i) {
        EXPECT_FLOAT_EQ(h_result[i], 1.0f)
            << "Loaded data mismatch at index " << i;
    }

    cudaFreeHost(h_pinned);
    pipeline.destroy();
}

/// Test accumulate expert outputs with known weights
TEST_F(PipelineTest, AccumulateExperts) {
    int num_active = 3;
    int n = 64;

    float* d_expert_outputs;
    float* d_weights;
    float* d_output;

    cudaMalloc(&d_expert_outputs, num_active * n * sizeof(float));
    cudaMalloc(&d_weights, num_active * sizeof(float));
    cudaMalloc(&d_output, n * sizeof(float));

    // Set expert outputs: expert 0 = 1.0, expert 1 = 2.0, expert 2 = 3.0
    std::vector<float> h_expert_outputs(num_active * n);
    for (int e = 0; e < num_active; ++e) {
        for (int i = 0; i < n; ++i) {
            h_expert_outputs[e * n + i] = (float)(e + 1);
        }
    }

    // Weights: [0.5, 0.3, 0.2]
    std::vector<float> h_weights = {0.5f, 0.3f, 0.2f};

    cudaMemcpy(d_expert_outputs, h_expert_outputs.data(),
               num_active * n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_weights, h_weights.data(),
               num_active * sizeof(float), cudaMemcpyHostToDevice);

    llm::accumulate_expert_outputs(d_output, d_expert_outputs, d_weights,
                                   num_active, n, 0);
    cudaDeviceSynchronize();

    // Expected: 0.5*1 + 0.3*2 + 0.2*3 = 0.5 + 0.6 + 0.6 = 1.7
    std::vector<float> h_output(n);
    cudaMemcpy(h_output.data(), d_output, n * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; ++i) {
        EXPECT_NEAR(h_output[i], 1.7f, 1e-5f)
            << "Accumulation mismatch at index " << i;
    }

    cudaFree(d_expert_outputs);
    cudaFree(d_weights);
    cudaFree(d_output);
}

/// Test accumulate with single expert equals identity
TEST_F(PipelineTest, AccumulateSingleExpert) {
    int n = 128;

    float* d_expert_outputs;
    float* d_weights;
    float* d_output;

    cudaMalloc(&d_expert_outputs, n * sizeof(float));
    cudaMalloc(&d_weights, sizeof(float));
    cudaMalloc(&d_output, n * sizeof(float));

    std::vector<float> h_vals(n);
    for (int i = 0; i < n; ++i) {
        h_vals[i] = (float)i * 0.01f;
    }
    float weight = 1.0f;

    cudaMemcpy(d_expert_outputs, h_vals.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_weights, &weight, sizeof(float), cudaMemcpyHostToDevice);

    llm::accumulate_expert_outputs(d_output, d_expert_outputs, d_weights,
                                   1, n, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_output(n);
    cudaMemcpy(h_output.data(), d_output, n * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; ++i) {
        EXPECT_NEAR(h_output[i], h_vals[i], 1e-5f);
    }

    cudaFree(d_expert_outputs);
    cudaFree(d_weights);
    cudaFree(d_output);
}
