// test_stream_capture.cu - Tests for CUDA Graph stream capture

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/stream_capture.cu"

class StreamCaptureTest : public GpuTest {};

TEST_F(StreamCaptureTest, CaptureSimpleSequenceWorks) {
    const int N = 1024;
    float* h_a = new float[N];
    float* h_b = new float[N];
    float* h_c = new float[N];

    // Initialize inputs
    for (int i = 0; i < N; i++) {
        h_a[i] = static_cast<float>(i);
        h_b[i] = 1.0f;
    }

    // Allocate device memory
    float* d_a = cuda_malloc<float>(N);
    float* d_b = cuda_malloc<float>(N);
    float* d_c = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_a, h_a, N);
    cuda_memcpy_h2d(d_b, h_b, N);

    // Create stream
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // Capture graph
    cudaGraph_t graph = capture_simple_sequence(stream, d_c, d_a, d_b, N, 256);

    // Instantiate and launch
    cudaGraphExec_t graphExec;
    instantiate_and_launch_graph(graph, stream, &graphExec);

    // Copy result back
    cuda_memcpy_d2h(h_c, d_c, N);

    // Verify: c = (a + b) * 2 = (i + 1) * 2
    for (int i = 0; i < N; i++) {
        float expected = (h_a[i] + h_b[i]) * 2.0f;
        EXPECT_FLOAT_EQ(h_c[i], expected) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_c);
    delete[] h_a;
    delete[] h_b;
    delete[] h_c;
}

TEST_F(StreamCaptureTest, CaptureWithMemcpyWorks) {
    const int N = 512;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i + 1);
    }

    // Allocate device memory
    float* d_data = cuda_malloc<float>(N);
    float* d_temp = cuda_malloc<float>(N);

    // Allocate pinned host memory for async operations
    float* h_input_pinned;
    float* h_output_pinned;
    cudaMallocHost(&h_input_pinned, N * sizeof(float));
    cudaMallocHost(&h_output_pinned, N * sizeof(float));

    memcpy(h_input_pinned, h_input, N * sizeof(float));

    // Create stream
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // Capture graph with memcpy
    cudaGraph_t graph = capture_with_memcpy(stream, d_data, d_temp,
                                             h_input_pinned, h_output_pinned, N, 256);

    // Instantiate and launch
    cudaGraphExec_t graphExec;
    instantiate_and_launch_graph(graph, stream, &graphExec);

    // Copy from pinned to regular host memory
    memcpy(h_output, h_output_pinned, N * sizeof(float));

    // Verify: output = input^2
    for (int i = 0; i < N; i++) {
        float expected = h_input[i] * h_input[i];
        EXPECT_FLOAT_EQ(h_output[i], expected) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cudaFreeHost(h_input_pinned);
    cudaFreeHost(h_output_pinned);
    cuda_free(d_data);
    cuda_free(d_temp);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(StreamCaptureTest, CapturePipelineWorks) {
    const int N = 1024;
    float* h_data1 = new float[N];
    float* h_data2 = new float[N];
    float* h_result = new float[N];

    // Initialize inputs
    for (int i = 0; i < N; i++) {
        h_data1[i] = 1.0f;
        h_data2[i] = 2.0f;
    }

    // Allocate device memory
    float* d_data1 = cuda_malloc<float>(N);
    float* d_data2 = cuda_malloc<float>(N);
    float* d_result = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_data1, h_data1, N);
    cuda_memcpy_h2d(d_data2, h_data2, N);

    // Create stream
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // Capture pipeline
    cudaGraph_t graph = capture_pipeline(stream, d_data1, d_data2, d_result, N, 256);

    // Instantiate and launch
    cudaGraphExec_t graphExec;
    instantiate_and_launch_graph(graph, stream, &graphExec);

    // Copy result back
    cuda_memcpy_d2h(h_result, d_result, N);

    // Verify: result = ((1*2) + (2*3))^2 = (2 + 6)^2 = 64
    for (int i = 0; i < N; i++) {
        float expected = (h_data1[i] * 2.0f + h_data2[i] * 3.0f);
        expected = expected * expected;
        EXPECT_FLOAT_EQ(h_result[i], expected) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_data1);
    cuda_free(d_data2);
    cuda_free(d_result);
    delete[] h_data1;
    delete[] h_data2;
    delete[] h_result;
}

TEST_F(StreamCaptureTest, GraphReusabilityWorks) {
    const int N = 256;
    float* h_a = new float[N];
    float* h_b = new float[N];
    float* h_c = new float[N];

    // Initialize inputs
    for (int i = 0; i < N; i++) {
        h_a[i] = 1.0f;
        h_b[i] = 2.0f;
    }

    // Allocate device memory
    float* d_a = cuda_malloc<float>(N);
    float* d_b = cuda_malloc<float>(N);
    float* d_c = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_a, h_a, N);
    cuda_memcpy_h2d(d_b, h_b, N);

    // Create stream and graph
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    cudaGraph_t graph = capture_simple_sequence(stream, d_c, d_a, d_b, N, 256);
    cudaGraphExec_t graphExec;
    cudaGraphInstantiate(&graphExec, graph, nullptr, nullptr, 0);

    // Launch multiple times
    launch_graph_multiple_times(graphExec, stream, 5);

    // Copy result back
    cuda_memcpy_d2h(h_c, d_c, N);

    // Verify result after multiple launches
    for (int i = 0; i < N; i++) {
        float expected = (h_a[i] + h_b[i]) * 2.0f;
        EXPECT_FLOAT_EQ(h_c[i], expected) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_c);
    delete[] h_a;
    delete[] h_b;
    delete[] h_c;
}
