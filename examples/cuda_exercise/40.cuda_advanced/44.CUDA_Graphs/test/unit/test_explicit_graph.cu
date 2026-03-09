// test_explicit_graph.cu - Tests for explicit CUDA Graph creation

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/explicit_graph.cu"

class ExplicitGraphTest : public GpuTest {};

TEST_F(ExplicitGraphTest, SingleKernelGraphWorks) {
    const int N = 512;
    float* h_data = new float[N];

    for (int i = 0; i < N; i++) h_data[i] = 0.0f;

    float* d_data = cuda_malloc<float>(N);
    cuda_memcpy_h2d(d_data, h_data, N);

    cudaGraph_t graph = create_single_kernel_graph(d_data, 10.0f, N, 256);

    cudaGraphExec_t graphExec;
    cudaStream_t stream;
    cudaStreamCreate(&stream);
    cudaGraphInstantiate(&graphExec, graph, nullptr, nullptr, 0);
    cudaGraphLaunch(graphExec, stream);
    cudaStreamSynchronize(stream);

    cuda_memcpy_d2h(h_data, d_data, N);

    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data[i], 10.0f) << "At index " << i;
    }

    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_data);
    delete[] h_data;
}

TEST_F(ExplicitGraphTest, SequentialGraphWorks) {
    const int N = 512;
    float* h_data = new float[N];

    for (int i = 0; i < N; i++) h_data[i] = 0.0f;

    float* d_data = cuda_malloc<float>(N);
    cuda_memcpy_h2d(d_data, h_data, N);

    cudaGraph_t graph = create_sequential_graph(d_data, N, 256);

    cudaGraphExec_t graphExec;
    cudaStream_t stream;
    cudaStreamCreate(&stream);
    cudaGraphInstantiate(&graphExec, graph, nullptr, nullptr, 0);
    cudaGraphLaunch(graphExec, stream);
    cudaStreamSynchronize(stream);

    cuda_memcpy_d2h(h_data, d_data, N);

    // Operations: +10, *2, +5 => (0+10)*2+5 = 25
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data[i], 25.0f) << "At index " << i;
    }

    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_data);
    delete[] h_data;
}

TEST_F(ExplicitGraphTest, GraphWithMemcpyWorks) {
    const int N = 256;
    float* h_input = new float[N];
    float* h_output = new float[N];

    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
        h_output[i] = 0.0f;
    }

    float* d_data = cuda_malloc<float>(N);

    cudaGraph_t graph = create_graph_with_memcpy(d_data, h_input, h_output, N, 256);

    cudaGraphExec_t graphExec;
    cudaStream_t stream;
    cudaStreamCreate(&stream);
    cudaGraphInstantiate(&graphExec, graph, nullptr, nullptr, 0);
    cudaGraphLaunch(graphExec, stream);
    cudaStreamSynchronize(stream);

    // Verify: output = input + 100
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i] + 100.0f) << "At index " << i;
    }

    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_data);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(ExplicitGraphTest, GraphWithMemsetWorks) {
    const int N = 256;
    float* h_data = new float[N];

    for (int i = 0; i < N; i++) h_data[i] = 999.0f;

    float* d_data = cuda_malloc<float>(N);
    cuda_memcpy_h2d(d_data, h_data, N);

    cudaGraph_t graph = create_graph_with_memset(d_data, N, 256);

    cudaGraphExec_t graphExec;
    cudaStream_t stream;
    cudaStreamCreate(&stream);
    cudaGraphInstantiate(&graphExec, graph, nullptr, nullptr, 0);
    cudaGraphLaunch(graphExec, stream);
    cudaStreamSynchronize(stream);

    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify: memset to 0, then +42
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data[i], 42.0f) << "At index " << i;
    }

    cudaGraphExecDestroy(graphExec);
    cudaGraphDestroy(graph);
    cudaStreamDestroy(stream);
    cuda_free(d_data);
    delete[] h_data;
}
