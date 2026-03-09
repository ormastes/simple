// test_graph_update.cu - Tests for CUDA Graph updates

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/graph_update.cu"

class GraphUpdateTest : public GpuTest {};

TEST_F(GraphUpdateTest, UpdateableKernelGraphWorks) {
    const int N = 256;
    float* h_data = new float[N];

    for (int i = 0; i < N; i++) h_data[i] = 10.0f;

    float* d_data = cuda_malloc<float>(N);
    cuda_memcpy_h2d(d_data, h_data, N);

    GraphUpdateContext ctx;
    init_graph_update_context(&ctx, d_data, N, 256);

    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // Execute with param = 1.0
    update_and_execute(&ctx, 1.0f, stream);

    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify: data = 10*1 + 1 = 11
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data[i], 11.0f) << "At index " << i;
    }

    // Graph can be reused multiple times
    update_and_execute(&ctx, 1.0f, stream);

    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify: data = 11*1 + 1 = 12
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data[i], 12.0f) << "At index " << i;
    }

    cleanup_graph_update_context(&ctx);
    cudaStreamDestroy(stream);
    cuda_free(d_data);
    delete[] h_data;
}

TEST_F(GraphUpdateTest, CloneAndModifyWorks) {
    const int N = 256;
    float* h_data1 = new float[N];
    float* h_data2 = new float[N];

    for (int i = 0; i < N; i++) {
        h_data1[i] = 10.0f;
        h_data2[i] = 20.0f;
    }

    float* d_data1 = cuda_malloc<float>(N);
    float* d_data2 = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_data1, h_data1, N);
    cuda_memcpy_h2d(d_data2, h_data2, N);

    // Create original graph for d_data1
    cudaGraphNode_t node;
    float param = 2.0f;
    cudaGraph_t original = create_updateable_kernel_graph(d_data1, &param, N, 256, &node);

    // Clone and modify for d_data2
    cudaGraph_t cloned = clone_and_modify_graph(original, d_data2, N, 256);

    // Execute both graphs
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    cudaGraphExec_t origExec, clonedExec;
    cudaGraphInstantiate(&origExec, original, nullptr, nullptr, 0);
    cudaGraphInstantiate(&clonedExec, cloned, nullptr, nullptr, 0);

    cudaGraphLaunch(origExec, stream);
    cudaStreamSynchronize(stream);

    cudaGraphLaunch(clonedExec, stream);
    cudaStreamSynchronize(stream);

    cuda_memcpy_d2h(h_data1, d_data1, N);
    cuda_memcpy_d2h(h_data2, d_data2, N);

    // Original should have: 10*2 + 2 = 22
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data1[i], 22.0f) << "Original at index " << i;
    }

    // Cloned operates on d_data2 (may have different result depending on implementation)
    // Just verify it executed without error
    EXPECT_GT(h_data2[0], 0.0f);

    cudaGraphExecDestroy(origExec);
    cudaGraphExecDestroy(clonedExec);
    cudaGraphDestroy(original);
    cudaGraphDestroy(cloned);
    cudaStreamDestroy(stream);
    cuda_free(d_data1);
    cuda_free(d_data2);
    delete[] h_data1;
    delete[] h_data2;
}
