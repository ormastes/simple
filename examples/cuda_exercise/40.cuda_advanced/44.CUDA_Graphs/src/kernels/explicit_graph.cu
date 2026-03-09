// explicit_graph.cu - Explicit CUDA Graph creation and node management

#ifndef EXPLICIT_GRAPH_CU
#define EXPLICIT_GRAPH_CU

#include <cuda_runtime.h>

// Simple increment kernel for explicit graph nodes
__global__ void increment_kernel(float* data, float value, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] += value;
    }
}

// Simple multiply kernel
__global__ void multiply_kernel(float* data, float factor, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] *= factor;
    }
}

// Create graph with single kernel node
cudaGraph_t create_single_kernel_graph(float* d_data, float value, int n, int blockSize) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // Set up kernel node parameters
    cudaGraphNode_t kernelNode;
    cudaKernelNodeParams kernelParams = {0};

    void* kernelArgs[] = {&d_data, &value, &n};

    kernelParams.func = (void*)increment_kernel;
    kernelParams.gridDim = dim3((n + blockSize - 1) / blockSize);
    kernelParams.blockDim = dim3(blockSize);
    kernelParams.sharedMemBytes = 0;
    kernelParams.kernelParams = kernelArgs;
    kernelParams.extra = nullptr;

    // Add kernel node (no dependencies)
    cudaGraphAddKernelNode(&kernelNode, graph, nullptr, 0, &kernelParams);

    return graph;
}

// Create graph with sequential kernel nodes
cudaGraph_t create_sequential_graph(float* d_data, int n, int blockSize) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // First kernel: increment by 10
    cudaGraphNode_t node1;
    cudaKernelNodeParams params1 = {0};
    float value1 = 10.0f;
    void* args1[] = {&d_data, &value1, &n};

    params1.func = (void*)increment_kernel;
    params1.gridDim = dim3((n + blockSize - 1) / blockSize);
    params1.blockDim = dim3(blockSize);
    params1.kernelParams = args1;

    cudaGraphAddKernelNode(&node1, graph, nullptr, 0, &params1);

    // Second kernel: multiply by 2 (depends on node1)
    cudaGraphNode_t node2;
    cudaKernelNodeParams params2 = {0};
    float value2 = 2.0f;
    void* args2[] = {&d_data, &value2, &n};

    params2.func = (void*)multiply_kernel;
    params2.gridDim = dim3((n + blockSize - 1) / blockSize);
    params2.blockDim = dim3(blockSize);
    params2.kernelParams = args2;

    cudaGraphAddKernelNode(&node2, graph, &node1, 1, &params2);

    // Third kernel: increment by 5 (depends on node2)
    cudaGraphNode_t node3;
    cudaKernelNodeParams params3 = {0};
    float value3 = 5.0f;
    void* args3[] = {&d_data, &value3, &n};

    params3.func = (void*)increment_kernel;
    params3.gridDim = dim3((n + blockSize - 1) / blockSize);
    params3.blockDim = dim3(blockSize);
    params3.kernelParams = args3;

    cudaGraphAddKernelNode(&node3, graph, &node2, 1, &params3);

    return graph;
}

// Create graph with memcpy nodes
cudaGraph_t create_graph_with_memcpy(float* d_data, const float* h_input, float* h_output,
                                      int n, int blockSize) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // H2D memcpy node
    cudaGraphNode_t memcpyH2D;
    cudaMemcpy3DParms h2dParams = {0};
    h2dParams.srcPtr = make_cudaPitchedPtr((void*)h_input, n * sizeof(float), n, 1);
    h2dParams.dstPtr = make_cudaPitchedPtr(d_data, n * sizeof(float), n, 1);
    h2dParams.extent = make_cudaExtent(n * sizeof(float), 1, 1);
    h2dParams.kind = cudaMemcpyHostToDevice;

    cudaGraphAddMemcpyNode(&memcpyH2D, graph, nullptr, 0, &h2dParams);

    // Kernel node (depends on H2D)
    cudaGraphNode_t kernelNode;
    cudaKernelNodeParams kernelParams = {0};
    float value = 100.0f;
    void* kernelArgs[] = {&d_data, &value, &n};

    kernelParams.func = (void*)increment_kernel;
    kernelParams.gridDim = dim3((n + blockSize - 1) / blockSize);
    kernelParams.blockDim = dim3(blockSize);
    kernelParams.kernelParams = kernelArgs;

    cudaGraphAddKernelNode(&kernelNode, graph, &memcpyH2D, 1, &kernelParams);

    // D2H memcpy node (depends on kernel)
    cudaGraphNode_t memcpyD2H;
    cudaMemcpy3DParms d2hParams = {0};
    d2hParams.srcPtr = make_cudaPitchedPtr(d_data, n * sizeof(float), n, 1);
    d2hParams.dstPtr = make_cudaPitchedPtr(h_output, n * sizeof(float), n, 1);
    d2hParams.extent = make_cudaExtent(n * sizeof(float), 1, 1);
    d2hParams.kind = cudaMemcpyDeviceToHost;

    cudaGraphAddMemcpyNode(&memcpyD2H, graph, &kernelNode, 1, &d2hParams);

    return graph;
}

// Create graph with memset node
cudaGraph_t create_graph_with_memset(float* d_data, int n, int blockSize) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // Memset node
    cudaGraphNode_t memsetNode;
    cudaMemsetParams memsetParams = {0};
    memsetParams.dst = d_data;
    memsetParams.value = 0;
    memsetParams.pitch = 0;
    memsetParams.elementSize = sizeof(float);
    memsetParams.width = n;
    memsetParams.height = 1;

    cudaGraphAddMemsetNode(&memsetNode, graph, nullptr, 0, &memsetParams);

    // Kernel node (depends on memset)
    cudaGraphNode_t kernelNode;
    cudaKernelNodeParams kernelParams = {0};
    float value = 42.0f;
    void* kernelArgs[] = {&d_data, &value, &n};

    kernelParams.func = (void*)increment_kernel;
    kernelParams.gridDim = dim3((n + blockSize - 1) / blockSize);
    kernelParams.blockDim = dim3(blockSize);
    kernelParams.kernelParams = kernelArgs;

    cudaGraphAddKernelNode(&kernelNode, graph, &memsetNode, 1, &kernelParams);

    return graph;
}

// Create graph with parallel branches
cudaGraph_t create_parallel_graph(float* d_data1, float* d_data2, float* d_result,
                                   int n, int blockSize) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // Branch 1: Process d_data1
    cudaGraphNode_t branch1;
    cudaKernelNodeParams params1 = {0};
    float value1 = 2.0f;
    void* args1[] = {&d_data1, &value1, &n};

    params1.func = (void*)multiply_kernel;
    params1.gridDim = dim3((n + blockSize - 1) / blockSize);
    params1.blockDim = dim3(blockSize);
    params1.kernelParams = args1;

    cudaGraphAddKernelNode(&branch1, graph, nullptr, 0, &params1);

    // Branch 2: Process d_data2 (parallel with branch1)
    cudaGraphNode_t branch2;
    cudaKernelNodeParams params2 = {0};
    float value2 = 3.0f;
    void* args2[] = {&d_data2, &value2, &n};

    params2.func = (void*)multiply_kernel;
    params2.gridDim = dim3((n + blockSize - 1) / blockSize);
    params2.blockDim = dim3(blockSize);
    params2.kernelParams = args2;

    cudaGraphAddKernelNode(&branch2, graph, nullptr, 0, &params2);

    // Merge: Add results (depends on both branches)
    cudaGraphNode_t mergeNode;
    cudaKernelNodeParams mergeParams = {0};

    // For simplicity, use multiply_kernel on result (in real code, would use add kernel)
    float mergeValue = 1.0f;
    void* mergeArgs[] = {&d_result, &mergeValue, &n};

    mergeParams.func = (void*)multiply_kernel;
    mergeParams.gridDim = dim3((n + blockSize - 1) / blockSize);
    mergeParams.blockDim = dim3(blockSize);
    mergeParams.kernelParams = mergeArgs;

    cudaGraphNode_t deps[] = {branch1, branch2};
    cudaGraphAddKernelNode(&mergeNode, graph, deps, 2, &mergeParams);

    return graph;
}

#endif // EXPLICIT_GRAPH_CU
