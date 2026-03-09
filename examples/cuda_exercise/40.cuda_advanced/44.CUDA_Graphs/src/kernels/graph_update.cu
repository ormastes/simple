// graph_update.cu - CUDA Graph update patterns for efficient graph reuse

#ifndef GRAPH_UPDATE_CU
#define GRAPH_UPDATE_CU

#include <cuda_runtime.h>

// Kernel for graph update demonstrations
__global__ void parametric_kernel(float* data, float param, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = data[idx] * param + param;
    }
}

// Another kernel for updates
__global__ void transform_kernel(float* output, const float* input, float scale, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = input[idx] * scale;
    }
}

// Update kernel node parameters in existing graph
void update_kernel_params(cudaGraphExec_t graphExec, cudaGraphNode_t node,
                           void* newKernelFunc, void** newArgs,
                           dim3 newGrid, dim3 newBlock) {
    cudaKernelNodeParams newParams = {0};
    newParams.func = newKernelFunc;
    newParams.gridDim = newGrid;
    newParams.blockDim = newBlock;
    newParams.sharedMemBytes = 0;
    newParams.kernelParams = newArgs;
    newParams.extra = nullptr;

    cudaGraphExecKernelNodeSetParams(graphExec, node, &newParams);
}

// Update memcpy node in existing graph
void update_memcpy_params(cudaGraphExec_t graphExec, cudaGraphNode_t node,
                           void* dst, void* src, size_t count, cudaMemcpyKind kind) {
    cudaMemcpy3DParms newParams = {0};
    newParams.srcPtr = make_cudaPitchedPtr(src, count, count / sizeof(float), 1);
    newParams.dstPtr = make_cudaPitchedPtr(dst, count, count / sizeof(float), 1);
    newParams.extent = make_cudaExtent(count, 1, 1);
    newParams.kind = kind;

    cudaGraphExecMemcpyNodeSetParams(graphExec, node, &newParams);
}

// Create updateable graph with kernel parameter changes
cudaGraph_t create_updateable_kernel_graph(float* d_data, float* param_ptr,
                                            int n, int blockSize,
                                            cudaGraphNode_t* out_node) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // Create kernel node with parameter pointer
    cudaKernelNodeParams params = {0};
    void* args[] = {&d_data, param_ptr, &n};

    params.func = (void*)parametric_kernel;
    params.gridDim = dim3((n + blockSize - 1) / blockSize);
    params.blockDim = dim3(blockSize);
    params.kernelParams = args;

    cudaGraphAddKernelNode(out_node, graph, nullptr, 0, &params);

    return graph;
}

// Create graph with updateable memcpy source
cudaGraph_t create_updateable_memcpy_graph(float* d_data, float* h_source,
                                            int n, cudaGraphNode_t* out_node) {
    cudaGraph_t graph;
    cudaGraphCreate(&graph, 0);

    // Create memcpy node
    cudaMemcpy3DParms memcpyParams = {0};
    memcpyParams.srcPtr = make_cudaPitchedPtr(h_source, n * sizeof(float), n, 1);
    memcpyParams.dstPtr = make_cudaPitchedPtr(d_data, n * sizeof(float), n, 1);
    memcpyParams.extent = make_cudaExtent(n * sizeof(float), 1, 1);
    memcpyParams.kind = cudaMemcpyHostToDevice;

    cudaGraphAddMemcpyNode(out_node, graph, nullptr, 0, &memcpyParams);

    return graph;
}

// Clone and modify graph
cudaGraph_t clone_and_modify_graph(cudaGraph_t original, float* new_data_ptr,
                                    int n, int blockSize) {
    cudaGraph_t cloned;
    cudaGraphClone(&cloned, original);

    // Get nodes from cloned graph
    size_t numNodes;
    cudaGraphGetNodes(cloned, nullptr, &numNodes);

    cudaGraphNode_t* nodes = new cudaGraphNode_t[numNodes];
    cudaGraphGetNodes(cloned, nodes, &numNodes);

    // Update first kernel node found
    for (size_t i = 0; i < numNodes; i++) {
        cudaGraphNodeType nodeType;
        cudaGraphNodeGetType(nodes[i], &nodeType);

        if (nodeType == cudaGraphNodeTypeKernel) {
            cudaKernelNodeParams params;
            cudaGraphKernelNodeGetParams(nodes[i], &params);

            // Update data pointer in parameters
            float param = 5.0f;
            void* newArgs[] = {&new_data_ptr, &param, &n};
            params.kernelParams = newArgs;

            cudaGraphKernelNodeSetParams(nodes[i], &params);
            break;
        }
    }

    delete[] nodes;
    return cloned;
}

// Demonstrate graph update workflow
struct GraphUpdateContext {
    cudaGraph_t graph;
    cudaGraphExec_t graphExec;
    cudaGraphNode_t kernelNode;
    float* d_data;
    float* h_param;  // Host-side parameter for updates
    int n;
    int blockSize;
};

// Initialize updateable graph context
void init_graph_update_context(GraphUpdateContext* ctx, float* d_data, int n, int blockSize) {
    ctx->d_data = d_data;
    ctx->n = n;
    ctx->blockSize = blockSize;

    // Allocate host parameter
    ctx->h_param = new float;
    *ctx->h_param = 1.0f;

    // Create initial graph
    ctx->graph = create_updateable_kernel_graph(d_data, ctx->h_param, n, blockSize, &ctx->kernelNode);

    // Instantiate
    cudaGraphInstantiate(&ctx->graphExec, ctx->graph, nullptr, nullptr, 0);
}

// Update parameter and re-execute
void update_and_execute(GraphUpdateContext* ctx, float new_param, cudaStream_t stream) {
    // Update parameter value
    *ctx->h_param = new_param;

    // Re-launch graph with new parameter
    cudaGraphLaunch(ctx->graphExec, stream);
    cudaStreamSynchronize(stream);
}

// Cleanup graph update context
void cleanup_graph_update_context(GraphUpdateContext* ctx) {
    delete ctx->h_param;
    cudaGraphExecDestroy(ctx->graphExec);
    cudaGraphDestroy(ctx->graph);
}

// Whole graph update (re-instantiate)
void whole_graph_update(cudaGraph_t* graph, cudaGraphExec_t* graphExec,
                         float* d_new_data, float new_param, int n, int blockSize) {
    // Destroy old executable
    if (*graphExec) {
        cudaGraphExecDestroy(*graphExec);
    }

    // Destroy old graph
    if (*graph) {
        cudaGraphDestroy(*graph);
    }

    // Create new graph
    float* param_ptr = new float;
    *param_ptr = new_param;

    cudaGraphNode_t node;
    *graph = create_updateable_kernel_graph(d_new_data, param_ptr, n, blockSize, &node);

    // Instantiate new executable
    cudaGraphInstantiate(graphExec, *graph, nullptr, nullptr, 0);

    delete param_ptr;
}

#endif // GRAPH_UPDATE_CU
