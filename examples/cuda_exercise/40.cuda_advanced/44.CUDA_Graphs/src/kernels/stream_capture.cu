// stream_capture.cu - CUDA Graph stream capture patterns

#ifndef STREAM_CAPTURE_CU
#define STREAM_CAPTURE_CU

#include <cuda_runtime.h>

// Simple vector addition kernel for graph capture
__global__ void vector_add_kernel(float* c, const float* a, const float* b, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}

// Simple vector scale kernel
__global__ void vector_scale_kernel(float* data, float scale, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] *= scale;
    }
}

// Simple vector square kernel
__global__ void vector_square_kernel(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = data[idx] * data[idx];
    }
}

// Capture a simple kernel sequence
cudaGraph_t capture_simple_sequence(cudaStream_t stream,
                                     float* d_c, const float* d_a, const float* d_b,
                                     int n, int blockSize) {
    cudaGraph_t graph;

    int gridSize = (n + blockSize - 1) / blockSize;

    // Begin capture
    cudaStreamBeginCapture(stream, cudaStreamCaptureModeGlobal);

    // Capture kernel launches
    vector_add_kernel<<<gridSize, blockSize, 0, stream>>>(d_c, d_a, d_b, n);
    vector_scale_kernel<<<gridSize, blockSize, 0, stream>>>(d_c, 2.0f, n);

    // End capture
    cudaStreamEndCapture(stream, &graph);

    return graph;
}

// Capture sequence with memcpy operations
cudaGraph_t capture_with_memcpy(cudaStream_t stream,
                                 float* d_data, float* d_temp,
                                 const float* h_input, float* h_output,
                                 int n, int blockSize) {
    cudaGraph_t graph;

    int gridSize = (n + blockSize - 1) / blockSize;

    // Begin capture
    cudaStreamBeginCapture(stream, cudaStreamCaptureModeGlobal);

    // Capture H2D memcpy
    cudaMemcpyAsync(d_data, h_input, n * sizeof(float), cudaMemcpyHostToDevice, stream);

    // Capture kernel
    vector_square_kernel<<<gridSize, blockSize, 0, stream>>>(d_data, n);

    // Capture D2D memcpy
    cudaMemcpyAsync(d_temp, d_data, n * sizeof(float), cudaMemcpyDeviceToDevice, stream);

    // Capture D2H memcpy
    cudaMemcpyAsync(h_output, d_temp, n * sizeof(float), cudaMemcpyDeviceToHost, stream);

    // End capture
    cudaStreamEndCapture(stream, &graph);

    return graph;
}

// Capture multi-kernel pipeline
cudaGraph_t capture_pipeline(cudaStream_t stream,
                              float* d_data1, float* d_data2, float* d_result,
                              int n, int blockSize) {
    cudaGraph_t graph;

    int gridSize = (n + blockSize - 1) / blockSize;

    // Begin capture
    cudaStreamBeginCapture(stream, cudaStreamCaptureModeGlobal);

    // Stage 1: Process both inputs
    vector_scale_kernel<<<gridSize, blockSize, 0, stream>>>(d_data1, 2.0f, n);
    vector_scale_kernel<<<gridSize, blockSize, 0, stream>>>(d_data2, 3.0f, n);

    // Stage 2: Combine results
    vector_add_kernel<<<gridSize, blockSize, 0, stream>>>(d_result, d_data1, d_data2, n);

    // Stage 3: Final processing
    vector_square_kernel<<<gridSize, blockSize, 0, stream>>>(d_result, n);

    // End capture
    cudaStreamEndCapture(stream, &graph);

    return graph;
}

// Helper: Instantiate and launch graph
void instantiate_and_launch_graph(cudaGraph_t graph, cudaStream_t stream,
                                   cudaGraphExec_t* graphExec) {
    cudaGraphInstantiate(graphExec, graph, nullptr, nullptr, 0);
    cudaGraphLaunch(*graphExec, stream);
    cudaStreamSynchronize(stream);
}

// Helper: Launch graph multiple times (demonstrating reuse)
void launch_graph_multiple_times(cudaGraphExec_t graphExec, cudaStream_t stream, int iterations) {
    for (int i = 0; i < iterations; i++) {
        cudaGraphLaunch(graphExec, stream);
    }
    cudaStreamSynchronize(stream);
}

#endif // STREAM_CAPTURE_CU
