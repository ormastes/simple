/**
 * @file pipeline_kernels.cu
 * @brief Pipeline management for overlapping computation with NVMe loading
 *
 * Implements double-buffering and multi-stream scheduling to overlap
 * expert weight loading from NVMe with computation on already-loaded
 * experts. This is critical for hiding NVMe latency in MoE inference.
 */

#include "common/pipeline.h"
#include <cstdio>
#include <cstring>

namespace llm {

void DoublePipeline::init(size_t size) {
    buffer_size = size;
    active_buffer = 0;

    for (int i = 0; i < 2; ++i) {
        cudaMalloc(&buffers[i], buffer_size);
        cudaStreamCreate(&streams[i]);
        cudaEventCreate(&events[i]);
    }
}

float* DoublePipeline::get_load_buffer() {
    return buffers[1 - active_buffer];
}

float* DoublePipeline::get_compute_buffer() {
    return buffers[active_buffer];
}

cudaStream_t DoublePipeline::get_load_stream() {
    return streams[1 - active_buffer];
}

cudaStream_t DoublePipeline::get_compute_stream() {
    return streams[active_buffer];
}

void DoublePipeline::swap() {
    // Wait for both stages to complete
    cudaEventRecord(events[active_buffer], streams[active_buffer]);
    cudaEventRecord(events[1 - active_buffer], streams[1 - active_buffer]);

    cudaStreamWaitEvent(streams[0], events[1], 0);
    cudaStreamWaitEvent(streams[1], events[0], 0);

    active_buffer = 1 - active_buffer;
}

void DoublePipeline::synchronize() {
    cudaStreamSynchronize(streams[0]);
    cudaStreamSynchronize(streams[1]);
}

void DoublePipeline::destroy() {
    for (int i = 0; i < 2; ++i) {
        cudaFree(buffers[i]);
        cudaStreamDestroy(streams[i]);
        cudaEventDestroy(events[i]);
    }
}

/**
 * @brief Kernel: simple element-wise multiply-accumulate for pipeline testing
 *
 * Used to simulate computation on an expert buffer while another is loading.
 *
 * @param[in,out] data   Expert weight buffer [n]
 * @param[in]     scale  Scale factor to apply
 * @param[in]     n      Number of elements
 */
__global__ void pipeline_compute_kernel(float* data, float scale, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = data[idx] * scale + 1.0f;
    }
}

void pipeline_step(DoublePipeline& pipeline, const void* load_data,
                   size_t load_size, int compute_n, float scale) {
    // Stage 1: Load next expert into inactive buffer (async)
    if (load_data && load_size > 0) {
        cudaMemcpyAsync(pipeline.get_load_buffer(), load_data, load_size,
                       cudaMemcpyHostToDevice, pipeline.get_load_stream());
    }

    // Stage 2: Compute on active buffer (concurrent with load)
    if (compute_n > 0) {
        int threads = 256;
        int blocks = (compute_n + threads - 1) / threads;
        pipeline_compute_kernel<<<blocks, threads, 0, pipeline.get_compute_stream()>>>(
            pipeline.get_compute_buffer(), scale, compute_n);
    }

    // Swap buffers for next iteration
    pipeline.swap();
}

/**
 * @brief Kernel: accumulate results from multiple expert outputs
 *
 * Weighted sum of expert outputs based on router weights.
 *
 * @param[out] output         Combined output [n]
 * @param[in]  expert_outputs Expert outputs [num_active x n]
 * @param[in]  weights        Router weights [num_active]
 * @param[in]  num_active     Number of active experts
 * @param[in]  n              Output dimension
 */
__global__ void accumulate_experts_kernel(float* output,
                                          const float* expert_outputs,
                                          const float* weights,
                                          int num_active, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float sum = 0.0f;
        for (int e = 0; e < num_active; ++e) {
            sum += weights[e] * expert_outputs[e * n + idx];
        }
        output[idx] = sum;
    }
}

void accumulate_expert_outputs(float* output, const float* expert_outputs,
                               const float* weights, int num_active, int n,
                               cudaStream_t stream) {
    int threads = 256;
    int blocks = (n + threads - 1) / threads;
    accumulate_experts_kernel<<<blocks, threads, 0, stream>>>(
        output, expert_outputs, weights, num_active, n);
}

} // namespace llm
