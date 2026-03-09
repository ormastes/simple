/**
 * @file pipeline.h
 * @brief Double-buffer pipeline for overlapping computation with NVMe loading
 *
 * Provides a double-buffering mechanism and multi-stream scheduling to overlap
 * expert weight loading from NVMe with computation on already-loaded experts.
 * This is critical for hiding NVMe latency in MoE inference.
 */
#pragma once
#include <cuda_runtime.h>
#include <cstddef>

namespace llm {

/**
 * @brief Configuration for the pipeline scheduler
 */
struct PipelineConfig {
    int num_stages;           ///< Number of pipeline stages (typically 2 for double-buffering)
    size_t buffer_size;       ///< Size of each stage buffer in bytes
    cudaStream_t* streams;    ///< CUDA streams for each stage
};

/**
 * @brief Double-buffer pipeline state
 *
 * Manages two GPU buffers so that one can be filled (loading expert
 * from NVMe) while the other is consumed (running computation).
 */
struct DoublePipeline {
    float* buffers[2];        ///< Two GPU buffers for ping-pong
    cudaStream_t streams[2];  ///< Dedicated stream per buffer
    cudaEvent_t events[2];    ///< Events for synchronization
    int active_buffer;        ///< Index of the buffer currently being computed on
    size_t buffer_size;       ///< Size of each buffer in bytes

    /**
     * @brief Initialize double-buffer pipeline
     * @param[in] size  Size of each buffer in bytes
     */
    void init(size_t size);

    /**
     * @brief Get the buffer used for loading (the inactive one)
     * @return Pointer to the load buffer
     */
    float* get_load_buffer();

    /**
     * @brief Get the buffer used for computation (the active one)
     * @return Pointer to the compute buffer
     */
    float* get_compute_buffer();

    /**
     * @brief Get the stream used for loading
     * @return CUDA stream for the load stage
     */
    cudaStream_t get_load_stream();

    /**
     * @brief Get the stream used for computation
     * @return CUDA stream for the compute stage
     */
    cudaStream_t get_compute_stream();

    /**
     * @brief Swap active and load buffers
     *
     * After computation finishes on the active buffer and loading
     * finishes on the inactive buffer, swap them for the next step.
     */
    void swap();

    /**
     * @brief Synchronize all pipeline stages
     */
    void synchronize();

    /**
     * @brief Free all pipeline resources
     */
    void destroy();
};

/**
 * @brief Run a pipeline step: load next expert while computing on current
 *
 * @param[in,out] pipeline    Double-buffer pipeline state
 * @param[in]     load_data   Host-pinned data to load into the next buffer (can be NULL to skip)
 * @param[in]     load_size   Size of data to load in bytes
 * @param[in]     compute_n   Number of elements in the compute buffer
 * @param[in]     scale       Scale factor for the compute kernel
 */
void pipeline_step(DoublePipeline& pipeline, const void* load_data,
                   size_t load_size, int compute_n, float scale);

/**
 * @brief Accumulate weighted expert outputs on the GPU
 *
 * @param[out] output          Combined output [n] (device)
 * @param[in]  expert_outputs  Expert outputs [num_active x n] (device)
 * @param[in]  weights         Router weights [num_active] (device)
 * @param[in]  num_active      Number of active experts
 * @param[in]  n               Output dimension
 * @param[in]  stream          CUDA stream
 */
void accumulate_expert_outputs(float* output, const float* expert_outputs,
                               const float* weights, int num_active, int n,
                               cudaStream_t stream = 0);

} // namespace llm
