/**
 * @file swiglu_ffn.h
 * @brief SwiGLU Feed-Forward Network interface
 *
 * Implements the SwiGLU activation function used in LLaMA, DeepSeek, and
 * PaLM models. SwiGLU replaces the traditional ReLU-based FFN with a
 * gated linear unit using the SiLU (Swish) activation:
 *
 *   output = W_down * (SiLU(W_gate * x) * (W_up * x))
 *
 * where SiLU(x) = x * sigmoid(x). This provides better gradient flow
 * and has been shown to improve model quality.
 */

#pragma once

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief SwiGLU FFN weight matrices
 *
 * The SwiGLU FFN uses three weight matrices instead of the standard two,
 * trading parameter count for improved activation quality.
 */
struct SwiGLUWeights {
    float* W_gate;  ///< Gate projection [d_model, d_ff]
    float* W_up;    ///< Up projection [d_model, d_ff]
    float* W_down;  ///< Down projection [d_ff, d_model]
    float* b_gate;  ///< Gate bias [d_ff] (optional, nullptr if unused)
    float* b_up;    ///< Up bias [d_ff] (optional)
    float* b_down;  ///< Down bias [d_model] (optional)
};

/**
 * @brief Compute SwiGLU FFN forward pass
 *
 * Computes: output = W_down * (SiLU(W_gate * x) * (W_up * x))
 *
 * The computation is fused into a single kernel where possible to minimize
 * global memory traffic for the intermediate activations.
 *
 * @param[out] output     Output tensor [batch, seq_len, d_model]
 * @param[in]  input      Input tensor [batch, seq_len, d_model]
 * @param[in]  weights    SwiGLU weight matrices
 * @param[in]  d_model    Model hidden dimension
 * @param[in]  d_ff       Feed-forward intermediate dimension
 * @param[in]  batch_size Number of sequences in batch
 * @param[in]  seq_len    Sequence length
 * @param[in]  stream     CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @performance Three matrix multiplications + fused element-wise ops
 */
void swiglu_forward(float* output, const float* input,
                    const SwiGLUWeights& weights,
                    int d_model, int d_ff,
                    int batch_size, int seq_len,
                    cudaStream_t stream = 0);

/**
 * @brief Allocate SwiGLU weights on device
 *
 * @param[in] d_model Model hidden dimension
 * @param[in] d_ff    Feed-forward intermediate dimension
 * @return SwiGLUWeights with allocated device pointers
 *
 * @note Caller must call free_swiglu_weights() to release memory
 */
SwiGLUWeights allocate_swiglu_weights(int d_model, int d_ff);

/**
 * @brief Free SwiGLU weights
 *
 * @param[in,out] weights Weights to free; pointers set to nullptr
 */
void free_swiglu_weights(SwiGLUWeights& weights);

/**
 * @brief Initialize SwiGLU weights with Xavier initialization
 *
 * @param[in,out] weights Pre-allocated weights to initialize
 * @param[in]     d_model Model hidden dimension
 * @param[in]     d_ff    Feed-forward intermediate dimension
 * @param[in]     seed    Random seed (default: 42)
 */
void initialize_swiglu_weights(SwiGLUWeights& weights,
                               int d_model, int d_ff,
                               unsigned int seed = 42);

} // namespace llm
