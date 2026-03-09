/**
 * @file feed_forward.h
 * @brief Feed-Forward Network (FFN) for transformer blocks
 *
 * Implements the position-wise feed-forward network used in each transformer
 * layer. The FFN consists of two linear transformations with a GELU activation
 * in between: FFN(x) = W2 * GELU(W1 * x + b1) + b2.
 *
 * The intermediate dimension (d_ff) is typically 4x the model dimension.
 */

#ifndef FEED_FORWARD_H
#define FEED_FORWARD_H

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief Weight parameters for the Feed-Forward Network
 *
 * Contains the up-projection (W1) and down-projection (W2) weight matrices
 * along with their corresponding bias vectors.
 */
struct FFNWeights {
    float* W1;   ///< Up projection weights [d_model, d_ff] (row-major)
    float* b1;   ///< Up projection bias [d_ff]
    float* W2;   ///< Down projection weights [d_ff, d_model] (row-major)
    float* b2;   ///< Down projection bias [d_model]
};

/**
 * @brief Configuration for the Feed-Forward Network
 *
 * Specifies the dimensions and hyperparameters of the FFN layer.
 */
struct FFNConfig {
    int d_model;   ///< Model dimension (input and output size)
    int d_ff;      ///< Feed-forward intermediate dimension (typically 4 * d_model)
    float dropout; ///< Dropout rate (not applied during inference)

    /**
     * @brief Construct FFN configuration
     *
     * @param d_model Model dimension
     * @param d_ff    Intermediate dimension (default: 4 * d_model)
     * @param dropout Dropout rate (default: 0.0)
     */
    FFNConfig(int d_model, int d_ff = 0, float dropout = 0.0f)
        : d_model(d_model), d_ff(d_ff > 0 ? d_ff : 4 * d_model), dropout(dropout) {}
};

/**
 * @brief Apply FFN forward pass
 *
 * Computes: output = W2 * GELU(W1 * input + b1) + b2
 *
 * The computation proceeds in three steps:
 * 1. Linear projection to intermediate dimension: hidden = W1 * input + b1
 * 2. GELU activation: hidden = GELU(hidden)
 * 3. Linear projection back to model dimension: output = W2 * hidden + b2
 *
 * @param[out] output      Output tensor [batch_size * seq_len, d_model]
 * @param[in]  input       Input tensor [batch_size * seq_len, d_model]
 * @param[in]  weights     FFN weight parameters
 * @param[in]  config      FFN configuration
 * @param[in]  batch_size  Batch size
 * @param[in]  seq_len     Sequence length
 * @param[in]  stream      CUDA stream for async execution
 *
 * @note All pointers must point to device memory
 * @note Input is treated as a 2D matrix of shape [batch_size*seq_len, d_model]
 */
void ffn_forward(float* output, const float* input, const FFNWeights& weights,
                const FFNConfig& config, int batch_size, int seq_len,
                cudaStream_t stream = 0);

/**
 * @brief Allocate FFN weight parameters on GPU
 *
 * Allocates all weight matrices and bias vectors, initialized with
 * small random values (Xavier initialization for weights, zeros for biases).
 *
 * @param config FFN configuration specifying dimensions
 * @return Allocated FFNWeights
 */
FFNWeights allocate_ffn_weights(const FFNConfig& config);

/**
 * @brief Free FFN weight parameters
 *
 * @param weights Weights to free; all pointers set to nullptr after freeing
 */
void free_ffn_weights(FFNWeights& weights);

/**
 * @brief CUDA kernel for naive matrix multiplication with bias
 *
 * Computes: C[i][j] = sum_k(A[i][k] * B[k][j]) + bias[j]
 *
 * @param[out] C    Output matrix [M, N]
 * @param[in]  A    Input matrix [M, K]
 * @param[in]  B    Weight matrix [K, N]
 * @param[in]  bias Bias vector [N], can be nullptr
 * @param[in]  M    Number of rows in A
 * @param[in]  K    Shared dimension
 * @param[in]  N    Number of columns in B
 */
__global__ void matmul_bias_kernel(float* C, const float* A, const float* B,
                                   const float* bias, int M, int K, int N);

/**
 * @brief CUDA kernel for GELU activation (in-place)
 *
 * Applies the Gaussian Error Linear Unit activation function:
 * GELU(x) = 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 *
 * @param[in,out] data  Data to apply GELU to [size]
 * @param[in]     size  Total number of elements
 */
__global__ void gelu_kernel(float* data, int size);

} // namespace llm

#endif // FEED_FORWARD_H
