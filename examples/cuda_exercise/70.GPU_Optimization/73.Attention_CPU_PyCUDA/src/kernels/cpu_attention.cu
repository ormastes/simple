/**
 * @file cpu_attention.cu
 * @brief CPU-based attention mechanism implementations for baseline comparison
 *
 * This file implements various CPU attention algorithms used in transformer models:
 * - Naive scaled dot-product attention (SDPA)
 * - Causal (masked) attention for autoregressive models
 * - Multi-head attention with output projection
 * - Parallel attention using OpenMP
 * - Numerically stable softmax
 */

#include "cpu_attention.h"
#include <algorithm>
#include <cmath>
#include <vector>

#ifdef HAS_OPENMP
#include <omp.h>
#endif

/**
 * @brief Internal helper: compute softmax over a single row in-place
 *
 * Numerically stable: subtract max before exp to avoid overflow.
 *
 * @param row   Pointer to the row data (modified in-place)
 * @param cols  Number of elements in the row
 */
static void softmax_row_inplace(float* row, int cols) {
    // Find max for numerical stability
    float max_val = row[0];
    for (int j = 1; j < cols; j++) {
        if (row[j] > max_val) {
            max_val = row[j];
        }
    }

    // Compute exp and sum
    float sum_exp = 0.0f;
    for (int j = 0; j < cols; j++) {
        row[j] = expf(row[j] - max_val);
        sum_exp += row[j];
    }

    // Normalize
    float inv_sum = 1.0f / sum_exp;
    for (int j = 0; j < cols; j++) {
        row[j] *= inv_sum;
    }
}

/**
 * @brief Naive scaled dot-product attention: softmax(Q*K^T / sqrt(d_k)) * V
 *
 * Time Complexity: O(seq_len^2 * d_model)
 * Memory: O(seq_len^2) for the attention score matrix
 *
 * Steps:
 *   1. Compute scores = Q * K^T  [seq_len x seq_len]
 *   2. Scale by 1 / sqrt(d_model)
 *   3. Apply softmax row-wise
 *   4. Multiply by V to get output [seq_len x d_model]
 *
 * @param[out] output   Output matrix [seq_len x d_model]
 * @param[in]  Q        Query matrix [seq_len x d_model]
 * @param[in]  K        Key matrix [seq_len x d_model]
 * @param[in]  V        Value matrix [seq_len x d_model]
 * @param[in]  seq_len  Sequence length
 * @param[in]  d_model  Model dimension (d_k)
 */
extern "C" void cpu_sdpa_naive(float* output, const float* Q, const float* K, const float* V,
                                int seq_len, int d_model) {
    float scale = 1.0f / sqrtf(static_cast<float>(d_model));

    // Allocate attention scores matrix [seq_len x seq_len]
    std::vector<float> scores(seq_len * seq_len);

    // Step 1: Compute scores = Q * K^T, scaled by 1/sqrt(d_k)
    for (int i = 0; i < seq_len; i++) {
        for (int j = 0; j < seq_len; j++) {
            float dot = 0.0f;
            for (int d = 0; d < d_model; d++) {
                dot += Q[i * d_model + d] * K[j * d_model + d];
            }
            scores[i * seq_len + j] = dot * scale;
        }
    }

    // Step 2: Apply softmax row-wise
    for (int i = 0; i < seq_len; i++) {
        softmax_row_inplace(&scores[i * seq_len], seq_len);
    }

    // Step 3: Compute output = scores * V  [seq_len x d_model]
    for (int i = 0; i < seq_len; i++) {
        for (int d = 0; d < d_model; d++) {
            float sum = 0.0f;
            for (int j = 0; j < seq_len; j++) {
                sum += scores[i * seq_len + j] * V[j * d_model + d];
            }
            output[i * d_model + d] = sum;
        }
    }
}

/**
 * @brief Scaled dot-product attention with causal (lower-triangular) mask
 *
 * Each position i can only attend to positions j <= i. Positions j > i
 * are set to -infinity before softmax, making their contribution zero.
 * This is essential for autoregressive generation (e.g., GPT-style models).
 *
 * @param[out] output   Output matrix [seq_len x d_model]
 * @param[in]  Q        Query matrix [seq_len x d_model]
 * @param[in]  K        Key matrix [seq_len x d_model]
 * @param[in]  V        Value matrix [seq_len x d_model]
 * @param[in]  seq_len  Sequence length
 * @param[in]  d_model  Model dimension
 */
extern "C" void cpu_sdpa_causal(float* output, const float* Q, const float* K, const float* V,
                                 int seq_len, int d_model) {
    float scale = 1.0f / sqrtf(static_cast<float>(d_model));

    // Allocate attention scores matrix [seq_len x seq_len]
    std::vector<float> scores(seq_len * seq_len);

    // Step 1: Compute scores = Q * K^T with causal mask
    for (int i = 0; i < seq_len; i++) {
        // Compute scores for positions j <= i (causal: can attend to past and current)
        for (int j = 0; j <= i; j++) {
            float dot = 0.0f;
            for (int d = 0; d < d_model; d++) {
                dot += Q[i * d_model + d] * K[j * d_model + d];
            }
            scores[i * seq_len + j] = dot * scale;
        }

        // Mask future positions to -infinity
        for (int j = i + 1; j < seq_len; j++) {
            scores[i * seq_len + j] = -INFINITY;
        }
    }

    // Step 2: Apply softmax row-wise (masked positions become ~0)
    for (int i = 0; i < seq_len; i++) {
        softmax_row_inplace(&scores[i * seq_len], seq_len);
    }

    // Step 3: Compute output = scores * V
    for (int i = 0; i < seq_len; i++) {
        for (int d = 0; d < d_model; d++) {
            float sum = 0.0f;
            for (int j = 0; j < seq_len; j++) {
                sum += scores[i * seq_len + j] * V[j * d_model + d];
            }
            output[i * d_model + d] = sum;
        }
    }
}

/**
 * @brief Multi-head attention with output projection
 *
 * Splits Q, K, V into num_heads independent attention heads,
 * runs SDPA on each head, concatenates the results, and
 * projects through W_O.
 *
 * Layout:
 *   Q, K, V: [batch_size x seq_len x d_model]
 *   Per-head: [seq_len x head_dim] where head_dim = d_model / num_heads
 *   W_O: [d_model x d_model]
 *
 * @param[out] output      Output matrix [batch_size x seq_len x d_model]
 * @param[in]  Q           Query matrix [batch_size x seq_len x d_model]
 * @param[in]  K           Key matrix [batch_size x seq_len x d_model]
 * @param[in]  V           Value matrix [batch_size x seq_len x d_model]
 * @param[in]  W_O         Output projection weight [d_model x d_model]
 * @param[in]  batch_size  Batch size
 * @param[in]  seq_len     Sequence length
 * @param[in]  d_model     Model dimension (must be divisible by num_heads)
 * @param[in]  num_heads   Number of attention heads
 */
extern "C" void cpu_multi_head_attention(float* output, const float* Q, const float* K, const float* V,
                                          const float* W_O, int batch_size, int seq_len, int d_model, int num_heads) {
    int head_dim = d_model / num_heads;

    // Temporary buffers for per-head Q, K, V and output
    std::vector<float> head_Q(seq_len * head_dim);
    std::vector<float> head_K(seq_len * head_dim);
    std::vector<float> head_V(seq_len * head_dim);
    std::vector<float> head_out(seq_len * head_dim);

    // Concatenated head outputs before projection [seq_len x d_model]
    std::vector<float> concat_out(seq_len * d_model);

    for (int b = 0; b < batch_size; b++) {
        const float* Q_batch = Q + b * seq_len * d_model;
        const float* K_batch = K + b * seq_len * d_model;
        const float* V_batch = V + b * seq_len * d_model;

        // Process each head
        for (int h = 0; h < num_heads; h++) {
            // Extract per-head slices: take columns [h*head_dim .. (h+1)*head_dim)
            for (int s = 0; s < seq_len; s++) {
                for (int d = 0; d < head_dim; d++) {
                    head_Q[s * head_dim + d] = Q_batch[s * d_model + h * head_dim + d];
                    head_K[s * head_dim + d] = K_batch[s * d_model + h * head_dim + d];
                    head_V[s * head_dim + d] = V_batch[s * d_model + h * head_dim + d];
                }
            }

            // Run SDPA on this head
            cpu_sdpa_naive(head_out.data(), head_Q.data(), head_K.data(), head_V.data(),
                          seq_len, head_dim);

            // Place head output into concatenated buffer
            for (int s = 0; s < seq_len; s++) {
                for (int d = 0; d < head_dim; d++) {
                    concat_out[s * d_model + h * head_dim + d] = head_out[s * head_dim + d];
                }
            }
        }

        // Project concatenated output through W_O: output = concat_out * W_O
        // concat_out: [seq_len x d_model], W_O: [d_model x d_model]
        float* out_batch = output + b * seq_len * d_model;
        for (int s = 0; s < seq_len; s++) {
            for (int d = 0; d < d_model; d++) {
                float sum = 0.0f;
                for (int k = 0; k < d_model; k++) {
                    sum += concat_out[s * d_model + k] * W_O[k * d_model + d];
                }
                out_batch[s * d_model + d] = sum;
            }
        }
    }
}

/**
 * @brief Parallel scaled dot-product attention using OpenMP
 *
 * Same algorithm as cpu_sdpa_naive but parallelizes computation
 * across sequence positions using OpenMP threads.
 *
 * @param[out] output       Output matrix [seq_len x d_model]
 * @param[in]  Q            Query matrix [seq_len x d_model]
 * @param[in]  K            Key matrix [seq_len x d_model]
 * @param[in]  V            Value matrix [seq_len x d_model]
 * @param[in]  seq_len      Sequence length
 * @param[in]  d_model      Model dimension
 * @param[in]  num_threads  Number of threads (-1 for all available)
 */
extern "C" void cpu_sdpa_parallel(float* output, const float* Q, const float* K, const float* V,
                                   int seq_len, int d_model, int num_threads) {
#ifdef HAS_OPENMP
    if (num_threads > 0) {
        omp_set_num_threads(num_threads);
    }

    float scale = 1.0f / sqrtf(static_cast<float>(d_model));

    // Each thread works on its own rows of the attention matrix
    #pragma omp parallel
    {
        // Thread-local scores buffer for one row
        std::vector<float> row_scores(seq_len);

        #pragma omp for
        for (int i = 0; i < seq_len; i++) {
            // Compute scores for row i: Q[i] dot K[j] for all j
            for (int j = 0; j < seq_len; j++) {
                float dot = 0.0f;
                for (int d = 0; d < d_model; d++) {
                    dot += Q[i * d_model + d] * K[j * d_model + d];
                }
                row_scores[j] = dot * scale;
            }

            // Softmax over this row
            softmax_row_inplace(row_scores.data(), seq_len);

            // Compute output row: scores * V
            for (int d = 0; d < d_model; d++) {
                float sum = 0.0f;
                for (int j = 0; j < seq_len; j++) {
                    sum += row_scores[j] * V[j * d_model + d];
                }
                output[i * d_model + d] = sum;
            }
        }
    }
#else
    // Fallback to naive if OpenMP not available
    cpu_sdpa_naive(output, Q, K, V, seq_len, d_model);
#endif
}

/**
 * @brief Numerically stable softmax over rows
 *
 * For each row: subtract max, compute exp, normalize by sum.
 * This prevents overflow/underflow in the exponential.
 *
 * @param[out] output  Output matrix [rows x cols], each row sums to 1.0
 * @param[in]  input   Input matrix [rows x cols]
 * @param[in]  rows    Number of rows
 * @param[in]  cols    Number of columns
 */
extern "C" void cpu_softmax(float* output, const float* input, int rows, int cols) {
    for (int i = 0; i < rows; i++) {
        // Copy input row to output
        for (int j = 0; j < cols; j++) {
            output[i * cols + j] = input[i * cols + j];
        }

        // Apply softmax in-place
        softmax_row_inplace(&output[i * cols], cols);
    }
}

/**
 * @brief Timed attention computation returning elapsed milliseconds
 *
 * Dispatches to the requested method and measures wall-clock time.
 *
 * @param[out] output   Output matrix [seq_len x d_model]
 * @param[in]  Q        Query matrix [seq_len x d_model]
 * @param[in]  K        Key matrix [seq_len x d_model]
 * @param[in]  V        Value matrix [seq_len x d_model]
 * @param[in]  seq_len  Sequence length
 * @param[in]  d_model  Model dimension
 * @param[in]  method   "naive", "causal", or "parallel"
 * @return Elapsed time in milliseconds
 */
extern "C" float cpu_attention_timed(float* output, const float* Q, const float* K, const float* V,
                                      int seq_len, int d_model, const char* method) {
    auto start = std::chrono::high_resolution_clock::now();

    if (strcmp(method, "naive") == 0) {
        cpu_sdpa_naive(output, Q, K, V, seq_len, d_model);
    } else if (strcmp(method, "causal") == 0) {
        cpu_sdpa_causal(output, Q, K, V, seq_len, d_model);
    } else if (strcmp(method, "parallel") == 0) {
        cpu_sdpa_parallel(output, Q, K, V, seq_len, d_model, -1);
    } else {
        cpu_sdpa_naive(output, Q, K, V, seq_len, d_model);
    }

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<float, std::milli> duration = end - start;
    return duration.count();
}
