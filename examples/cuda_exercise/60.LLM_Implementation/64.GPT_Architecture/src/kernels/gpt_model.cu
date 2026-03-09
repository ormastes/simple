/**
 * @file gpt_model.cu
 * @brief CUDA implementation of GPT model forward pass
 *
 * Implements weight allocation, initialization, and the full forward pass:
 * token embedding lookup, position embedding addition, transformer blocks,
 * final layer norm, and logit computation via weight-tied LM head.
 */

#include "common/gpt_model.h"
#include "common/layer_norm.h"
#include "common/multi_head_attention.h"
#include "common/causal_attention.h"
#include "cuda_utils.h"
#include <cmath>
#include <random>
#include <vector>

namespace llm {

// Anonymous namespace to avoid duplicate symbol conflicts with module 63
namespace {

// ============================================================================
// GPU Kernels (internal to this translation unit)
// ============================================================================

/**
 * @brief Embedding lookup kernel: maps token IDs to embedding vectors
 *
 * @param[out] output      Output embeddings [batch_size * seq_len, d_model]
 * @param[in]  input_ids   Token IDs [batch_size * seq_len]
 * @param[in]  embeddings  Embedding table [vocab_size, d_model]
 * @param[in]  total_tokens  batch_size * seq_len
 * @param[in]  d_model     Embedding dimension
 */
__global__ void token_embedding_lookup_kernel(
    float* output, const int* input_ids, const float* embeddings,
    int total_tokens, int d_model
) {
    int token_idx = blockIdx.x;
    int dim_idx = threadIdx.x;

    if (token_idx < total_tokens && dim_idx < d_model) {
        int token_id = input_ids[token_idx];
        output[token_idx * d_model + dim_idx] = embeddings[token_id * d_model + dim_idx];
    }
}

/**
 * @brief Add position embeddings to token embeddings in-place
 *
 * @param[in,out] hidden    Hidden states [batch_size, seq_len, d_model]
 * @param[in]     pos_emb   Position embeddings [max_seq_len, d_model]
 * @param[in]     batch_size Number of sequences
 * @param[in]     seq_len   Sequence length
 * @param[in]     d_model   Model dimension
 */
__global__ void add_position_embeddings_kernel(
    float* hidden, const float* pos_emb,
    int batch_size, int seq_len, int d_model
) {
    int batch_idx = blockIdx.y;
    int pos_idx = blockIdx.x;
    int dim_idx = threadIdx.x;

    if (batch_idx < batch_size && pos_idx < seq_len && dim_idx < d_model) {
        int hidden_idx = (batch_idx * seq_len + pos_idx) * d_model + dim_idx;
        hidden[hidden_idx] += pos_emb[pos_idx * d_model + dim_idx];
    }
}

/**
 * @brief GELU activation kernel (approximate version used in GPT-2)
 *
 * GELU(x) = 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 *
 * @param[in,out] data   Data to apply GELU to [n]
 * @param[in]     n      Number of elements
 */
__global__ void gelu_kernel(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = data[idx];
        float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
        data[idx] = x * cdf;
    }
}

/**
 * @brief Naive matrix multiply: C = A * B
 *
 * @param[out] C  Output matrix [M, N]
 * @param[in]  A  Left matrix [M, K]
 * @param[in]  B  Right matrix [K, N]
 * @param[in]  M  Rows of A
 * @param[in]  N  Columns of B
 * @param[in]  K  Inner dimension
 */
__global__ void matmul_kernel(float* C, const float* A, const float* B,
                              int M, int N, int K) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; ++k) {
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

/**
 * @brief Matrix multiply with bias: C = A * B + bias
 *
 * @param[out] C     Output matrix [M, N]
 * @param[in]  A     Left matrix [M, K]
 * @param[in]  B     Right matrix [K, N]
 * @param[in]  bias  Bias vector [N]
 * @param[in]  M     Rows of A
 * @param[in]  N     Columns of B
 * @param[in]  K     Inner dimension
 */
__global__ void matmul_bias_kernel(float* C, const float* A, const float* B,
                                   const float* bias, int M, int N, int K) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M && col < N) {
        float sum = bias[col];
        for (int k = 0; k < K; ++k) {
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

/**
 * @brief Element-wise addition: out = a + b (residual connection)
 *
 * @param[out] out  Output [n]
 * @param[in]  a    First operand [n]
 * @param[in]  b    Second operand [n]
 * @param[in]  n    Number of elements
 */
__global__ void residual_add_kernel(float* out, const float* a, const float* b, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        out[idx] = a[idx] + b[idx];
    }
}

} // anonymous namespace

// ============================================================================
// Helper functions
// ============================================================================

/**
 * @brief Initialize weights on host with Xavier initialization and copy to device
 *
 * @param d_ptr   Device pointer to fill
 * @param count   Number of float elements
 * @param fan_in  Input dimension for Xavier scaling
 * @param seed    Random seed
 */
static void xavier_init(float* d_ptr, size_t count, int fan_in, unsigned int seed) {
    std::vector<float> h_data(count);
    std::default_random_engine gen(seed);
    float stddev = 1.0f / std::sqrt(static_cast<float>(fan_in));
    std::normal_distribution<float> dist(0.0f, stddev);
    for (auto& val : h_data) {
        val = dist(gen);
    }
    CHECK_CUDA(cudaMemcpy(d_ptr, h_data.data(), count * sizeof(float),
                          cudaMemcpyHostToDevice));
}

/**
 * @brief Initialize a device buffer to a constant value
 *
 * @param d_ptr  Device pointer
 * @param count  Number of elements
 * @param value  Value to fill with
 */
static void fill_constant(float* d_ptr, size_t count, float value) {
    std::vector<float> h_data(count, value);
    CHECK_CUDA(cudaMemcpy(d_ptr, h_data.data(), count * sizeof(float),
                          cudaMemcpyHostToDevice));
}

// ============================================================================
// GPTModel methods
// ============================================================================

void GPTModel::allocate() {
    int d = config.d_model;
    int v = config.vocab_size;
    int s = config.max_seq_len;
    int ff = config.d_ff;
    int nl = config.num_layers;
    unsigned int seed = 42;

    // Token embeddings [vocab_size, d_model]
    CHECK_CUDA(cudaMalloc(&weights.token_embeddings, (size_t)v * d * sizeof(float)));
    xavier_init(weights.token_embeddings, (size_t)v * d, d, seed++);

    // Position embeddings [max_seq_len, d_model]
    CHECK_CUDA(cudaMalloc(&weights.position_embeddings, (size_t)s * d * sizeof(float)));
    xavier_init(weights.position_embeddings, (size_t)s * d, d, seed++);

    // Transformer layers
    weights.layers = new TransformerBlockWeights[nl];
    for (int l = 0; l < nl; ++l) {
        auto& layer = weights.layers[l];

        // Attention weights: W_Q, W_K, W_V, W_O [d_model, d_model]
        CHECK_CUDA(cudaMalloc(&layer.attention.W_Q, (size_t)d * d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.attention.W_K, (size_t)d * d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.attention.W_V, (size_t)d * d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.attention.W_O, (size_t)d * d * sizeof(float)));
        xavier_init(layer.attention.W_Q, (size_t)d * d, d, seed++);
        xavier_init(layer.attention.W_K, (size_t)d * d, d, seed++);
        xavier_init(layer.attention.W_V, (size_t)d * d, d, seed++);
        xavier_init(layer.attention.W_O, (size_t)d * d, d, seed++);

        // Attention biases [d_model]
        CHECK_CUDA(cudaMalloc(&layer.attention.b_Q, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.attention.b_K, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.attention.b_V, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.attention.b_O, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMemset(layer.attention.b_Q, 0, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMemset(layer.attention.b_K, 0, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMemset(layer.attention.b_V, 0, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMemset(layer.attention.b_O, 0, (size_t)d * sizeof(float)));

        // LayerNorm1 (pre-attention)
        CHECK_CUDA(cudaMalloc(&layer.norm1.gamma, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.norm1.beta, (size_t)d * sizeof(float)));
        fill_constant(layer.norm1.gamma, d, 1.0f);
        CHECK_CUDA(cudaMemset(layer.norm1.beta, 0, (size_t)d * sizeof(float)));

        // FFN weights
        CHECK_CUDA(cudaMalloc(&layer.ffn.W1, (size_t)d * ff * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.ffn.b1, (size_t)ff * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.ffn.W2, (size_t)ff * d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.ffn.b2, (size_t)d * sizeof(float)));
        xavier_init(layer.ffn.W1, (size_t)d * ff, d, seed++);
        CHECK_CUDA(cudaMemset(layer.ffn.b1, 0, (size_t)ff * sizeof(float)));
        xavier_init(layer.ffn.W2, (size_t)ff * d, ff, seed++);
        CHECK_CUDA(cudaMemset(layer.ffn.b2, 0, (size_t)d * sizeof(float)));

        // LayerNorm2 (pre-FFN)
        CHECK_CUDA(cudaMalloc(&layer.norm2.gamma, (size_t)d * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&layer.norm2.beta, (size_t)d * sizeof(float)));
        fill_constant(layer.norm2.gamma, d, 1.0f);
        CHECK_CUDA(cudaMemset(layer.norm2.beta, 0, (size_t)d * sizeof(float)));
    }

    // Final layer norm
    CHECK_CUDA(cudaMalloc(&weights.final_norm.gamma, (size_t)d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.final_norm.beta, (size_t)d * sizeof(float)));
    fill_constant(weights.final_norm.gamma, d, 1.0f);
    CHECK_CUDA(cudaMemset(weights.final_norm.beta, 0, (size_t)d * sizeof(float)));
}

void GPTModel::deallocate() {
    int nl = config.num_layers;

    cuda_free(weights.token_embeddings);
    weights.token_embeddings = nullptr;

    cuda_free(weights.position_embeddings);
    weights.position_embeddings = nullptr;

    if (weights.layers) {
        for (int l = 0; l < nl; ++l) {
            auto& layer = weights.layers[l];
            cuda_free(layer.attention.W_Q);
            cuda_free(layer.attention.W_K);
            cuda_free(layer.attention.W_V);
            cuda_free(layer.attention.W_O);
            cuda_free(layer.attention.b_Q);
            cuda_free(layer.attention.b_K);
            cuda_free(layer.attention.b_V);
            cuda_free(layer.attention.b_O);
            cuda_free(layer.norm1.gamma);
            cuda_free(layer.norm1.beta);
            cuda_free(layer.ffn.W1);
            cuda_free(layer.ffn.b1);
            cuda_free(layer.ffn.W2);
            cuda_free(layer.ffn.b2);
            cuda_free(layer.norm2.gamma);
            cuda_free(layer.norm2.beta);
        }
        delete[] weights.layers;
        weights.layers = nullptr;
    }

    cuda_free(weights.final_norm.gamma);
    cuda_free(weights.final_norm.beta);
    weights.final_norm.gamma = nullptr;
    weights.final_norm.beta = nullptr;
}

long long GPTModel::num_parameters() const {
    return count_parameters(config);
}

void GPTModel::forward(float* logits, const int* input_ids,
                      int batch_size, int seq_len, cudaStream_t stream) {
    int d = config.d_model;
    int v = config.vocab_size;
    int ff = config.d_ff;
    int total_tokens = batch_size * seq_len;

    // Allocate intermediate buffers
    float* hidden = nullptr;     // [batch_size * seq_len, d_model]
    float* residual = nullptr;   // [batch_size * seq_len, d_model]
    float* normed = nullptr;     // [batch_size * seq_len, d_model]
    float* attn_out = nullptr;   // [batch_size * seq_len, d_model]
    float* ffn_hidden = nullptr; // [batch_size * seq_len, d_ff]
    float* ffn_out = nullptr;    // [batch_size * seq_len, d_model]
    float* Q = nullptr;          // [batch_size * seq_len, d_model]
    float* K = nullptr;          // [batch_size * seq_len, d_model]
    float* V = nullptr;          // [batch_size * seq_len, d_model]

    size_t hidden_size = (size_t)total_tokens * d;
    size_t ffn_size = (size_t)total_tokens * ff;

    CHECK_CUDA(cudaMalloc(&hidden, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&residual, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&normed, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&attn_out, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&ffn_hidden, ffn_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&ffn_out, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&Q, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&K, hidden_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&V, hidden_size * sizeof(float)));

    // Step 1: Token embedding lookup
    int block_dim = (d <= 1024) ? d : 1024;
    token_embedding_lookup_kernel<<<total_tokens, block_dim, 0, stream>>>(
        hidden, input_ids, weights.token_embeddings, total_tokens, d);

    // Step 2: Add position embeddings
    dim3 pos_grid(seq_len, batch_size);
    add_position_embeddings_kernel<<<pos_grid, block_dim, 0, stream>>>(
        hidden, weights.position_embeddings, batch_size, seq_len, d);

    // Step 3: Transformer blocks
    AttentionConfig attn_config(d, config.num_heads, config.max_seq_len);

    for (int l = 0; l < config.num_layers; ++l) {
        auto& layer = weights.layers[l];

        // Save residual
        CHECK_CUDA(cudaMemcpyAsync(residual, hidden, hidden_size * sizeof(float),
                                    cudaMemcpyDeviceToDevice, stream));

        // Pre-attention LayerNorm
        layer_norm_forward(normed, hidden, layer.norm1.gamma, layer.norm1.beta,
                          total_tokens, d, 1e-5f, stream);

        // Compute Q, K, V projections: Q = normed * W_Q + b_Q, etc.
        dim3 mm_block(16, 16);
        dim3 mm_grid((d + 15) / 16, (total_tokens + 15) / 16);

        matmul_bias_kernel<<<mm_grid, mm_block, 0, stream>>>(
            Q, normed, layer.attention.W_Q, layer.attention.b_Q,
            total_tokens, d, d);
        matmul_bias_kernel<<<mm_grid, mm_block, 0, stream>>>(
            K, normed, layer.attention.W_K, layer.attention.b_K,
            total_tokens, d, d);
        matmul_bias_kernel<<<mm_grid, mm_block, 0, stream>>>(
            V, normed, layer.attention.W_V, layer.attention.b_V,
            total_tokens, d, d);

        // Multi-head causal attention
        causal_attention_forward(attn_out, Q, K, V, attn_config,
                                batch_size, seq_len, stream);

        // Output projection: attn_out = attn_out * W_O + b_O
        matmul_bias_kernel<<<mm_grid, mm_block, 0, stream>>>(
            normed, attn_out, layer.attention.W_O, layer.attention.b_O,
            total_tokens, d, d);

        // Residual connection
        int threads = 256;
        int blocks = ((int)hidden_size + threads - 1) / threads;
        residual_add_kernel<<<blocks, threads, 0, stream>>>(
            hidden, residual, normed, (int)hidden_size);

        // Save residual for FFN
        CHECK_CUDA(cudaMemcpyAsync(residual, hidden, hidden_size * sizeof(float),
                                    cudaMemcpyDeviceToDevice, stream));

        // Pre-FFN LayerNorm
        layer_norm_forward(normed, hidden, layer.norm2.gamma, layer.norm2.beta,
                          total_tokens, d, 1e-5f, stream);

        // FFN: hidden_ff = GELU(normed * W1 + b1)
        dim3 ff_grid((ff + 15) / 16, (total_tokens + 15) / 16);
        matmul_bias_kernel<<<ff_grid, mm_block, 0, stream>>>(
            ffn_hidden, normed, layer.ffn.W1, layer.ffn.b1,
            total_tokens, ff, d);

        int gelu_blocks = ((int)ffn_size + 255) / 256;
        gelu_kernel<<<gelu_blocks, 256, 0, stream>>>(ffn_hidden, (int)ffn_size);

        // FFN: ffn_out = hidden_ff * W2 + b2
        matmul_bias_kernel<<<mm_grid, mm_block, 0, stream>>>(
            ffn_out, ffn_hidden, layer.ffn.W2, layer.ffn.b2,
            total_tokens, d, ff);

        // Residual connection
        residual_add_kernel<<<blocks, threads, 0, stream>>>(
            hidden, residual, ffn_out, (int)hidden_size);
    }

    // Step 4: Final layer norm
    layer_norm_forward(normed, hidden, weights.final_norm.gamma, weights.final_norm.beta,
                      total_tokens, d, 1e-5f, stream);

    // Step 5: LM head (weight tying): logits = normed * token_embeddings^T
    // logits[total_tokens, vocab_size] = normed[total_tokens, d_model] * embed^T[d_model, vocab_size]
    // We treat token_embeddings[vocab_size, d_model] transposed as [d_model, vocab_size]
    // So: logits[i, j] = sum_k normed[i, k] * token_embeddings[j, k]
    // This is normed * token_embeddings^T
    dim3 lm_block(16, 16);
    dim3 lm_grid((v + 15) / 16, (total_tokens + 15) / 16);

    // We need a transposed matmul: C[m,n] = A[m,k] * B^T[n,k]
    // Since our matmul_kernel does C = A * B where B is [K, N],
    // we need B to be [d_model, vocab_size] but we have [vocab_size, d_model].
    // Use a separate kernel for this.
    // For simplicity, manually compute the transposed matmul.
    // logits[row, col] = sum_k normed[row, k] * token_embeddings[col, k]

    // Launch a simple kernel for transposed matmul
    auto transposed_matmul = [] __device__(float* C, const float* A, const float* BT,
                                            int M, int N, int K,
                                            int row, int col) -> float {
        float sum = 0.0f;
        for (int k = 0; k < K; ++k) {
            sum += A[row * K + k] * BT[col * K + k];
        }
        return sum;
    };
    (void)transposed_matmul;  // Used conceptually; actual kernel below

    // We'll use a dedicated kernel inline via lambda approach won't work for __global__,
    // so we do it manually in the matmul call by pre-allocating or using the existing kernel
    // with a transposed view. For correctness and simplicity, let's just iterate.

    // Actually, let's just use a dedicated global function defined above (matmul_kernel)
    // but we need to transpose. We'll allocate a transposed copy.
    float* embed_t = nullptr;  // [d_model, vocab_size]
    CHECK_CUDA(cudaMalloc(&embed_t, (size_t)d * v * sizeof(float)));

    // Transpose token_embeddings [vocab_size, d_model] -> [d_model, vocab_size]
    // Simple transpose kernel
    {
        dim3 t_block(16, 16);
        dim3 t_grid((v + 15) / 16, (d + 15) / 16);
        // We need a transpose kernel; define one inline is not possible, so
        // we do the transpose on host conceptually. For GPU, let's just launch the
        // matmul differently. Actually, let's write the LM head matmul directly:
        // logits[i][j] = sum_k hidden[i][k] * embed[j][k]  (embed transposed)
    }

    // Use a grid over (total_tokens, vocab_size) and compute each element
    // We'll reuse matmul_kernel but need to handle the transpose properly.
    // The cleanest solution: allocate embed_t and transpose.

    // Transpose kernel (inline)
    // For each element (i, j) in output: embed_t[j][i] = embed[i][j]
    // embed is [vocab_size, d_model], embed_t is [d_model, vocab_size]
    {
        // Simple transpose: each thread handles one element
        int total = v * d;
        int t_threads = 256;
        int t_blocks = (total + t_threads - 1) / t_threads;

        // We need a __global__ kernel, but we can't define one inside a function.
        // Instead, let's just do the matmul properly. We'll compute logits inline
        // by using the matmul_kernel with a transposed approach: swap K dimension.
        // Actually matmul_kernel does C[M,N] = A[M,K] * B[K,N]
        // We want C[total_tokens, vocab_size] = normed[total_tokens, d] * embed^T[d, vocab_size]
        // If we can get embed^T, we're set. Let's use cudaMemcpy2D for transpose.

        // Simpler approach: just compute on CPU... No, this is GPU code.
        // Best approach: transpose using cudaMemcpy2D won't work for actual transpose.
        // Let's just do a simple per-element copy via our existing infrastructure.
        (void)t_blocks;
        (void)t_threads;
        (void)total;
    }

    // Use a batched approach: for each output element, compute the dot product.
    // Since we already have matmul_kernel and the LM head is not the bottleneck
    // for correctness testing, let's compute logits row by row using the standard
    // matmul with proper strides. The simplest correct approach:
    // Manually compute C = A * B^T using element-wise indexing in the matmul_kernel
    // by reinterpreting the memory layout.

    // Final approach: just compute logits[i][j] = dot(normed[i], embed[j])
    // This is equivalent to matmul_kernel with B transposed.
    // We define the transpose operation here using a simple element copy.
    {
        // Fill embed_t[k][j] = embed[j][k]
        // Launch total elements threads, each computes its (k, j) from a linear index
        // But we can't define a kernel here. We'll do it via cudaMemcpy.
        // Host-side transpose then copy:
        std::vector<float> h_embed((size_t)v * d);
        CHECK_CUDA(cudaMemcpy(h_embed.data(), weights.token_embeddings,
                              (size_t)v * d * sizeof(float), cudaMemcpyDeviceToHost));
        std::vector<float> h_embed_t((size_t)d * v);
        for (int i = 0; i < v; ++i) {
            for (int j = 0; j < d; ++j) {
                h_embed_t[j * v + i] = h_embed[i * d + j];
            }
        }
        CHECK_CUDA(cudaMemcpy(embed_t, h_embed_t.data(),
                              (size_t)d * v * sizeof(float), cudaMemcpyHostToDevice));
    }

    // Now compute logits = normed * embed_t (standard matmul)
    matmul_kernel<<<lm_grid, lm_block, 0, stream>>>(
        logits, normed, embed_t, total_tokens, v, d);

    // Free temporary buffers
    cuda_free(embed_t);
    cuda_free(hidden);
    cuda_free(residual);
    cuda_free(normed);
    cuda_free(attn_out);
    cuda_free(ffn_hidden);
    cuda_free(ffn_out);
    cuda_free(Q);
    cuda_free(K);
    cuda_free(V);
}

} // namespace llm
