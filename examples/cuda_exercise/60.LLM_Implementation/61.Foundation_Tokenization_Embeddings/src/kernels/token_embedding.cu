/**
 * @file token_embedding.cu
 * @brief CUDA implementation of token embedding layer
 */

#include "common/token_embedding.h"
#include "cuda_utils.h"
#include <cmath>

namespace llm {

__global__ void embedding_lookup_kernel(
    const int* token_ids,
    const float* embedding_table,
    float* output,
    int batch_size,
    int seq_len,
    int embed_dim
) {
    // Grid: (seq_len, batch_size)
    // Block: (embed_dim)
    int batch_idx = blockIdx.y;
    int seq_idx = blockIdx.x;
    int embed_idx = threadIdx.x;

    if (batch_idx < batch_size && seq_idx < seq_len && embed_idx < embed_dim) {
        // Get token ID for this position
        int token_id = token_ids[batch_idx * seq_len + seq_idx];

        // Lookup embedding value
        float embedding_value = embedding_table[token_id * embed_dim + embed_idx];

        // Write to output
        int out_idx = (batch_idx * seq_len + seq_idx) * embed_dim + embed_idx;
        output[out_idx] = embedding_value;
    }
}

TokenEmbedding::TokenEmbedding(int vocab_size, int embed_dim)
    : vocab_size_(vocab_size), embed_dim_(embed_dim), d_embedding_table_(nullptr) {

    // Allocate embedding table on GPU
    size_t table_bytes = vocab_size_ * embed_dim_ * sizeof(float);
    CHECK_CUDA(cudaMalloc(&d_embedding_table_, table_bytes));

    // Initialize with random values
    InitializeEmbeddings();
}

TokenEmbedding::~TokenEmbedding() {
    if (d_embedding_table_) {
        cudaFree(d_embedding_table_);
        d_embedding_table_ = nullptr;
    }
}

void TokenEmbedding::Forward(const int* d_token_ids, float* d_output,
                            int batch_size, int seq_len) {
    // Launch configuration
    // Grid: one block per (batch, sequence position)
    // Block: one thread per embedding dimension
    dim3 grid(seq_len, batch_size);
    dim3 block(embed_dim_);

    embedding_lookup_kernel<<<grid, block>>>(
        d_token_ids,
        d_embedding_table_,
        d_output,
        batch_size,
        seq_len,
        embed_dim_
    );

    CHECK_KERNEL_LAUNCH();
}

void TokenEmbedding::InitializeEmbeddings() {
    // Xavier/Glorot initialization: N(0, 1/sqrt(embed_dim))
    std::vector<float> h_table(vocab_size_ * embed_dim_);

    std::default_random_engine gen(42);  // Fixed seed for reproducibility
    float stddev = 1.0f / std::sqrt(static_cast<float>(embed_dim_));
    std::normal_distribution<float> dist(0.0f, stddev);

    for (auto& val : h_table) {
        val = dist(gen);
    }

    // Copy to GPU
    CHECK_CUDA(cudaMemcpy(
        d_embedding_table_,
        h_table.data(),
        h_table.size() * sizeof(float),
        cudaMemcpyHostToDevice
    ));
}

void TokenEmbedding::LoadWeights(const float* h_weights, size_t num_elements) {
    if (num_elements != static_cast<size_t>(vocab_size_ * embed_dim_)) {
        throw std::runtime_error("Weight count mismatch");
    }

    CHECK_CUDA(cudaMemcpy(
        d_embedding_table_,
        h_weights,
        num_elements * sizeof(float),
        cudaMemcpyHostToDevice
    ));
}

void TokenEmbedding::GetWeights(float* h_weights) const {
    CHECK_CUDA(cudaMemcpy(
        h_weights,
        d_embedding_table_,
        vocab_size_ * embed_dim_ * sizeof(float),
        cudaMemcpyDeviceToHost
    ));
}

} // namespace llm
