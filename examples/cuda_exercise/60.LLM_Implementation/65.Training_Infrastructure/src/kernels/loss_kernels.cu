/**
 * @file loss_kernels.cu
 * @brief CUDA kernels for training loss functions
 *
 * Implements cross-entropy loss and MSE loss on GPU. Cross-entropy is the
 * standard loss for language modeling, computing -sum(target * log(softmax(logits)))
 * over the vocabulary dimension for each token position.
 */

#include <cuda_runtime.h>
#include <cfloat>
#include <cmath>

namespace llm {

/**
 * @brief Numerically stable log-softmax followed by negative log-likelihood
 *
 * For each sample, computes:
 *   loss = -logits[target] + log(sum(exp(logits)))
 * using the log-sum-exp trick for numerical stability.
 *
 * Each block processes one sample (one token position). Threads cooperate
 * via shared memory reduction to find the max and compute the sum.
 *
 * @param[in]  logits       Model output logits [batch_size, vocab_size]
 * @param[in]  targets      Target token IDs [batch_size]
 * @param[out] losses       Per-sample losses [batch_size]
 * @param[in]  batch_size   Number of samples
 * @param[in]  vocab_size   Vocabulary size (number of classes)
 */
__global__ void cross_entropy_loss_kernel(
    const float* logits,
    const int* targets,
    float* losses,
    int batch_size,
    int vocab_size
) {
    int sample = blockIdx.x;
    if (sample >= batch_size) return;

    const float* sample_logits = logits + sample * vocab_size;
    int target = targets[sample];

    // Shared memory for reductions
    extern __shared__ float shared[];

    // Step 1: Find max logit for numerical stability
    float local_max = -FLT_MAX;
    for (int i = threadIdx.x; i < vocab_size; i += blockDim.x) {
        local_max = fmaxf(local_max, sample_logits[i]);
    }
    shared[threadIdx.x] = local_max;
    __syncthreads();

    // Reduce to find global max
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            shared[threadIdx.x] = fmaxf(shared[threadIdx.x], shared[threadIdx.x + stride]);
        }
        __syncthreads();
    }
    float max_logit = shared[0];
    __syncthreads();

    // Step 2: Compute sum(exp(logits - max))
    float local_sum = 0.0f;
    for (int i = threadIdx.x; i < vocab_size; i += blockDim.x) {
        local_sum += expf(sample_logits[i] - max_logit);
    }
    shared[threadIdx.x] = local_sum;
    __syncthreads();

    // Reduce to find global sum
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            shared[threadIdx.x] += shared[threadIdx.x + stride];
        }
        __syncthreads();
    }
    float log_sum_exp = logf(shared[0]) + max_logit;

    // Step 3: Loss = -logits[target] + log_sum_exp
    if (threadIdx.x == 0) {
        losses[sample] = -sample_logits[target] + log_sum_exp;
    }
}

/**
 * @brief Launch cross-entropy loss computation
 *
 * Computes per-sample cross-entropy loss for a batch of logits and targets.
 * The mean loss across the batch can be computed by reducing the output.
 *
 * @param[in]  d_logits     Logits tensor (device) [batch_size, vocab_size]
 * @param[in]  d_targets    Target token IDs (device) [batch_size]
 * @param[out] d_losses     Per-sample losses (device) [batch_size]
 * @param[in]  batch_size   Number of samples
 * @param[in]  vocab_size   Vocabulary size
 * @param[in]  stream       CUDA stream (default: 0)
 */
void cross_entropy_loss(const float* d_logits, const int* d_targets,
                        float* d_losses, int batch_size, int vocab_size,
                        cudaStream_t stream = 0) {
    int block_size = 256;
    int shared_mem = block_size * sizeof(float);
    cross_entropy_loss_kernel<<<batch_size, block_size, shared_mem, stream>>>(
        d_logits, d_targets, d_losses, batch_size, vocab_size
    );
}

/**
 * @brief Mean Squared Error loss kernel
 *
 * Computes MSE = mean((pred - target)^2) for each sample.
 * Each block handles one sample with thread-parallel reduction.
 *
 * @param[in]  predictions  Model predictions [batch_size, dim]
 * @param[in]  targets      Target values [batch_size, dim]
 * @param[out] losses       Per-sample MSE losses [batch_size]
 * @param[in]  batch_size   Number of samples
 * @param[in]  dim          Feature dimension
 */
__global__ void mse_loss_kernel(
    const float* predictions,
    const float* targets,
    float* losses,
    int batch_size,
    int dim
) {
    int sample = blockIdx.x;
    if (sample >= batch_size) return;

    const float* pred = predictions + sample * dim;
    const float* tgt = targets + sample * dim;

    extern __shared__ float shared[];

    // Compute local sum of squared differences
    float local_sum = 0.0f;
    for (int i = threadIdx.x; i < dim; i += blockDim.x) {
        float diff = pred[i] - tgt[i];
        local_sum += diff * diff;
    }
    shared[threadIdx.x] = local_sum;
    __syncthreads();

    // Reduce
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            shared[threadIdx.x] += shared[threadIdx.x + stride];
        }
        __syncthreads();
    }

    // Write mean squared error
    if (threadIdx.x == 0) {
        losses[sample] = shared[0] / static_cast<float>(dim);
    }
}

/**
 * @brief Launch MSE loss computation
 *
 * @param[in]  d_predictions  Predictions (device) [batch_size, dim]
 * @param[in]  d_targets      Targets (device) [batch_size, dim]
 * @param[out] d_losses       Per-sample MSE losses (device) [batch_size]
 * @param[in]  batch_size     Number of samples
 * @param[in]  dim            Feature dimension
 * @param[in]  stream         CUDA stream (default: 0)
 */
void mse_loss(const float* d_predictions, const float* d_targets,
              float* d_losses, int batch_size, int dim,
              cudaStream_t stream = 0) {
    int block_size = 256;
    int shared_mem = block_size * sizeof(float);
    mse_loss_kernel<<<batch_size, block_size, shared_mem, stream>>>(
        d_predictions, d_targets, d_losses, batch_size, dim
    );
}

/**
 * @brief GRPO reward computation kernel (placeholder)
 *
 * Computes group-relative policy optimization rewards for reasoning training.
 * This is a placeholder for DeepSeek R1-style GRPO training, where
 * multiple samples per prompt are scored and rewards are normalized
 * within each group.
 *
 * @param[in]  scores        Raw scores for each sample [num_groups, num_samples]
 * @param[out] rewards       Normalized rewards [num_groups, num_samples]
 * @param[in]  num_groups    Number of prompt groups
 * @param[in]  num_samples   Number of samples per group
 */
__global__ void grpo_reward_kernel(
    const float* scores,
    float* rewards,
    int num_groups,
    int num_samples
) {
    int group = blockIdx.x;
    if (group >= num_groups) return;

    const float* group_scores = scores + group * num_samples;
    float* group_rewards = rewards + group * num_samples;

    // Compute group mean and std for normalization
    extern __shared__ float shared[];

    float local_sum = 0.0f;
    for (int i = threadIdx.x; i < num_samples; i += blockDim.x) {
        local_sum += group_scores[i];
    }
    shared[threadIdx.x] = local_sum;
    __syncthreads();

    // Reduce for mean
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            shared[threadIdx.x] += shared[threadIdx.x + stride];
        }
        __syncthreads();
    }
    float mean = shared[0] / static_cast<float>(num_samples);
    __syncthreads();

    // Compute variance
    float local_var = 0.0f;
    for (int i = threadIdx.x; i < num_samples; i += blockDim.x) {
        float diff = group_scores[i] - mean;
        local_var += diff * diff;
    }
    shared[threadIdx.x] = local_var;
    __syncthreads();

    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            shared[threadIdx.x] += shared[threadIdx.x + stride];
        }
        __syncthreads();
    }
    float std_dev = sqrtf(shared[0] / static_cast<float>(num_samples) + 1e-8f);

    // Normalize rewards: (score - mean) / std
    for (int i = threadIdx.x; i < num_samples; i += blockDim.x) {
        group_rewards[i] = (group_scores[i] - mean) / std_dev;
    }
}

} // namespace llm
