/**
 * @file test_loss.cu
 * @brief Unit tests for cross-entropy and MSE loss GPU kernels
 *
 * Verifies loss computation correctness against hand-computed expected
 * values and known edge cases.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <vector>
#include <cmath>

// Forward declarations for loss kernels (defined in loss_kernels.cu)
namespace llm {
void cross_entropy_loss(const float* d_logits, const int* d_targets,
                        float* d_losses, int batch_size, int vocab_size,
                        cudaStream_t stream);
void mse_loss(const float* d_predictions, const float* d_targets,
              float* d_losses, int batch_size, int dim,
              cudaStream_t stream);
}

namespace llm {
namespace test {

/**
 * @brief Test fixture for loss function kernel tests
 */
class LossKernelTest : public ::testing::Test {
protected:
    void SetUp() override {
        cudaSetDevice(0);
    }
};

/// Cross-entropy of a one-hot target against uniform logits
TEST_F(LossKernelTest, CrossEntropyUniformLogits) {
    const int batch_size = 1;
    const int vocab_size = 4;

    // Uniform logits [0, 0, 0, 0] -> softmax = [0.25, 0.25, 0.25, 0.25]
    std::vector<float> h_logits = {0.0f, 0.0f, 0.0f, 0.0f};
    std::vector<int> h_targets = {0};

    float* d_logits;
    int* d_targets;
    float* d_losses;
    cudaMalloc(&d_logits, batch_size * vocab_size * sizeof(float));
    cudaMalloc(&d_targets, batch_size * sizeof(int));
    cudaMalloc(&d_losses, batch_size * sizeof(float));

    cudaMemcpy(d_logits, h_logits.data(), h_logits.size() * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_targets, h_targets.data(), h_targets.size() * sizeof(int), cudaMemcpyHostToDevice);

    cross_entropy_loss(d_logits, d_targets, d_losses, batch_size, vocab_size, 0);
    cudaDeviceSynchronize();

    float h_loss;
    cudaMemcpy(&h_loss, d_losses, sizeof(float), cudaMemcpyDeviceToHost);

    // Expected: -log(1/4) = log(4) = 1.3863
    float expected = std::log(static_cast<float>(vocab_size));
    EXPECT_NEAR(h_loss, expected, 0.01f);

    cudaFree(d_logits);
    cudaFree(d_targets);
    cudaFree(d_losses);
}

/// Cross-entropy where the correct class has the highest logit
TEST_F(LossKernelTest, CrossEntropyCorrectPrediction) {
    const int batch_size = 1;
    const int vocab_size = 4;

    // Logits: target class has much higher value -> low loss
    std::vector<float> h_logits = {10.0f, 0.0f, 0.0f, 0.0f};
    std::vector<int> h_targets = {0};

    float* d_logits;
    int* d_targets;
    float* d_losses;
    cudaMalloc(&d_logits, batch_size * vocab_size * sizeof(float));
    cudaMalloc(&d_targets, batch_size * sizeof(int));
    cudaMalloc(&d_losses, batch_size * sizeof(float));

    cudaMemcpy(d_logits, h_logits.data(), h_logits.size() * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_targets, h_targets.data(), h_targets.size() * sizeof(int), cudaMemcpyHostToDevice);

    cross_entropy_loss(d_logits, d_targets, d_losses, batch_size, vocab_size, 0);
    cudaDeviceSynchronize();

    float h_loss;
    cudaMemcpy(&h_loss, d_losses, sizeof(float), cudaMemcpyDeviceToHost);

    // Loss should be close to zero for confident correct prediction
    EXPECT_LT(h_loss, 0.1f);

    cudaFree(d_logits);
    cudaFree(d_targets);
    cudaFree(d_losses);
}

/// Cross-entropy with batch of multiple samples
TEST_F(LossKernelTest, CrossEntropyBatch) {
    const int batch_size = 2;
    const int vocab_size = 3;

    // Batch of 2 samples
    std::vector<float> h_logits = {
        1.0f, 2.0f, 3.0f,   // Sample 0
        3.0f, 2.0f, 1.0f    // Sample 1
    };
    std::vector<int> h_targets = {2, 0};  // Both correct = highest logit

    float* d_logits;
    int* d_targets;
    float* d_losses;
    cudaMalloc(&d_logits, batch_size * vocab_size * sizeof(float));
    cudaMalloc(&d_targets, batch_size * sizeof(int));
    cudaMalloc(&d_losses, batch_size * sizeof(float));

    cudaMemcpy(d_logits, h_logits.data(), h_logits.size() * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_targets, h_targets.data(), h_targets.size() * sizeof(int), cudaMemcpyHostToDevice);

    cross_entropy_loss(d_logits, d_targets, d_losses, batch_size, vocab_size, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_losses(batch_size);
    cudaMemcpy(h_losses.data(), d_losses, batch_size * sizeof(float), cudaMemcpyDeviceToHost);

    // Both samples should have the same loss (symmetric logits)
    EXPECT_NEAR(h_losses[0], h_losses[1], 1e-5f);

    // Loss should be positive
    EXPECT_GT(h_losses[0], 0.0f);
    EXPECT_GT(h_losses[1], 0.0f);

    cudaFree(d_logits);
    cudaFree(d_targets);
    cudaFree(d_losses);
}

/// MSE loss for identical predictions and targets should be zero
TEST_F(LossKernelTest, MSELossZero) {
    const int batch_size = 1;
    const int dim = 4;

    std::vector<float> h_data = {1.0f, 2.0f, 3.0f, 4.0f};

    float* d_predictions;
    float* d_targets;
    float* d_losses;
    cudaMalloc(&d_predictions, batch_size * dim * sizeof(float));
    cudaMalloc(&d_targets, batch_size * dim * sizeof(float));
    cudaMalloc(&d_losses, batch_size * sizeof(float));

    cudaMemcpy(d_predictions, h_data.data(), h_data.size() * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_targets, h_data.data(), h_data.size() * sizeof(float), cudaMemcpyHostToDevice);

    mse_loss(d_predictions, d_targets, d_losses, batch_size, dim, 0);
    cudaDeviceSynchronize();

    float h_loss;
    cudaMemcpy(&h_loss, d_losses, sizeof(float), cudaMemcpyDeviceToHost);

    EXPECT_NEAR(h_loss, 0.0f, 1e-6f);

    cudaFree(d_predictions);
    cudaFree(d_targets);
    cudaFree(d_losses);
}

/// MSE loss with known difference
TEST_F(LossKernelTest, MSELossKnownValue) {
    const int batch_size = 1;
    const int dim = 4;

    // Predictions: [1, 2, 3, 4], Targets: [2, 3, 4, 5]
    // Diff: [-1, -1, -1, -1], Squared: [1, 1, 1, 1], Mean: 1.0
    std::vector<float> h_pred = {1.0f, 2.0f, 3.0f, 4.0f};
    std::vector<float> h_target = {2.0f, 3.0f, 4.0f, 5.0f};

    float* d_predictions;
    float* d_targets;
    float* d_losses;
    cudaMalloc(&d_predictions, batch_size * dim * sizeof(float));
    cudaMalloc(&d_targets, batch_size * dim * sizeof(float));
    cudaMalloc(&d_losses, batch_size * sizeof(float));

    cudaMemcpy(d_predictions, h_pred.data(), h_pred.size() * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_targets, h_target.data(), h_target.size() * sizeof(float), cudaMemcpyHostToDevice);

    mse_loss(d_predictions, d_targets, d_losses, batch_size, dim, 0);
    cudaDeviceSynchronize();

    float h_loss;
    cudaMemcpy(&h_loss, d_losses, sizeof(float), cudaMemcpyDeviceToHost);

    EXPECT_NEAR(h_loss, 1.0f, 1e-5f);

    cudaFree(d_predictions);
    cudaFree(d_targets);
    cudaFree(d_losses);
}

} // namespace test
} // namespace llm
