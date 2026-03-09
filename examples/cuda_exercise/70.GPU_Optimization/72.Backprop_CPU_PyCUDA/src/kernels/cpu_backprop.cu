/**
 * @file cpu_backprop.cu
 * @brief CPU-based backpropagation implementations for baseline comparison
 *
 * This file implements various CPU backpropagation algorithms for neural network
 * training:
 * - Naive forward and backward passes for fully connected layers
 * - Activation functions (ReLU, Sigmoid) and their gradients
 * - Multi-threaded parallel implementations using OpenMP
 * - Timed forward+backward pass for benchmarking
 */

#include "cpu_backprop.h"
#include <algorithm>
#include <cmath>

#ifdef HAS_OPENMP
#include <omp.h>
#endif

/**
 * @brief Forward pass for a fully connected layer: output = input * weights^T + bias
 *
 * Computes the linear transformation for each sample in the batch.
 * Time Complexity: O(batch_size * input_dim * output_dim)
 *
 * @param[out] output   Output matrix [batch_size x output_dim]
 * @param[in]  input    Input matrix [batch_size x input_dim]
 * @param[in]  weights  Weight matrix [output_dim x input_dim]
 * @param[in]  bias     Bias vector [output_dim]
 * @param[in]  batch_size Number of samples in the batch
 * @param[in]  input_dim  Number of input features
 * @param[in]  output_dim Number of output features
 */
extern "C" void cpu_forward(float* output, const float* input, const float* weights, const float* bias,
                            int batch_size, int input_dim, int output_dim) {
    for (int b = 0; b < batch_size; b++) {
        for (int o = 0; o < output_dim; o++) {
            float sum = bias[o];
            for (int i = 0; i < input_dim; i++) {
                sum += input[b * input_dim + i] * weights[o * input_dim + i];
            }
            output[b * output_dim + o] = sum;
        }
    }
}

/**
 * @brief Backward pass: compute gradients for input, weights, and bias
 *
 * Implements the chain rule for gradient propagation through a linear layer:
 * - grad_input  = grad_output * weights      (for propagation to previous layer)
 * - grad_weights = grad_output^T * input      (for weight update)
 * - grad_bias   = sum(grad_output, dim=0)     (for bias update)
 *
 * @param[out] grad_input   Gradient w.r.t. input [batch_size x input_dim]
 * @param[out] grad_weights Gradient w.r.t. weights [output_dim x input_dim]
 * @param[out] grad_bias    Gradient w.r.t. bias [output_dim]
 * @param[in]  grad_output  Gradient from upstream [batch_size x output_dim]
 * @param[in]  input        Cached input from forward pass [batch_size x input_dim]
 * @param[in]  weights      Weight matrix [output_dim x input_dim]
 * @param[in]  batch_size   Number of samples in the batch
 * @param[in]  input_dim    Number of input features
 * @param[in]  output_dim   Number of output features
 */
extern "C" void cpu_backward(float* grad_input, float* grad_weights, float* grad_bias,
                             const float* grad_output, const float* input, const float* weights,
                             int batch_size, int input_dim, int output_dim) {
    // Gradient w.r.t. input: grad_input = grad_output * weights
    for (int b = 0; b < batch_size; b++) {
        for (int i = 0; i < input_dim; i++) {
            float sum = 0.0f;
            for (int o = 0; o < output_dim; o++) {
                sum += grad_output[b * output_dim + o] * weights[o * input_dim + i];
            }
            grad_input[b * input_dim + i] = sum;
        }
    }

    // Gradient w.r.t. weights: grad_weights = grad_output^T * input
    for (int o = 0; o < output_dim; o++) {
        for (int i = 0; i < input_dim; i++) {
            float sum = 0.0f;
            for (int b = 0; b < batch_size; b++) {
                sum += grad_output[b * output_dim + o] * input[b * input_dim + i];
            }
            grad_weights[o * input_dim + i] = sum;
        }
    }

    // Gradient w.r.t. bias: grad_bias = sum(grad_output, dim=0)
    for (int o = 0; o < output_dim; o++) {
        float sum = 0.0f;
        for (int b = 0; b < batch_size; b++) {
            sum += grad_output[b * output_dim + o];
        }
        grad_bias[o] = sum;
    }
}

/**
 * @brief Parallel forward pass using OpenMP
 *
 * Multi-threaded forward pass that parallelizes across the batch and output
 * dimensions using OpenMP collapse(2).
 *
 * @param[out] output      Output matrix [batch_size x output_dim]
 * @param[in]  input       Input matrix [batch_size x input_dim]
 * @param[in]  weights     Weight matrix [output_dim x input_dim]
 * @param[in]  bias        Bias vector [output_dim]
 * @param[in]  batch_size  Number of samples in the batch
 * @param[in]  input_dim   Number of input features
 * @param[in]  output_dim  Number of output features
 * @param[in]  num_threads Number of OpenMP threads (-1 for all available)
 */
extern "C" void cpu_forward_parallel(float* output, const float* input, const float* weights, const float* bias,
                                     int batch_size, int input_dim, int output_dim, int num_threads) {
#ifdef HAS_OPENMP
    if (num_threads > 0) {
        omp_set_num_threads(num_threads);
    }

    #pragma omp parallel for collapse(2)
    for (int b = 0; b < batch_size; b++) {
        for (int o = 0; o < output_dim; o++) {
            float sum = bias[o];
            for (int i = 0; i < input_dim; i++) {
                sum += input[b * input_dim + i] * weights[o * input_dim + i];
            }
            output[b * output_dim + o] = sum;
        }
    }
#else
    // Fallback to naive if OpenMP not available
    cpu_forward(output, input, weights, bias, batch_size, input_dim, output_dim);
#endif
}

/**
 * @brief Parallel backward pass using OpenMP
 *
 * Multi-threaded backward pass that parallelizes gradient computations:
 * - grad_input: parallelized across batch and input dimensions
 * - grad_weights: parallelized across output and input dimensions
 * - grad_bias: parallelized across output dimension
 *
 * @param[out] grad_input   Gradient w.r.t. input [batch_size x input_dim]
 * @param[out] grad_weights Gradient w.r.t. weights [output_dim x input_dim]
 * @param[out] grad_bias    Gradient w.r.t. bias [output_dim]
 * @param[in]  grad_output  Gradient from upstream [batch_size x output_dim]
 * @param[in]  input        Cached input from forward pass [batch_size x input_dim]
 * @param[in]  weights      Weight matrix [output_dim x input_dim]
 * @param[in]  batch_size   Number of samples in the batch
 * @param[in]  input_dim    Number of input features
 * @param[in]  output_dim   Number of output features
 * @param[in]  num_threads  Number of OpenMP threads (-1 for all available)
 */
extern "C" void cpu_backward_parallel(float* grad_input, float* grad_weights, float* grad_bias,
                                      const float* grad_output, const float* input, const float* weights,
                                      int batch_size, int input_dim, int output_dim, int num_threads) {
#ifdef HAS_OPENMP
    if (num_threads > 0) {
        omp_set_num_threads(num_threads);
    }

    // Parallel gradient w.r.t. input
    #pragma omp parallel for collapse(2)
    for (int b = 0; b < batch_size; b++) {
        for (int i = 0; i < input_dim; i++) {
            float sum = 0.0f;
            for (int o = 0; o < output_dim; o++) {
                sum += grad_output[b * output_dim + o] * weights[o * input_dim + i];
            }
            grad_input[b * input_dim + i] = sum;
        }
    }

    // Parallel gradient w.r.t. weights with reduction
    #pragma omp parallel for collapse(2)
    for (int o = 0; o < output_dim; o++) {
        for (int i = 0; i < input_dim; i++) {
            float sum = 0.0f;
            for (int b = 0; b < batch_size; b++) {
                sum += grad_output[b * output_dim + o] * input[b * input_dim + i];
            }
            grad_weights[o * input_dim + i] = sum;
        }
    }

    // Parallel gradient w.r.t. bias
    #pragma omp parallel for
    for (int o = 0; o < output_dim; o++) {
        float sum = 0.0f;
        for (int b = 0; b < batch_size; b++) {
            sum += grad_output[b * output_dim + o];
        }
        grad_bias[o] = sum;
    }
#else
    // Fallback to naive if OpenMP not available
    cpu_backward(grad_input, grad_weights, grad_bias, grad_output, input, weights,
                 batch_size, input_dim, output_dim);
#endif
}

/**
 * @brief ReLU forward pass: output = max(0, input)
 *
 * Element-wise application of the Rectified Linear Unit activation function.
 *
 * @param[out] output Output array [n]
 * @param[in]  input  Input array [n]
 * @param[in]  n      Number of elements
 */
extern "C" void cpu_relu_forward(float* output, const float* input, int n) {
    for (int i = 0; i < n; i++) {
        output[i] = (input[i] > 0.0f) ? input[i] : 0.0f;
    }
}

/**
 * @brief ReLU backward pass: grad_input = (input > 0) ? grad_output : 0
 *
 * The gradient of ReLU is 1 where the input was positive, 0 otherwise.
 *
 * @param[out] grad_input   Gradient w.r.t. input [n]
 * @param[in]  grad_output  Gradient from upstream [n]
 * @param[in]  input        Cached input from forward pass [n]
 * @param[in]  n            Number of elements
 */
extern "C" void cpu_relu_backward(float* grad_input, const float* grad_output, const float* input, int n) {
    for (int i = 0; i < n; i++) {
        grad_input[i] = (input[i] > 0.0f) ? grad_output[i] : 0.0f;
    }
}

/**
 * @brief Sigmoid forward pass: output = 1 / (1 + exp(-input))
 *
 * Element-wise application of the sigmoid activation function.
 *
 * @param[out] output Output array [n]
 * @param[in]  input  Input array [n]
 * @param[in]  n      Number of elements
 */
extern "C" void cpu_sigmoid_forward(float* output, const float* input, int n) {
    for (int i = 0; i < n; i++) {
        output[i] = 1.0f / (1.0f + expf(-input[i]));
    }
}

/**
 * @brief Sigmoid backward pass: grad_input = grad_output * output * (1 - output)
 *
 * Uses the cached sigmoid output to efficiently compute the gradient.
 *
 * @param[out] grad_input   Gradient w.r.t. input [n]
 * @param[in]  grad_output  Gradient from upstream [n]
 * @param[in]  output       Cached sigmoid output from forward pass [n]
 * @param[in]  n            Number of elements
 */
extern "C" void cpu_sigmoid_backward(float* grad_input, const float* grad_output, const float* output, int n) {
    for (int i = 0; i < n; i++) {
        float sigmoid = output[i];
        grad_input[i] = grad_output[i] * sigmoid * (1.0f - sigmoid);
    }
}

/**
 * @brief Timed forward+backward pass returning elapsed time in milliseconds
 *
 * Runs both forward and backward passes and returns the total elapsed time.
 * Useful for benchmarking different implementation methods.
 *
 * @param[out] output       Output of forward pass [batch_size x output_dim]
 * @param[out] grad_input   Gradient w.r.t. input [batch_size x input_dim]
 * @param[out] grad_weights Gradient w.r.t. weights [output_dim x input_dim]
 * @param[out] grad_bias    Gradient w.r.t. bias [output_dim]
 * @param[in]  input        Input matrix [batch_size x input_dim]
 * @param[in]  weights      Weight matrix [output_dim x input_dim]
 * @param[in]  bias         Bias vector [output_dim]
 * @param[in]  grad_output  Gradient from upstream [batch_size x output_dim]
 * @param[in]  batch_size   Number of samples in the batch
 * @param[in]  input_dim    Number of input features
 * @param[in]  output_dim   Number of output features
 * @param[in]  method       Method name: "naive" or "parallel"
 * @return Elapsed time in milliseconds
 */
extern "C" float cpu_forward_backward_timed(float* output, float* grad_input, float* grad_weights, float* grad_bias,
                                            const float* input, const float* weights, const float* bias,
                                            const float* grad_output,
                                            int batch_size, int input_dim, int output_dim, const char* method) {
    auto start = std::chrono::high_resolution_clock::now();

    if (strcmp(method, "naive") == 0) {
        cpu_forward(output, input, weights, bias, batch_size, input_dim, output_dim);
        cpu_backward(grad_input, grad_weights, grad_bias, grad_output, input, weights,
                     batch_size, input_dim, output_dim);
    } else if (strcmp(method, "parallel") == 0) {
        cpu_forward_parallel(output, input, weights, bias, batch_size, input_dim, output_dim, -1);
        cpu_backward_parallel(grad_input, grad_weights, grad_bias, grad_output, input, weights,
                              batch_size, input_dim, output_dim, -1);
    } else {
        cpu_forward(output, input, weights, bias, batch_size, input_dim, output_dim);
        cpu_backward(grad_input, grad_weights, grad_bias, grad_output, input, weights,
                     batch_size, input_dim, output_dim);
    }

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<float, std::milli> duration = end - start;
    return duration.count();
}
