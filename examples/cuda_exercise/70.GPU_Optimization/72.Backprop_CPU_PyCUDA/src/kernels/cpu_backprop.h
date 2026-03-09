/**
 * @file cpu_backprop.h
 * @brief CPU backpropagation header for neural network training baseline
 *
 * Provides forward pass, backward pass (gradient computation), activation
 * functions, and their gradients for fully connected (linear) layers.
 */

#pragma once

#include <chrono>
#include <cstring>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Forward pass for a fully connected layer: output = input * weights^T + bias
 *
 * @param[out] output   Output matrix [batch_size x output_dim]
 * @param[in]  input    Input matrix [batch_size x input_dim]
 * @param[in]  weights  Weight matrix [output_dim x input_dim]
 * @param[in]  bias     Bias vector [output_dim]
 * @param[in]  batch_size Number of samples in the batch
 * @param[in]  input_dim  Number of input features
 * @param[in]  output_dim Number of output features
 */
void cpu_forward(float* output, const float* input, const float* weights, const float* bias,
                int batch_size, int input_dim, int output_dim);

/**
 * @brief Backward pass: compute gradients for input, weights, and bias
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
void cpu_backward(float* grad_input, float* grad_weights, float* grad_bias,
                 const float* grad_output, const float* input, const float* weights,
                 int batch_size, int input_dim, int output_dim);

/**
 * @brief Parallel forward pass using OpenMP
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
void cpu_forward_parallel(float* output, const float* input, const float* weights, const float* bias,
                         int batch_size, int input_dim, int output_dim, int num_threads);

/**
 * @brief Parallel backward pass using OpenMP
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
void cpu_backward_parallel(float* grad_input, float* grad_weights, float* grad_bias,
                          const float* grad_output, const float* input, const float* weights,
                          int batch_size, int input_dim, int output_dim, int num_threads);

/**
 * @brief ReLU forward pass: output = max(0, input)
 *
 * @param[out] output Output array [n]
 * @param[in]  input  Input array [n]
 * @param[in]  n      Number of elements
 */
void cpu_relu_forward(float* output, const float* input, int n);

/**
 * @brief ReLU backward pass: grad_input = (input > 0) ? grad_output : 0
 *
 * @param[out] grad_input   Gradient w.r.t. input [n]
 * @param[in]  grad_output  Gradient from upstream [n]
 * @param[in]  input        Cached input from forward pass [n]
 * @param[in]  n            Number of elements
 */
void cpu_relu_backward(float* grad_input, const float* grad_output, const float* input, int n);

/**
 * @brief Sigmoid forward pass: output = 1 / (1 + exp(-input))
 *
 * @param[out] output Output array [n]
 * @param[in]  input  Input array [n]
 * @param[in]  n      Number of elements
 */
void cpu_sigmoid_forward(float* output, const float* input, int n);

/**
 * @brief Sigmoid backward pass: grad_input = grad_output * output * (1 - output)
 *
 * @param[out] grad_input   Gradient w.r.t. input [n]
 * @param[in]  grad_output  Gradient from upstream [n]
 * @param[in]  output       Cached sigmoid output from forward pass [n]
 * @param[in]  n            Number of elements
 */
void cpu_sigmoid_backward(float* grad_input, const float* grad_output, const float* output, int n);

/**
 * @brief Timed forward+backward pass returning elapsed time in milliseconds
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
float cpu_forward_backward_timed(float* output, float* grad_input, float* grad_weights, float* grad_bias,
                                const float* input, const float* weights, const float* bias,
                                const float* grad_output,
                                int batch_size, int input_dim, int output_dim, const char* method);

#ifdef __cplusplus
}
#endif
