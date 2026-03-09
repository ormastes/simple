/**
 * @file torch_api.h
 * @brief C API for CUDA operations compatible with PyTorch ctypes integration
 *
 * Provides a stable C ABI that can be loaded by Python via ctypes. Each function
 * operates on raw float pointers and shape descriptors, making it straightforward
 * to bridge between PyTorch tensors (via .data_ptr()) and CUDA kernels.
 */
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Status codes returned by all C API functions
 *
 * Every API function returns a TorchStatus to indicate success or the category
 * of failure encountered during execution.
 */
typedef enum {
    TORCH_SUCCESS = 0,                  ///< Operation completed successfully
    TORCH_ERROR_INVALID_ARGUMENT = 1,   ///< Invalid input (null pointer, bad dimensions)
    TORCH_ERROR_CUDA = 2,               ///< CUDA runtime error
    TORCH_ERROR_OUT_OF_MEMORY = 3       ///< GPU memory allocation failure
} TorchStatus;

/**
 * @brief Lightweight tensor descriptor for C API boundary
 *
 * Describes a contiguous row-major tensor by its data pointer, shape array,
 * number of dimensions, and total element count.
 */
typedef struct {
    float* data;        ///< Pointer to contiguous float data (host or device)
    int64_t* shape;     ///< Array of dimension sizes [d0, d1, ..., d_{ndim-1}]
    int ndim;           ///< Number of dimensions
    int64_t numel;      ///< Total number of elements (product of shape)
} TorchTensorDesc;

// ---- Matrix Multiplication ----

/**
 * @brief Compute C = A * B using tiled CUDA matmul kernel
 *
 * @param[out] C  Output tensor descriptor [M x N], must be pre-allocated on device
 * @param[in]  A  Input tensor descriptor  [M x K], device memory
 * @param[in]  B  Input tensor descriptor  [K x N], device memory
 * @return TORCH_SUCCESS on success, error code otherwise
 */
TorchStatus torch_matmul(TorchTensorDesc* C, const TorchTensorDesc* A,
                         const TorchTensorDesc* B);

// ---- Backpropagation (Linear Layer) ----

/**
 * @brief Forward pass of a linear layer: output = input * weight^T + bias
 *
 * @param[out] output  Result tensor [batch x out_features], device memory
 * @param[in]  input   Input tensor  [batch x in_features], device memory
 * @param[in]  weight  Weight tensor [out_features x in_features], device memory
 * @param[in]  bias    Bias tensor   [out_features] (may be NULL for no bias)
 * @return TORCH_SUCCESS on success, error code otherwise
 */
TorchStatus torch_linear_forward(TorchTensorDesc* output, const TorchTensorDesc* input,
                                 const TorchTensorDesc* weight, const TorchTensorDesc* bias);

/**
 * @brief Backward pass of a linear layer
 *
 * Computes gradients with respect to input, weight, and bias from the upstream
 * gradient of the output.
 *
 * @param[out] grad_input   Gradient w.r.t. input  [batch x in_features]
 * @param[out] grad_weight  Gradient w.r.t. weight [out_features x in_features]
 * @param[out] grad_bias    Gradient w.r.t. bias   [out_features] (may be NULL)
 * @param[in]  grad_output  Upstream gradient      [batch x out_features]
 * @param[in]  input        Saved input from forward [batch x in_features]
 * @param[in]  weight       Weight tensor           [out_features x in_features]
 * @return TORCH_SUCCESS on success, error code otherwise
 */
TorchStatus torch_linear_backward(TorchTensorDesc* grad_input, TorchTensorDesc* grad_weight,
                                  TorchTensorDesc* grad_bias,
                                  const TorchTensorDesc* grad_output,
                                  const TorchTensorDesc* input,
                                  const TorchTensorDesc* weight);

// ---- Scaled Dot-Product Attention ----

/**
 * @brief Compute scaled dot-product attention
 *
 * Implements Attention(Q,K,V) = softmax(Q * K^T / sqrt(d_k)) * V with an
 * optional causal mask that prevents attending to future positions.
 *
 * @param[out] output  Attention output [batch x seq_len x head_dim]
 * @param[in]  Q       Query tensor     [batch x seq_len x head_dim]
 * @param[in]  K       Key tensor       [batch x seq_len x head_dim]
 * @param[in]  V       Value tensor     [batch x seq_len x head_dim]
 * @param[in]  causal  Non-zero to apply causal (lower-triangular) mask
 * @return TORCH_SUCCESS on success, error code otherwise
 */
TorchStatus torch_scaled_dot_product_attention(TorchTensorDesc* output,
                                               const TorchTensorDesc* Q,
                                               const TorchTensorDesc* K,
                                               const TorchTensorDesc* V,
                                               int causal);

#ifdef __cplusplus
}
#endif
