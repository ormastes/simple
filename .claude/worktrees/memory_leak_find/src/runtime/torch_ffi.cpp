/*
 * torch_ffi.cpp - C++ bridge implementing all rt_torch_* SFFI functions
 *
 * Uses libtorch C++ API to back the Simple language torch SFFI declarations.
 * Compiled as a shared library (libspl_torch.so) and loaded at runtime.
 *
 * Handle design:
 *   - g_tensors: unordered_map<int64_t, at::Tensor> mapping i64 handles to tensors
 *   - g_streams: unordered_map<int64_t, at::cuda::CUDAStream> for CUDA streams
 *   - g_next_handle: monotonically increasing counter; 0 = invalid handle
 */

#include "runtime.h"

#include <torch/torch.h>
#include <ATen/cuda/CUDAContext.h>
#include <c10/cuda/CUDACachingAllocator.h>

#include <unordered_map>
#include <atomic>
#include <string>
#include <vector>
#include <algorithm>
#include <stdexcept>
#include <cstring>

/* ============================================================================
 * Internal Handle Tables
 * ============================================================================ */

namespace {

static std::unordered_map<int64_t, at::Tensor> g_tensors;
/* Use vector to avoid default-constructor requirement of CUDAStream in map */
static std::vector<std::pair<int64_t, at::cuda::CUDAStream>> g_streams;
static std::atomic<int64_t> g_next_handle{1};

/* No-grad guard managed by no_grad_begin/end */
static thread_local torch::NoGradGuard* g_no_grad_guard = nullptr;

/* Store a tensor in the handle table and return its handle */
static int64_t store_tensor(at::Tensor t) {
    int64_t h = g_next_handle.fetch_add(1);
    g_tensors[h] = std::move(t);
    return h;
}

/* Retrieve a tensor by handle (panics on invalid handle) */
static at::Tensor get_tensor(int64_t h) {
    auto it = g_tensors.find(h);
    if (it == g_tensors.end()) {
        spl_eprintln("rt_torch: invalid tensor handle");
        spl_panic("invalid tensor handle");
    }
    return it->second;
}

/* Convert SplArray* of i64 to std::vector<int64_t> */
static std::vector<int64_t> to_i64_vec(SplArray* a) {
    if (!a) return {};
    int64_t n = spl_array_len(a);
    std::vector<int64_t> v(n);
    for (int64_t i = 0; i < n; i++) {
        v[i] = spl_as_int(spl_array_get(a, i));
    }
    return v;
}

/* Convert SplArray* of f64 to std::vector<double> */
static std::vector<double> to_f64_vec(SplArray* a) {
    if (!a) return {};
    int64_t n = spl_array_len(a);
    std::vector<double> v(n);
    for (int64_t i = 0; i < n; i++) {
        v[i] = spl_as_float(spl_array_get(a, i));
    }
    return v;
}

/* Build SplArray* of i64 from IntArrayRef (tensor shape) */
static SplArray* from_sizes(at::IntArrayRef sizes) {
    SplArray* a = spl_array_new_i64();
    for (int64_t d : sizes) {
        spl_array_push_i64(a, d);
    }
    return a;
}

} /* anonymous namespace */

/* ============================================================================
 * All rt_torch_* functions exported as C symbols
 * ============================================================================ */

extern "C" {

/* ----------------------------------------------------------------------------
 * Library information
 * -------------------------------------------------------------------------- */

bool rt_torch_available() {
    return true;
}

char* rt_torch_version() {
    static const std::string ver =
        std::to_string(TORCH_VERSION_MAJOR) + "." +
        std::to_string(TORCH_VERSION_MINOR) + "." +
        std::to_string(TORCH_VERSION_PATCH);
    return spl_str_new(ver.c_str());
}

bool rt_torch_cuda_available() {
    return torch::cuda::is_available();
}

/* ----------------------------------------------------------------------------
 * Tensor creation
 * -------------------------------------------------------------------------- */

int64_t rt_torch_tensor_zeros(SplArray* dims) {
    return store_tensor(torch::zeros(to_i64_vec(dims)));
}

int64_t rt_torch_tensor_ones(SplArray* dims) {
    return store_tensor(torch::ones(to_i64_vec(dims)));
}

int64_t rt_torch_tensor_randn(SplArray* dims) {
    return store_tensor(torch::randn(to_i64_vec(dims)));
}

int64_t rt_torch_tensor_rand(SplArray* dims) {
    return store_tensor(torch::rand(to_i64_vec(dims)));
}

int64_t rt_torch_tensor_full(SplArray* dims, double value) {
    return store_tensor(torch::full(to_i64_vec(dims), value));
}

int64_t rt_torch_tensor_from_data(SplArray* data, SplArray* dims) {
    auto d = to_f64_vec(data);
    auto sh = to_i64_vec(dims);
    /* from_blob does not own data, clone() makes an owning copy */
    auto t = torch::from_blob(d.data(), sh, torch::kFloat64).clone();
    return store_tensor(std::move(t));
}

int64_t rt_torch_tensor_arange(double start, double end, double step) {
    return store_tensor(torch::arange(start, end, step));
}

int64_t rt_torch_tensor_linspace(double start, double end, int64_t steps) {
    return store_tensor(torch::linspace(start, end, steps));
}

int64_t rt_torch_tensor_eye(int64_t n) {
    return store_tensor(torch::eye(n));
}

int64_t rt_torch_tensor_empty(SplArray* dims) {
    return store_tensor(torch::empty(to_i64_vec(dims)));
}

/* ----------------------------------------------------------------------------
 * Element-wise arithmetic
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_add(int64_t handle, int64_t other) {
    return store_tensor(get_tensor(handle) + get_tensor(other));
}

int64_t rt_torch_torchtensor_sub(int64_t handle, int64_t other) {
    return store_tensor(get_tensor(handle) - get_tensor(other));
}

int64_t rt_torch_torchtensor_mul(int64_t handle, int64_t other) {
    return store_tensor(get_tensor(handle) * get_tensor(other));
}

int64_t rt_torch_torchtensor_div(int64_t handle, int64_t other) {
    return store_tensor(get_tensor(handle) / get_tensor(other));
}

int64_t rt_torch_torchtensor_pow(int64_t handle, double exponent) {
    return store_tensor(torch::pow(get_tensor(handle), exponent));
}

int64_t rt_torch_torchtensor_neg(int64_t handle) {
    return store_tensor(-get_tensor(handle));
}

int64_t rt_torch_torchtensor_abs(int64_t handle) {
    return store_tensor(torch::abs(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_sqrt(int64_t handle) {
    return store_tensor(torch::sqrt(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_exp(int64_t handle) {
    return store_tensor(torch::exp(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_log(int64_t handle) {
    return store_tensor(torch::log(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_add_scalar(int64_t handle, double scalar) {
    return store_tensor(get_tensor(handle) + scalar);
}

int64_t rt_torch_torchtensor_mul_scalar(int64_t handle, double scalar) {
    return store_tensor(get_tensor(handle) * scalar);
}

/* ----------------------------------------------------------------------------
 * Activation functions
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_relu(int64_t handle) {
    return store_tensor(torch::relu(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_sigmoid(int64_t handle) {
    return store_tensor(torch::sigmoid(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_tanh(int64_t handle) {
    return store_tensor(torch::tanh(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_leaky_relu(int64_t handle, double negative_slope) {
    return store_tensor(torch::leaky_relu(get_tensor(handle), negative_slope));
}

int64_t rt_torch_torchtensor_gelu(int64_t handle) {
    return store_tensor(torch::gelu(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_softmax(int64_t handle, int64_t dim) {
    return store_tensor(torch::softmax(get_tensor(handle), dim));
}

int64_t rt_torch_torchtensor_log_softmax(int64_t handle, int64_t dim) {
    return store_tensor(torch::log_softmax(get_tensor(handle), dim));
}

/* ----------------------------------------------------------------------------
 * Linear algebra
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_matmul(int64_t handle, int64_t other) {
    return store_tensor(torch::matmul(get_tensor(handle), get_tensor(other)));
}

int64_t rt_torch_torchtensor_dot(int64_t handle, int64_t other) {
    return store_tensor(torch::dot(get_tensor(handle), get_tensor(other)));
}

int64_t rt_torch_torchtensor_transpose(int64_t handle, int64_t dim0, int64_t dim1) {
    return store_tensor(get_tensor(handle).transpose(dim0, dim1));
}

int64_t rt_torch_torchtensor_t(int64_t handle) {
    return store_tensor(get_tensor(handle).t());
}

double rt_torch_torchtensor_norm(int64_t handle) {
    return get_tensor(handle).norm().item<double>();
}

double rt_torch_torchtensor_det(int64_t handle) {
    return at::linalg_det(get_tensor(handle)).item<double>();
}

int64_t rt_torch_torchtensor_inverse(int64_t handle) {
    return store_tensor(at::linalg_inv(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_svd(int64_t handle) {
    /* Return U (first component of SVD decomposition) */
    auto result = at::linalg_svd(get_tensor(handle), false);
    return store_tensor(std::get<0>(result));
}

int64_t rt_torch_torchtensor_eig(int64_t handle) {
    /* Return real part of eigenvalues */
    auto result = at::linalg_eig(get_tensor(handle));
    return store_tensor(torch::real(std::get<0>(result)));
}

/* ----------------------------------------------------------------------------
 * Reduction operations
 * -------------------------------------------------------------------------- */

double rt_torch_torchtensor_sum(int64_t handle) {
    return get_tensor(handle).sum().item<double>();
}

int64_t rt_torch_torchtensor_sum_dim(int64_t handle, int64_t dim, bool keepdim) {
    return store_tensor(get_tensor(handle).sum(dim, keepdim));
}

double rt_torch_torchtensor_mean(int64_t handle) {
    return get_tensor(handle).mean().item<double>();
}

int64_t rt_torch_torchtensor_mean_dim(int64_t handle, int64_t dim, bool keepdim) {
    return store_tensor(get_tensor(handle).mean(dim, keepdim));
}

double rt_torch_torchtensor_max(int64_t handle) {
    return get_tensor(handle).max().item<double>();
}

int64_t rt_torch_torchtensor_max_dim(int64_t handle, int64_t dim, bool keepdim) {
    auto result = get_tensor(handle).max(dim, keepdim);
    return store_tensor(std::get<0>(result));
}

double rt_torch_torchtensor_min(int64_t handle) {
    return get_tensor(handle).min().item<double>();
}

int64_t rt_torch_torchtensor_min_dim(int64_t handle, int64_t dim, bool keepdim) {
    auto result = get_tensor(handle).min(dim, keepdim);
    return store_tensor(std::get<0>(result));
}

int64_t rt_torch_torchtensor_argmax(int64_t handle, int64_t dim, bool keepdim) {
    if (dim < 0) {
        return store_tensor(get_tensor(handle).argmax());
    }
    return store_tensor(get_tensor(handle).argmax(dim, keepdim));
}

int64_t rt_torch_torchtensor_argmin(int64_t handle, int64_t dim, bool keepdim) {
    if (dim < 0) {
        return store_tensor(get_tensor(handle).argmin());
    }
    return store_tensor(get_tensor(handle).argmin(dim, keepdim));
}

double rt_torch_torchtensor_std(int64_t handle) {
    return get_tensor(handle).std().item<double>();
}

double rt_torch_torchtensor_var(int64_t handle) {
    return get_tensor(handle).var().item<double>();
}

/* ----------------------------------------------------------------------------
 * Shape manipulation
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_ndim(int64_t handle) {
    return (int64_t)get_tensor(handle).dim();
}

int64_t rt_torch_torchtensor_numel(int64_t handle) {
    return get_tensor(handle).numel();
}

SplArray* rt_torch_torchtensor_shape(int64_t handle) {
    return from_sizes(get_tensor(handle).sizes());
}

int64_t rt_torch_torchtensor_reshape(int64_t handle, SplArray* dims) {
    return store_tensor(get_tensor(handle).reshape(to_i64_vec(dims)));
}

int64_t rt_torch_torchtensor_view(int64_t handle, SplArray* dims) {
    return store_tensor(get_tensor(handle).contiguous().view(to_i64_vec(dims)));
}

int64_t rt_torch_torchtensor_permute(int64_t handle, SplArray* dims) {
    return store_tensor(get_tensor(handle).permute(to_i64_vec(dims)));
}

int64_t rt_torch_torchtensor_squeeze(int64_t handle) {
    return store_tensor(get_tensor(handle).squeeze());
}

int64_t rt_torch_torchtensor_squeeze_dim(int64_t handle, int64_t dim) {
    return store_tensor(get_tensor(handle).squeeze(dim));
}

int64_t rt_torch_torchtensor_unsqueeze(int64_t handle, int64_t dim) {
    return store_tensor(get_tensor(handle).unsqueeze(dim));
}

int64_t rt_torch_torchtensor_flatten(int64_t handle) {
    return store_tensor(get_tensor(handle).flatten());
}

int64_t rt_torch_torchtensor_contiguous(int64_t handle) {
    return store_tensor(get_tensor(handle).contiguous());
}

/* ----------------------------------------------------------------------------
 * Indexing and slicing
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_slice(int64_t handle, int64_t dim, int64_t start, int64_t end, int64_t step) {
    return store_tensor(get_tensor(handle).slice(dim, start, end, step));
}

int64_t rt_torch_torchtensor_index_select(int64_t handle, int64_t dim, int64_t indices) {
    return store_tensor(get_tensor(handle).index_select(dim, get_tensor(indices)));
}

int64_t rt_torch_torchtensor_gather(int64_t handle, int64_t dim, int64_t indices) {
    return store_tensor(torch::gather(get_tensor(handle), dim, get_tensor(indices)));
}

int64_t rt_torch_torchtensor_cat(SplArray* tensors, int64_t dim) {
    int64_t n = spl_array_len(tensors);
    std::vector<at::Tensor> ts;
    ts.reserve(n);
    for (int64_t i = 0; i < n; i++) {
        ts.push_back(get_tensor(spl_as_int(spl_array_get(tensors, i))));
    }
    return store_tensor(torch::cat(ts, dim));
}

int64_t rt_torch_torchtensor_stack(SplArray* tensors, int64_t dim) {
    int64_t n = spl_array_len(tensors);
    std::vector<at::Tensor> ts;
    ts.reserve(n);
    for (int64_t i = 0; i < n; i++) {
        ts.push_back(get_tensor(spl_as_int(spl_array_get(tensors, i))));
    }
    return store_tensor(torch::stack(ts, dim));
}

SplArray* rt_torch_torchtensor_chunk(int64_t handle, int64_t chunks, int64_t dim) {
    auto chunk_list = get_tensor(handle).chunk(chunks, dim);
    SplArray* arr = spl_array_new_i64();
    for (auto& t : chunk_list) {
        spl_array_push_i64(arr, store_tensor(t));
    }
    return arr;
}

/* ----------------------------------------------------------------------------
 * Neural network operations
 * -------------------------------------------------------------------------- */

int64_t rt_torch_nn_conv2d(int64_t input, int64_t weight, int64_t bias,
                           SplArray* stride, SplArray* padding,
                           SplArray* dilation, int64_t groups) {
    auto in = get_tensor(input);
    auto w  = get_tensor(weight);
    c10::optional<at::Tensor> bias_opt;
    if (bias != 0) {
        bias_opt = get_tensor(bias);
    }
    return store_tensor(at::conv2d(in, w, bias_opt,
        to_i64_vec(stride), to_i64_vec(padding), to_i64_vec(dilation), groups));
}

int64_t rt_torch_nn_max_pool2d(int64_t input, SplArray* kernel_size,
                               SplArray* stride, SplArray* padding) {
    return store_tensor(at::max_pool2d(get_tensor(input),
        to_i64_vec(kernel_size), to_i64_vec(stride), to_i64_vec(padding)));
}

int64_t rt_torch_nn_avg_pool2d(int64_t input, SplArray* kernel_size,
                               SplArray* stride, SplArray* padding) {
    return store_tensor(at::avg_pool2d(get_tensor(input),
        to_i64_vec(kernel_size), to_i64_vec(stride), to_i64_vec(padding)));
}

int64_t rt_torch_nn_batch_norm(int64_t input, int64_t running_mean,
                               int64_t running_var, int64_t weight,
                               int64_t bias, bool training,
                               double momentum, double eps) {
    auto in   = get_tensor(input);
    auto mean = get_tensor(running_mean);
    auto var  = get_tensor(running_var);
    auto w    = get_tensor(weight);
    auto b    = get_tensor(bias);
    return store_tensor(at::batch_norm(in, w, b, mean, var,
        training, momentum, eps, /*cudnn_enabled=*/true));
}

int64_t rt_torch_nn_layer_norm(int64_t input, SplArray* normalized_shape,
                               int64_t weight, int64_t bias, double eps) {
    auto in = get_tensor(input);
    auto w  = get_tensor(weight);
    auto b  = get_tensor(bias);
    return store_tensor(at::layer_norm(in, to_i64_vec(normalized_shape), w, b, eps));
}

int64_t rt_torch_nn_dropout(int64_t input, double p, bool training) {
    return store_tensor(at::dropout(get_tensor(input), p, training));
}

int64_t rt_torch_nn_linear(int64_t input, int64_t weight, int64_t bias) {
    auto in = get_tensor(input);
    auto w  = get_tensor(weight);
    auto b  = get_tensor(bias);
    return store_tensor(at::linear(in, w, b));
}

int64_t rt_torch_nn_embedding(int64_t input, int64_t weight) {
    return store_tensor(at::embedding(get_tensor(weight), get_tensor(input)));
}

/* ----------------------------------------------------------------------------
 * Loss functions
 * -------------------------------------------------------------------------- */

double rt_torch_nn_mse_loss(int64_t input, int64_t target) {
    return at::mse_loss(get_tensor(input), get_tensor(target)).item<double>();
}

double rt_torch_nn_cross_entropy(int64_t input, int64_t target) {
    return at::cross_entropy_loss(get_tensor(input), get_tensor(target)).item<double>();
}

double rt_torch_nn_binary_cross_entropy(int64_t input, int64_t target) {
    return at::binary_cross_entropy(get_tensor(input), get_tensor(target)).item<double>();
}

double rt_torch_nn_nll_loss(int64_t input, int64_t target) {
    return at::nll_loss(get_tensor(input), get_tensor(target)).item<double>();
}

/* ----------------------------------------------------------------------------
 * Autograd operations
 * -------------------------------------------------------------------------- */

void rt_torch_autograd_set_requires_grad(int64_t handle, bool requires_grad) {
    g_tensors[handle].requires_grad_(requires_grad);
}

bool rt_torch_autograd_requires_grad(int64_t handle) {
    return get_tensor(handle).requires_grad();
}

int64_t rt_torch_autograd_grad(int64_t handle) {
    auto t = get_tensor(handle);
    if (t.grad().defined()) {
        return store_tensor(t.grad());
    }
    return 0;
}

void rt_torch_autograd_backward(int64_t handle) {
    get_tensor(handle).backward();
}

void rt_torch_autograd_zero_grad(int64_t handle) {
    auto& t = g_tensors[handle];
    if (t.grad().defined()) {
        t.grad().zero_();
    }
}

int64_t rt_torch_autograd_detach(int64_t handle) {
    return store_tensor(get_tensor(handle).detach());
}

void rt_torch_autograd_no_grad_begin() {
    if (!g_no_grad_guard) {
        g_no_grad_guard = new torch::NoGradGuard();
    }
}

void rt_torch_autograd_no_grad_end() {
    delete g_no_grad_guard;
    g_no_grad_guard = nullptr;
}

/* ----------------------------------------------------------------------------
 * Device management
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_cuda(int64_t handle, int32_t device_id) {
    auto device = torch::Device(torch::kCUDA, device_id);
    return store_tensor(get_tensor(handle).to(device));
}

int64_t rt_torch_torchtensor_cpu(int64_t handle) {
    return store_tensor(get_tensor(handle).to(torch::kCPU));
}

bool rt_torch_torchtensor_is_cuda(int64_t handle) {
    return get_tensor(handle).is_cuda();
}

int32_t rt_torch_torchtensor_device(int64_t handle) {
    auto t = get_tensor(handle);
    if (t.is_cuda()) {
        return (int32_t)t.get_device();
    }
    return -1;
}

int64_t rt_torch_torchtensor_to_stream(int64_t handle, int32_t device_id, int64_t stream) {
    (void)stream; /* stream scheduling handled by PyTorch internally */
    auto device = torch::Device(torch::kCUDA, device_id);
    return store_tensor(get_tensor(handle).to(device));
}

int64_t rt_torch_torchtensor_clone(int64_t handle) {
    return store_tensor(get_tensor(handle).clone());
}

/* ----------------------------------------------------------------------------
 * CUDA streams
 * -------------------------------------------------------------------------- */

/* Helper: find stream by handle */
static at::cuda::CUDAStream* find_stream(int64_t handle) {
    for (auto& p : g_streams) {
        if (p.first == handle) return &p.second;
    }
    return nullptr;
}

int64_t rt_torch_stream_create(int32_t device_id) {
    auto stream = at::cuda::getStreamFromPool(false, device_id);
    int64_t h = g_next_handle.fetch_add(1);
    g_streams.emplace_back(h, stream);
    return h;
}

void rt_torch_torchstream_sync(int64_t handle) {
    auto* s = find_stream(handle);
    if (s) s->synchronize();
}

bool rt_torch_torchstream_query(int64_t handle) {
    auto* s = find_stream(handle);
    if (s) return s->query();
    return true;
}

void rt_torch_torchstream_free(int64_t handle) {
    g_streams.erase(
        std::remove_if(g_streams.begin(), g_streams.end(),
            [handle](const auto& p) { return p.first == handle; }),
        g_streams.end());
}

/* ----------------------------------------------------------------------------
 * Memory management
 * -------------------------------------------------------------------------- */

void rt_torch_torchtensor_free(int64_t handle) {
    g_tensors.erase(handle);
}

int64_t rt_torch_cuda_memory_allocated(int32_t device_id) {
    if (!torch::cuda::is_available()) return 0;
    auto stats = c10::cuda::CUDACachingAllocator::getDeviceStats(device_id);
    /* StatType::AGGREGATE = 0 */
    return (int64_t)stats.allocated_bytes[0].current;
}

int64_t rt_torch_cuda_max_memory_allocated(int32_t device_id) {
    if (!torch::cuda::is_available()) return 0;
    auto stats = c10::cuda::CUDACachingAllocator::getDeviceStats(device_id);
    return (int64_t)stats.allocated_bytes[0].peak;
}

void rt_torch_cuda_empty_cache() {
    if (torch::cuda::is_available()) {
        c10::cuda::CUDACachingAllocator::emptyCache();
    }
}

/* ===================================================================
 * Bit-cast wrappers for DynLoader (f64 <-> i64)
 *
 * DynLoader (spl_wffi_call_i64) can only pass/return int64_t.
 * These wrappers bit-cast f64 params/returns to int64_t so
 * DynLoader can invoke functions that use doubles.
 * =================================================================== */

static int64_t f64_to_bits(double f) {
    int64_t b; std::memcpy(&b, &f, 8); return b;
}
static double bits_to_f64(int64_t b) {
    double f; std::memcpy(&f, &b, 8); return f;
}

/* --- f64-returning reductions (1 arg) --- */

int64_t rt_torch_torchtensor_sum_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_sum(handle));
}
int64_t rt_torch_torchtensor_mean_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_mean(handle));
}
int64_t rt_torch_torchtensor_max_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_max(handle));
}
int64_t rt_torch_torchtensor_min_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_min(handle));
}
int64_t rt_torch_torchtensor_norm_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_norm(handle));
}
int64_t rt_torch_torchtensor_det_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_det(handle));
}
int64_t rt_torch_torchtensor_std_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_std(handle));
}
int64_t rt_torch_torchtensor_var_bits(int64_t handle) {
    return f64_to_bits(rt_torch_torchtensor_var(handle));
}

/* --- f64-returning losses (2 args) --- */

int64_t rt_torch_nn_mse_loss_bits(int64_t input, int64_t target) {
    return f64_to_bits(rt_torch_nn_mse_loss(input, target));
}
int64_t rt_torch_nn_cross_entropy_bits(int64_t input, int64_t target) {
    return f64_to_bits(rt_torch_nn_cross_entropy(input, target));
}
int64_t rt_torch_nn_binary_cross_entropy_bits(int64_t input, int64_t target) {
    return f64_to_bits(rt_torch_nn_binary_cross_entropy(input, target));
}
int64_t rt_torch_nn_nll_loss_bits(int64_t input, int64_t target) {
    return f64_to_bits(rt_torch_nn_nll_loss(input, target));
}

/* --- f64-input element-wise ops --- */

int64_t rt_torch_torchtensor_pow_bits(int64_t handle, int64_t exponent_bits) {
    return rt_torch_torchtensor_pow(handle, bits_to_f64(exponent_bits));
}
int64_t rt_torch_torchtensor_add_scalar_bits(int64_t handle, int64_t scalar_bits) {
    return rt_torch_torchtensor_add_scalar(handle, bits_to_f64(scalar_bits));
}
int64_t rt_torch_torchtensor_mul_scalar_bits(int64_t handle, int64_t scalar_bits) {
    return rt_torch_torchtensor_mul_scalar(handle, bits_to_f64(scalar_bits));
}

/* --- f64-input activations --- */

int64_t rt_torch_torchtensor_leaky_relu_bits(int64_t handle, int64_t slope_bits) {
    return rt_torch_torchtensor_leaky_relu(handle, bits_to_f64(slope_bits));
}

/* --- f64-input tensor creation --- */

int64_t rt_torch_tensor_arange_bits(int64_t start_bits, int64_t end_bits, int64_t step_bits) {
    return rt_torch_tensor_arange(bits_to_f64(start_bits), bits_to_f64(end_bits), bits_to_f64(step_bits));
}
int64_t rt_torch_tensor_linspace_bits(int64_t start_bits, int64_t end_bits, int64_t steps) {
    return rt_torch_tensor_linspace(bits_to_f64(start_bits), bits_to_f64(end_bits), steps);
}

/* --- f64-input NN ops --- */

int64_t rt_torch_nn_dropout_bits(int64_t input, int64_t p_bits, int64_t training) {
    return rt_torch_nn_dropout(input, bits_to_f64(p_bits), training != 0);
}

/* ===================================================================
 * Fixed-dimension wrappers for DynLoader (P2)
 *
 * DynLoader can't pass SplArray* args. These wrappers take
 * individual dimension values instead of arrays.
 * =================================================================== */

/* --- Tensor Creation: zeros --- */

int64_t rt_torch_tensor_zeros_1d(int64_t d0) {
    return store_tensor(torch::zeros({d0}));
}
int64_t rt_torch_tensor_zeros_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::zeros({d0, d1}));
}
int64_t rt_torch_tensor_zeros_3d(int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(torch::zeros({d0, d1, d2}));
}
int64_t rt_torch_tensor_zeros_4d(int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(torch::zeros({d0, d1, d2, d3}));
}

/* --- Tensor Creation: ones --- */

int64_t rt_torch_tensor_ones_1d(int64_t d0) {
    return store_tensor(torch::ones({d0}));
}
int64_t rt_torch_tensor_ones_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::ones({d0, d1}));
}
int64_t rt_torch_tensor_ones_3d(int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(torch::ones({d0, d1, d2}));
}
int64_t rt_torch_tensor_ones_4d(int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(torch::ones({d0, d1, d2, d3}));
}

/* --- Tensor Creation: randn --- */

int64_t rt_torch_tensor_randn_1d(int64_t d0) {
    return store_tensor(torch::randn({d0}));
}
int64_t rt_torch_tensor_randn_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::randn({d0, d1}));
}
int64_t rt_torch_tensor_randn_3d(int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(torch::randn({d0, d1, d2}));
}
int64_t rt_torch_tensor_randn_4d(int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(torch::randn({d0, d1, d2, d3}));
}

/* --- Tensor Creation: rand --- */

int64_t rt_torch_tensor_rand_1d(int64_t d0) {
    return store_tensor(torch::rand({d0}));
}
int64_t rt_torch_tensor_rand_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::rand({d0, d1}));
}
int64_t rt_torch_tensor_rand_3d(int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(torch::rand({d0, d1, d2}));
}
int64_t rt_torch_tensor_rand_4d(int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(torch::rand({d0, d1, d2, d3}));
}

/* --- Tensor Creation: empty --- */

int64_t rt_torch_tensor_empty_1d(int64_t d0) {
    return store_tensor(torch::empty({d0}));
}
int64_t rt_torch_tensor_empty_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::empty({d0, d1}));
}
int64_t rt_torch_tensor_empty_3d(int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(torch::empty({d0, d1, d2}));
}
int64_t rt_torch_tensor_empty_4d(int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(torch::empty({d0, d1, d2, d3}));
}

/* --- Tensor Creation: full (with f64 bit-cast for value) --- */

int64_t rt_torch_tensor_full_1d(int64_t d0, int64_t value_bits) {
    return store_tensor(torch::full({d0}, bits_to_f64(value_bits)));
}
int64_t rt_torch_tensor_full_2d(int64_t d0, int64_t d1, int64_t value_bits) {
    return store_tensor(torch::full({d0, d1}, bits_to_f64(value_bits)));
}
int64_t rt_torch_tensor_full_3d(int64_t d0, int64_t d1, int64_t d2, int64_t value_bits) {
    return store_tensor(torch::full({d0, d1, d2}, bits_to_f64(value_bits)));
}
int64_t rt_torch_tensor_full_4d(int64_t d0, int64_t d1, int64_t d2, int64_t d3, int64_t value_bits) {
    return store_tensor(torch::full({d0, d1, d2, d3}, bits_to_f64(value_bits)));
}

/* --- Shape: reshape --- */

int64_t rt_torch_torchtensor_reshape_1d(int64_t handle, int64_t d0) {
    return store_tensor(get_tensor(handle).reshape({d0}));
}
int64_t rt_torch_torchtensor_reshape_2d(int64_t handle, int64_t d0, int64_t d1) {
    return store_tensor(get_tensor(handle).reshape({d0, d1}));
}
int64_t rt_torch_torchtensor_reshape_3d(int64_t handle, int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(get_tensor(handle).reshape({d0, d1, d2}));
}
int64_t rt_torch_torchtensor_reshape_4d(int64_t handle, int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(get_tensor(handle).reshape({d0, d1, d2, d3}));
}

/* --- Shape: view --- */

int64_t rt_torch_torchtensor_view_1d(int64_t handle, int64_t d0) {
    return store_tensor(get_tensor(handle).contiguous().view({d0}));
}
int64_t rt_torch_torchtensor_view_2d(int64_t handle, int64_t d0, int64_t d1) {
    return store_tensor(get_tensor(handle).contiguous().view({d0, d1}));
}
int64_t rt_torch_torchtensor_view_3d(int64_t handle, int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(get_tensor(handle).contiguous().view({d0, d1, d2}));
}
int64_t rt_torch_torchtensor_view_4d(int64_t handle, int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(get_tensor(handle).contiguous().view({d0, d1, d2, d3}));
}

/* --- Shape: permute --- */

int64_t rt_torch_torchtensor_permute_2d(int64_t handle, int64_t d0, int64_t d1) {
    return store_tensor(get_tensor(handle).permute({d0, d1}));
}
int64_t rt_torch_torchtensor_permute_3d(int64_t handle, int64_t d0, int64_t d1, int64_t d2) {
    return store_tensor(get_tensor(handle).permute({d0, d1, d2}));
}
int64_t rt_torch_torchtensor_permute_4d(int64_t handle, int64_t d0, int64_t d1, int64_t d2, int64_t d3) {
    return store_tensor(get_tensor(handle).permute({d0, d1, d2, d3}));
}

/* --- Cat/Stack (fixed tensor count) --- */

int64_t rt_torch_torchtensor_cat_2(int64_t t0, int64_t t1, int64_t dim) {
    std::vector<at::Tensor> v = {get_tensor(t0), get_tensor(t1)};
    return store_tensor(torch::cat(v, dim));
}
int64_t rt_torch_torchtensor_cat_3(int64_t t0, int64_t t1, int64_t t2, int64_t dim) {
    std::vector<at::Tensor> v = {get_tensor(t0), get_tensor(t1), get_tensor(t2)};
    return store_tensor(torch::cat(v, dim));
}
int64_t rt_torch_torchtensor_cat_4(int64_t t0, int64_t t1, int64_t t2, int64_t t3, int64_t dim) {
    std::vector<at::Tensor> v = {get_tensor(t0), get_tensor(t1), get_tensor(t2), get_tensor(t3)};
    return store_tensor(torch::cat(v, dim));
}

int64_t rt_torch_torchtensor_stack_2(int64_t t0, int64_t t1, int64_t dim) {
    std::vector<at::Tensor> v = {get_tensor(t0), get_tensor(t1)};
    return store_tensor(torch::stack(v, dim));
}
int64_t rt_torch_torchtensor_stack_3(int64_t t0, int64_t t1, int64_t t2, int64_t dim) {
    std::vector<at::Tensor> v = {get_tensor(t0), get_tensor(t1), get_tensor(t2)};
    return store_tensor(torch::stack(v, dim));
}
int64_t rt_torch_torchtensor_stack_4(int64_t t0, int64_t t1, int64_t t2, int64_t t3, int64_t dim) {
    std::vector<at::Tensor> v = {get_tensor(t0), get_tensor(t1), get_tensor(t2), get_tensor(t3)};
    return store_tensor(torch::stack(v, dim));
}

/* --- Shape query: get single dimension size --- */

int64_t rt_torch_torchtensor_shape_dim(int64_t handle, int64_t dim_idx) {
    auto sizes = get_tensor(handle).sizes();
    if (dim_idx < 0 || dim_idx >= (int64_t)sizes.size()) return -1;
    return sizes[dim_idx];
}

/* --- NN: batch_norm (all i64 + f64 bit-cast) --- */

int64_t rt_torch_nn_batch_norm_bits(int64_t input, int64_t running_mean,
                                    int64_t running_var, int64_t weight,
                                    int64_t bias, int64_t training,
                                    int64_t momentum_bits, int64_t eps_bits) {
    return rt_torch_nn_batch_norm(input, running_mean, running_var, weight, bias,
                                 training != 0, bits_to_f64(momentum_bits),
                                 bits_to_f64(eps_bits));
}

/* --- NN: layer_norm (fixed 1d normalized shape + f64 bit-cast) --- */

int64_t rt_torch_nn_layer_norm_1d(int64_t input, int64_t norm_d0,
                                  int64_t weight, int64_t bias,
                                  int64_t eps_bits) {
    auto in = get_tensor(input);
    auto w  = get_tensor(weight);
    auto b  = get_tensor(bias);
    return store_tensor(at::layer_norm(in, {norm_d0}, w, b, bits_to_f64(eps_bits)));
}
int64_t rt_torch_nn_layer_norm_2d(int64_t input, int64_t norm_d0, int64_t norm_d1,
                                  int64_t weight, int64_t bias,
                                  int64_t eps_bits) {
    auto in = get_tensor(input);
    auto w  = get_tensor(weight);
    auto b  = get_tensor(bias);
    return store_tensor(at::layer_norm(in, {norm_d0, norm_d1}, w, b, bits_to_f64(eps_bits)));
}

/* --- NN: conv2d (fixed 2d stride/padding/dilation) --- */

int64_t rt_torch_nn_conv2d_simple(int64_t input, int64_t weight, int64_t bias,
                                  int64_t stride_h, int64_t stride_w,
                                  int64_t pad_h, int64_t pad_w,
                                  int64_t dil_h, int64_t dil_w,
                                  int64_t groups) {
    auto in = get_tensor(input);
    auto w  = get_tensor(weight);
    auto b  = (bias == 0) ? at::Tensor() : get_tensor(bias);
    return store_tensor(at::conv2d(in, w, b, {stride_h, stride_w},
                                   {pad_h, pad_w}, {dil_h, dil_w}, groups));
}

/* --- NN: max_pool2d / avg_pool2d (fixed 2d) --- */

int64_t rt_torch_nn_max_pool2d_simple(int64_t input,
                                      int64_t kh, int64_t kw,
                                      int64_t sh, int64_t sw,
                                      int64_t ph, int64_t pw) {
    return store_tensor(at::max_pool2d(get_tensor(input), {kh, kw}, {sh, sw}, {ph, pw}));
}

int64_t rt_torch_nn_avg_pool2d_simple(int64_t input,
                                      int64_t kh, int64_t kw,
                                      int64_t sh, int64_t sw,
                                      int64_t ph, int64_t pw) {
    return store_tensor(at::avg_pool2d(get_tensor(input), {kh, kw}, {sh, sw}, {ph, pw}));
}

/* ----------------------------------------------------------------------------
 * Trigonometric functions (Group 1)
 * -------------------------------------------------------------------------- */

int64_t rt_torch_torchtensor_sin(int64_t handle) {
    return store_tensor(torch::sin(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_cos(int64_t handle) {
    return store_tensor(torch::cos(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_tan(int64_t handle) {
    return store_tensor(torch::tan(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_asin(int64_t handle) {
    return store_tensor(torch::asin(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_acos(int64_t handle) {
    return store_tensor(torch::acos(get_tensor(handle)));
}

int64_t rt_torch_torchtensor_atan2(int64_t handle, int64_t other) {
    return store_tensor(torch::atan2(get_tensor(handle), get_tensor(other)));
}

/* ----------------------------------------------------------------------------
 * Integer tensor creation (Group 2)
 * -------------------------------------------------------------------------- */

int64_t rt_torch_tensor_arange_int(int64_t start, int64_t end, int64_t step) {
    return store_tensor(torch::arange(start, end, step, torch::kInt64));
}

int64_t rt_torch_tensor_zeros_int_1d(int64_t d0) {
    return store_tensor(torch::zeros({d0}, torch::kInt64));
}
int64_t rt_torch_tensor_zeros_int_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::zeros({d0, d1}, torch::kInt64));
}

int64_t rt_torch_tensor_ones_int_1d(int64_t d0) {
    return store_tensor(torch::ones({d0}, torch::kInt64));
}
int64_t rt_torch_tensor_ones_int_2d(int64_t d0, int64_t d1) {
    return store_tensor(torch::ones({d0, d1}, torch::kInt64));
}

int64_t rt_torch_tensor_full_int_1d(int64_t d0, int64_t value) {
    return store_tensor(torch::full({d0}, value, torch::kInt64));
}
int64_t rt_torch_tensor_full_int_2d(int64_t d0, int64_t d1, int64_t value) {
    return store_tensor(torch::full({d0, d1}, value, torch::kInt64));
}

int64_t rt_torch_tensor_from_i64_data(SplArray* data, SplArray* dims) {
    auto d = to_i64_vec(data);
    auto sh = to_i64_vec(dims);
    auto t = torch::from_blob(d.data(), sh, torch::kInt64).clone();
    return store_tensor(std::move(t));
}

int64_t rt_torch_torchtensor_to_float(int64_t handle) {
    return store_tensor(get_tensor(handle).to(torch::kFloat64));
}

int64_t rt_torch_torchtensor_to_int(int64_t handle) {
    return store_tensor(get_tensor(handle).to(torch::kInt64));
}

int64_t rt_torch_torchtensor_to_float32(int64_t handle) {
    return store_tensor(get_tensor(handle).to(torch::kFloat32));
}

/* ----------------------------------------------------------------------------
 * Tensor serialization (Group 3)
 * -------------------------------------------------------------------------- */

void rt_torch_tensor_save(int64_t handle, const char* path) {
    auto t = get_tensor(handle);
    std::vector<torch::Tensor> tensors = {t};
    torch::save(tensors, std::string(path));
}

int64_t rt_torch_tensor_load(const char* path) {
    std::vector<torch::Tensor> tensors;
    torch::load(tensors, std::string(path));
    if (tensors.empty()) {
        spl_eprintln("rt_torch: no tensors found in file");
        spl_panic("tensor load failed");
    }
    return store_tensor(tensors[0]);
}

/* DynLoader variants: path passed as i64 pointer to C string */
void rt_torch_tensor_save_dyn(int64_t handle, int64_t path_ptr) {
    const char* path = reinterpret_cast<const char*>(path_ptr);
    rt_torch_tensor_save(handle, path);
}

int64_t rt_torch_tensor_load_dyn(int64_t path_ptr) {
    const char* path = reinterpret_cast<const char*>(path_ptr);
    return rt_torch_tensor_load(path);
}

/* ----------------------------------------------------------------------------
 * Safetensors loading (Group 4)
 * -------------------------------------------------------------------------- */

} /* extern "C" — pause to define safetensors internals */

namespace {

struct SafetensorMeta {
    std::string name;
    std::string dtype;
    std::vector<int64_t> shape;
    int64_t data_offset_begin;
    int64_t data_offset_end;
};

struct SafetensorFile {
    std::string path;
    std::vector<SafetensorMeta> tensors;
    int64_t header_size;
    /* raw file data (header + tensor data) */
    std::vector<char> file_data;
};

static std::unordered_map<int64_t, SafetensorFile> g_safetensors;
static std::atomic<int64_t> g_next_sf_handle{1};

/* Minimal JSON parser for safetensors header.
 * Safetensors header format:
 *   { "tensor_name": {"dtype":"F32","shape":[3,4],"data_offsets":[0,48]}, ... }
 *   Plus optional "__metadata__" key (skipped).
 */

static void skip_ws(const char*& p, const char* end) {
    while (p < end && (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r')) p++;
}

static std::string parse_string(const char*& p, const char* end) {
    if (p >= end || *p != '"') return "";
    p++; /* skip opening quote */
    std::string s;
    while (p < end && *p != '"') {
        if (*p == '\\' && p + 1 < end) { p++; s += *p++; }
        else { s += *p++; }
    }
    if (p < end) p++; /* skip closing quote */
    return s;
}

static int64_t parse_int64(const char*& p, const char* end) {
    int64_t v = 0;
    bool neg = false;
    if (p < end && *p == '-') { neg = true; p++; }
    while (p < end && *p >= '0' && *p <= '9') {
        v = v * 10 + (*p - '0');
        p++;
    }
    return neg ? -v : v;
}

/* Skip a JSON value (string, number, array, object, true, false, null) */
static void skip_value(const char*& p, const char* end) {
    skip_ws(p, end);
    if (p >= end) return;
    if (*p == '"') { parse_string(p, end); return; }
    if (*p == '{') {
        p++; int depth = 1;
        while (p < end && depth > 0) {
            if (*p == '{') depth++;
            else if (*p == '}') depth--;
            else if (*p == '"') { parse_string(p, end); continue; }
            p++;
        }
        return;
    }
    if (*p == '[') {
        p++; int depth = 1;
        while (p < end && depth > 0) {
            if (*p == '[') depth++;
            else if (*p == ']') depth--;
            else if (*p == '"') { parse_string(p, end); continue; }
            p++;
        }
        return;
    }
    /* number, true, false, null */
    while (p < end && *p != ',' && *p != '}' && *p != ']' &&
           *p != ' ' && *p != '\t' && *p != '\n' && *p != '\r') p++;
}

static at::ScalarType safetensor_dtype_to_torch(const std::string& dtype) {
    if (dtype == "F64") return torch::kFloat64;
    if (dtype == "F32") return torch::kFloat32;
    if (dtype == "F16") return torch::kFloat16;
    if (dtype == "BF16") return torch::kBFloat16;
    if (dtype == "I64") return torch::kInt64;
    if (dtype == "I32") return torch::kInt32;
    if (dtype == "I16") return torch::kInt16;
    if (dtype == "I8") return torch::kInt8;
    if (dtype == "U8") return torch::kUInt8;
    if (dtype == "BOOL") return torch::kBool;
    spl_eprintln("rt_torch: unknown safetensor dtype");
    return torch::kFloat32; /* fallback */
}

static bool parse_safetensor_header(const char* json, int64_t json_len,
                                    std::vector<SafetensorMeta>& out) {
    const char* p = json;
    const char* end = json + json_len;
    skip_ws(p, end);
    if (p >= end || *p != '{') return false;
    p++; /* skip '{' */

    while (p < end) {
        skip_ws(p, end);
        if (*p == '}') break;
        if (*p == ',') { p++; continue; }

        std::string key = parse_string(p, end);
        skip_ws(p, end);
        if (p < end && *p == ':') p++; /* skip ':' */
        skip_ws(p, end);

        /* Skip __metadata__ */
        if (key == "__metadata__") {
            skip_value(p, end);
            continue;
        }

        /* Parse tensor entry: {"dtype":"...","shape":[...],"data_offsets":[start,end]} */
        if (p >= end || *p != '{') { skip_value(p, end); continue; }
        p++; /* skip '{' */

        SafetensorMeta meta;
        meta.name = key;
        meta.data_offset_begin = 0;
        meta.data_offset_end = 0;

        while (p < end && *p != '}') {
            skip_ws(p, end);
            if (*p == ',') { p++; continue; }
            std::string field = parse_string(p, end);
            skip_ws(p, end);
            if (p < end && *p == ':') p++;
            skip_ws(p, end);

            if (field == "dtype") {
                meta.dtype = parse_string(p, end);
            } else if (field == "shape") {
                if (p < end && *p == '[') {
                    p++; /* skip '[' */
                    while (p < end && *p != ']') {
                        skip_ws(p, end);
                        if (*p == ',') { p++; continue; }
                        if (*p == ']') break;
                        meta.shape.push_back(parse_int64(p, end));
                    }
                    if (p < end) p++; /* skip ']' */
                }
            } else if (field == "data_offsets") {
                if (p < end && *p == '[') {
                    p++;
                    skip_ws(p, end);
                    meta.data_offset_begin = parse_int64(p, end);
                    skip_ws(p, end);
                    if (p < end && *p == ',') p++;
                    skip_ws(p, end);
                    meta.data_offset_end = parse_int64(p, end);
                    skip_ws(p, end);
                    if (p < end && *p == ']') p++;
                }
            } else {
                skip_value(p, end);
            }
        }
        if (p < end && *p == '}') p++; /* skip closing '}' of tensor entry */

        out.push_back(std::move(meta));
    }
    return true;
}

} /* anonymous namespace */

extern "C" {

int64_t rt_torch_safetensors_open(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        spl_eprintln("rt_torch: cannot open safetensors file");
        return 0;
    }

    /* Read header size (first 8 bytes, little-endian uint64) */
    uint64_t header_size = 0;
    if (fread(&header_size, 8, 1, f) != 1) {
        fclose(f);
        spl_eprintln("rt_torch: cannot read safetensors header size");
        return 0;
    }

    /* Read entire file into memory */
    fseek(f, 0, SEEK_END);
    long file_size = ftell(f);
    fseek(f, 0, SEEK_SET);

    SafetensorFile sf;
    sf.path = path;
    sf.header_size = (int64_t)header_size;
    sf.file_data.resize(file_size);
    if ((long)fread(sf.file_data.data(), 1, file_size, f) != file_size) {
        fclose(f);
        spl_eprintln("rt_torch: cannot read safetensors file data");
        return 0;
    }
    fclose(f);

    /* Parse JSON header (starts at byte 8, length = header_size) */
    const char* json = sf.file_data.data() + 8;
    if (!parse_safetensor_header(json, (int64_t)header_size, sf.tensors)) {
        spl_eprintln("rt_torch: failed to parse safetensors header");
        return 0;
    }

    int64_t h = g_next_sf_handle.fetch_add(1);
    g_safetensors[h] = std::move(sf);
    return h;
}

void rt_torch_safetensors_close(int64_t handle) {
    g_safetensors.erase(handle);
}

int64_t rt_torch_safetensors_num_tensors(int64_t handle) {
    auto it = g_safetensors.find(handle);
    if (it == g_safetensors.end()) return 0;
    return (int64_t)it->second.tensors.size();
}

char* rt_torch_safetensors_list_names(int64_t handle) {
    auto it = g_safetensors.find(handle);
    if (it == g_safetensors.end()) return spl_str_new("");
    std::string result;
    for (size_t i = 0; i < it->second.tensors.size(); i++) {
        if (i > 0) result += '\n';
        result += it->second.tensors[i].name;
    }
    return spl_str_new(result.c_str());
}

int64_t rt_torch_safetensors_get_tensor(int64_t sf_handle, const char* name) {
    auto it = g_safetensors.find(sf_handle);
    if (it == g_safetensors.end()) {
        spl_eprintln("rt_torch: invalid safetensors handle");
        return 0;
    }
    SafetensorFile& sf = it->second;
    std::string target(name);

    for (auto& meta : sf.tensors) {
        if (meta.name != target) continue;

        /* Data starts after 8-byte size prefix + header */
        int64_t data_base = 8 + sf.header_size;
        const char* raw = sf.file_data.data() + data_base + meta.data_offset_begin;
        int64_t nbytes = meta.data_offset_end - meta.data_offset_begin;

        at::ScalarType dtype = safetensor_dtype_to_torch(meta.dtype);
        auto t = torch::from_blob(
            const_cast<char*>(raw), meta.shape,
            torch::TensorOptions().dtype(dtype)
        ).clone(); /* clone to own memory */

        return store_tensor(std::move(t));
    }

    spl_eprintln("rt_torch: tensor not found in safetensors file");
    return 0;
}

/* DynLoader variants: path/name passed as i64 pointer to C string */
int64_t rt_torch_safetensors_open_dyn(int64_t path_ptr) {
    return rt_torch_safetensors_open(reinterpret_cast<const char*>(path_ptr));
}

void rt_torch_safetensors_close_dyn(int64_t handle) {
    rt_torch_safetensors_close(handle);
}

int64_t rt_torch_safetensors_num_tensors_dyn(int64_t handle) {
    return rt_torch_safetensors_num_tensors(handle);
}

int64_t rt_torch_safetensors_list_names_dyn(int64_t handle) {
    /* Returns char* as i64 pointer — caller uses rt_cstring_to_text */
    return reinterpret_cast<int64_t>(rt_torch_safetensors_list_names(handle));
}

int64_t rt_torch_safetensors_get_tensor_dyn(int64_t sf_handle, int64_t name_ptr) {
    return rt_torch_safetensors_get_tensor(sf_handle, reinterpret_cast<const char*>(name_ptr));
}

} /* extern "C" */
