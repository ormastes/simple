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

} /* extern "C" */
