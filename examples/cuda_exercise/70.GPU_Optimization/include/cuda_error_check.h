/**
 * @file cuda_error_check.h
 * @brief Common CUDA error checking macros for GPU Optimization modules
 *
 * Provides comprehensive error handling utilities following best practices
 * from NVIDIA documentation and high-quality reference implementations.
 */

#pragma once

#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>

/**
 * Check CUDA runtime API calls
 * Usage: CHECK_CUDA(cudaMalloc(&ptr, size));
 *
 * On error: Prints file, line, and error string, then exits
 */
#ifndef CHECK_CUDA
#define CHECK_CUDA(call) do { \
    cudaError_t error = (call); \
    if (error != cudaSuccess) { \
        fprintf(stderr, "CUDA error at %s:%d: %s\n", \
                __FILE__, __LINE__, cudaGetErrorString(error)); \
        exit(EXIT_FAILURE); \
    } \
} while(0)
#endif

/**
 * Check CUDA kernel launch
 * Usage: After kernel<<<>>>(); CHECK_KERNEL_LAUNCH();
 *
 * Checks both launch errors and synchronous execution errors
 */
#define CHECK_KERNEL_LAUNCH() do { \
    cudaError_t error = cudaGetLastError(); \
    if (error != cudaSuccess) { \
        fprintf(stderr, "CUDA kernel launch error at %s:%d: %s\n", \
                __FILE__, __LINE__, cudaGetErrorString(error)); \
        exit(EXIT_FAILURE); \
    } \
    error = cudaDeviceSynchronize(); \
    if (error != cudaSuccess) { \
        fprintf(stderr, "CUDA kernel execution error at %s:%d: %s\n", \
                __FILE__, __LINE__, cudaGetErrorString(error)); \
        exit(EXIT_FAILURE); \
    } \
} while(0)

/**
 * Check CUDA kernel launch (async version, no synchronize)
 * Usage: After kernel<<<>>>(); CHECK_KERNEL_LAUNCH_ASYNC();
 */
#define CHECK_KERNEL_LAUNCH_ASYNC() do { \
    cudaError_t error = cudaGetLastError(); \
    if (error != cudaSuccess) { \
        fprintf(stderr, "CUDA kernel launch error at %s:%d: %s\n", \
                __FILE__, __LINE__, cudaGetErrorString(error)); \
        exit(EXIT_FAILURE); \
    } \
} while(0)

/**
 * Non-fatal CUDA error check (returns error code instead of exiting)
 * Usage: if (CHECK_CUDA_NONFATAL(cudaMalloc(&ptr, size)) != cudaSuccess) { ... }
 */
#define CHECK_CUDA_NONFATAL(call) \
    [&]() -> cudaError_t { \
        cudaError_t error = (call); \
        if (error != cudaSuccess) { \
            fprintf(stderr, "CUDA warning at %s:%d: %s\n", \
                    __FILE__, __LINE__, cudaGetErrorString(error)); \
        } \
        return error; \
    }()

/**
 * CUDA error check with custom error message
 * Usage: CHECK_CUDA_MSG(cudaMalloc(&ptr, size), "Failed to allocate memory");
 */
#define CHECK_CUDA_MSG(call, msg) do { \
    cudaError_t error = (call); \
    if (error != cudaSuccess) { \
        fprintf(stderr, "CUDA error at %s:%d: %s\n  %s\n", \
                __FILE__, __LINE__, cudaGetErrorString(error), msg); \
        exit(EXIT_FAILURE); \
    } \
} while(0)

#ifdef __cplusplus
/**
 * RAII wrapper for CUDA device memory
 * Automatically frees memory when going out of scope
 */
template<typename T>
class CudaMemory {
private:
    T* ptr_;
    size_t size_;

public:
    CudaMemory() : ptr_(nullptr), size_(0) {}

    explicit CudaMemory(size_t count) : ptr_(nullptr), size_(count * sizeof(T)) {
        CHECK_CUDA(cudaMalloc(&ptr_, size_));
    }

    ~CudaMemory() {
        if (ptr_) {
            cudaFree(ptr_);
        }
    }

    // Disable copy
    CudaMemory(const CudaMemory&) = delete;
    CudaMemory& operator=(const CudaMemory&) = delete;

    // Enable move
    CudaMemory(CudaMemory&& other) noexcept : ptr_(other.ptr_), size_(other.size_) {
        other.ptr_ = nullptr;
        other.size_ = 0;
    }

    CudaMemory& operator=(CudaMemory&& other) noexcept {
        if (this != &other) {
            if (ptr_) cudaFree(ptr_);
            ptr_ = other.ptr_;
            size_ = other.size_;
            other.ptr_ = nullptr;
            other.size_ = 0;
        }
        return *this;
    }

    T* get() { return ptr_; }
    const T* get() const { return ptr_; }
    size_t size() const { return size_; }
    size_t count() const { return size_ / sizeof(T); }

    void copyToDevice(const T* host_data, size_t count) {
        CHECK_CUDA(cudaMemcpy(ptr_, host_data, count * sizeof(T), cudaMemcpyHostToDevice));
    }

    void copyToHost(T* host_data, size_t count) const {
        CHECK_CUDA(cudaMemcpy(host_data, ptr_, count * sizeof(T), cudaMemcpyDeviceToHost));
    }
};

/**
 * RAII wrapper for CUDA pinned host memory
 */
template<typename T>
class CudaPinnedMemory {
private:
    T* ptr_;
    size_t size_;

public:
    CudaPinnedMemory() : ptr_(nullptr), size_(0) {}

    explicit CudaPinnedMemory(size_t count) : ptr_(nullptr), size_(count * sizeof(T)) {
        CHECK_CUDA(cudaMallocHost(&ptr_, size_));
    }

    ~CudaPinnedMemory() {
        if (ptr_) {
            cudaFreeHost(ptr_);
        }
    }

    // Disable copy
    CudaPinnedMemory(const CudaPinnedMemory&) = delete;
    CudaPinnedMemory& operator=(const CudaPinnedMemory&) = delete;

    // Enable move
    CudaPinnedMemory(CudaPinnedMemory&& other) noexcept : ptr_(other.ptr_), size_(other.size_) {
        other.ptr_ = nullptr;
        other.size_ = 0;
    }

    CudaPinnedMemory& operator=(CudaPinnedMemory&& other) noexcept {
        if (this != &other) {
            if (ptr_) cudaFreeHost(ptr_);
            ptr_ = other.ptr_;
            size_ = other.size_;
            other.ptr_ = nullptr;
            other.size_ = 0;
        }
        return *this;
    }

    T* get() { return ptr_; }
    const T* get() const { return ptr_; }
    size_t size() const { return size_; }
    size_t count() const { return size_ / sizeof(T); }
};
#endif // __cplusplus
