// cuda_utils.h - Common CUDA utilities and error checking macros
#pragma once

#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <sstream>

using namespace std;

//==================================================//
//              Error Checking Macros               //
//==================================================//

// Basic CUDA error checking macro
#ifndef CHECK_CUDA
#define CHECK_CUDA(call)                                                         \
    do {                                                                         \
        cudaError_t error = call;                                              \
        if (error != cudaSuccess) {                                            \
            fprintf(stderr, "CUDA Error at %s:%d - %s: %s\n",                 \
                    __FILE__, __LINE__, #call, cudaGetErrorString(error));    \
            exit(1);                                                            \
        }                                                                       \
    } while (0)
#endif

// Extended error checking with custom message
#ifndef CHECK_CUDA_MSG
#define CHECK_CUDA_MSG(call, msg)                                              \
    do {                                                                        \
        cudaError_t error = call;                                             \
        if (error != cudaSuccess) {                                           \
            fprintf(stderr, "CUDA Error at %s:%d - %s\n%s: %s\n",            \
                    __FILE__, __LINE__, msg, #call,                          \
                    cudaGetErrorString(error));                               \
            exit(1);                                                           \
        }                                                                      \
    } while (0)
#endif

// Check last CUDA error (useful after kernel launches)
#define CHECK_LAST_CUDA_ERROR()                                                \
    do {                                                                        \
        cudaError_t error = cudaGetLastError();                               \
        if (error != cudaSuccess) {                                           \
            fprintf(stderr, "Last CUDA Error at %s:%d: %s\n",                \
                    __FILE__, __LINE__, cudaGetErrorString(error));          \
            exit(1);                                                           \
        }                                                                      \
    } while (0)

// Check both launch and execution errors
#define CHECK_KERNEL_LAUNCH()                                                   \
    do {                                                                        \
        CHECK_LAST_CUDA_ERROR();                                              \
        CHECK_CUDA(cudaDeviceSynchronize());                                  \
    } while (0)

//==================================================//
//              Memory Utilities                    //
//==================================================//

// Safe memory allocation with error checking
template<typename T>
inline T* cuda_malloc(size_t count) {
    T* ptr = nullptr;
    size_t size = count * sizeof(T);
    CHECK_CUDA(cudaMalloc(&ptr, size));
    return ptr;
}

// Safe memory allocation and initialization
template<typename T>
inline T* cuda_calloc(size_t count) {
    T* ptr = cuda_malloc<T>(count);
    CHECK_CUDA(cudaMemset(ptr, 0, count * sizeof(T)));
    return ptr;
}

// Safe memory copy with error checking
template<typename T>
inline void cuda_memcpy(T* dst, const T* src, size_t count, cudaMemcpyKind kind) {
    CHECK_CUDA(cudaMemcpy(dst, src, count * sizeof(T), kind));
}

// Convenience functions for common copy directions
template<typename T>
inline void cuda_memcpy_h2d(T* d_dst, const T* h_src, size_t count) {
    cuda_memcpy(d_dst, h_src, count, cudaMemcpyHostToDevice);
}

template<typename T>
inline void cuda_memcpy_d2h(T* h_dst, const T* d_src, size_t count) {
    cuda_memcpy(h_dst, d_src, count, cudaMemcpyDeviceToHost);
}

template<typename T>
inline void cuda_memcpy_d2d(T* d_dst, const T* d_src, size_t count) {
    cuda_memcpy(d_dst, d_src, count, cudaMemcpyDeviceToDevice);
}

// Safe memory set with error checking
template<typename T>
inline void cuda_memset(T* ptr, int value, size_t count) {
    CHECK_CUDA(cudaMemset(ptr, value, count * sizeof(T)));
}

// Safe memory free
inline void cuda_free(void* ptr) {
    if (ptr) {
        CHECK_CUDA(cudaFree(ptr));
    }
}

//==================================================//
//              Device Query Utilities              //
//==================================================//

// Get device count with error checking
// Returns number of available CUDA devices, or 0 if CUDA unavailable
inline int get_device_count() {
    int count = 0;
    cudaError_t err = cudaGetDeviceCount(&count);
    if (err != cudaSuccess) {
        // CUDA not available or error - return 0
        return 0;
    }
    return count;
}

// Check if CUDA is available
inline bool is_cuda_available() {
    return get_device_count() > 0;
}

// Get device properties with error checking
// Returns true if successful, false if device invalid
inline bool get_device_props(cudaDeviceProp& props, int device = 0) {
    cudaError_t err = cudaGetDeviceProperties(&props, device);
    return (err == cudaSuccess);
}

// Get device properties with error checking (returns struct)
inline cudaDeviceProp get_device_props(int device = 0) {
    cudaDeviceProp props;
    CHECK_CUDA(cudaGetDeviceProperties(&props, device));
    return props;
}

// Set active device with error checking
inline bool set_device(int device) {
    cudaError_t err = cudaSetDevice(device);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to set device %d: %s\n",
                device, cudaGetErrorString(err));
        return false;
    }
    return true;
}

// Get current device
inline int get_current_device() {
    int device = -1;
    cudaError_t err = cudaGetDevice(&device);
    if (err != cudaSuccess) {
        return -1;
    }
    return device;
}

// Print device properties
inline void print_device_info(int device = 0) {
    cudaDeviceProp props;
    if (!get_device_props(props, device)) {
        printf("Device %d: Not available\n", device);
        return;
    }
    printf("Device %d: %s\n", device, props.name);
    printf("  Compute Capability: %d.%d\n", props.major, props.minor);
    printf("  Total Global Memory: %.2f GB\n", props.totalGlobalMem / (1024.0 * 1024 * 1024));
    printf("  SMs: %d\n", props.multiProcessorCount);
    printf("  Max Threads per Block: %d\n", props.maxThreadsPerBlock);
    printf("  Warp Size: %d\n", props.warpSize);
    printf("  Max Shared Memory per Block: %zu KB\n", props.sharedMemPerBlock / 1024);
    printf("  Max Registers per Block: %d\n", props.regsPerBlock);
}

// Check if device supports unified addressing (required for pinned memory)
inline bool supports_unified_addressing(int device = 0) {
    cudaDeviceProp props;
    if (!get_device_props(props, device)) {
        return false;
    }
    return props.unifiedAddressing != 0;
}

// Check if device supports P2P access with another device
inline bool can_access_peer(int device, int peer_device) {
    int can_access = 0;
    cudaError_t err = cudaDeviceCanAccessPeer(&can_access, device, peer_device);
    if (err != cudaSuccess) {
        return false;
    }
    return can_access != 0;
}

// Get optimal block size for a kernel
template<typename KernelFunc>
inline dim3 get_optimal_block_size(KernelFunc kernel, size_t dynamic_shmem = 0) {
    int min_grid_size, block_size;
    CHECK_CUDA(cudaOccupancyMaxPotentialBlockSize(
        &min_grid_size, &block_size, kernel, dynamic_shmem));
    return dim3(block_size);
}

//==================================================//
//              Timing Utilities                    //
//==================================================//

// CUDA event timer class
class CudaTimer {
private:
    cudaEvent_t start_event, stop_event;
    bool is_started;

public:
    CudaTimer() : is_started(false) {
        CHECK_CUDA(cudaEventCreate(&start_event));
        CHECK_CUDA(cudaEventCreate(&stop_event));
    }

    ~CudaTimer() {
        cudaEventDestroy(start_event);
        cudaEventDestroy(stop_event);
    }

    void start() {
        CHECK_CUDA(cudaEventRecord(start_event));
        is_started = true;
    }

    void stop() {
        if (!is_started) {
            fprintf(stderr, "Timer not started!\n");
            return;
        }
        CHECK_CUDA(cudaEventRecord(stop_event));
        CHECK_CUDA(cudaEventSynchronize(stop_event));
        is_started = false;
    }

    float elapsed_ms() {
        float milliseconds = 0;
        CHECK_CUDA(cudaEventElapsedTime(&milliseconds, start_event, stop_event));
        return milliseconds;
    }

    float elapsed_s() {
        return elapsed_ms() / 1000.0f;
    }
};

//==================================================//
//              Grid/Block Calculation              //
//==================================================//

// Calculate grid size for 1D kernel
inline int grid_size_1d(int total_threads, int block_size) {
    return (total_threads + block_size - 1) / block_size;
}

// Calculate grid size for 2D kernel
inline dim3 grid_size_2d(int width, int height, dim3 block) {
    return dim3(
        (width + block.x - 1) / block.x,
        (height + block.y - 1) / block.y
    );
}

// Calculate grid size for 3D kernel
inline dim3 grid_size_3d(int width, int height, int depth, dim3 block) {
    return dim3(
        (width + block.x - 1) / block.x,
        (height + block.y - 1) / block.y,
        (depth + block.z - 1) / block.z
    );
}

//==================================================//
//              Debug Utilities                     //
//==================================================//

// Configurable debug logging macro
// Set DEBUG_LOG_ENABLED=1 to enable debug output globally
// Or define it per-file before including this header
#ifndef DEBUG_LOG_ENABLED
#define DEBUG_LOG_ENABLED 0
#endif

#if DEBUG_LOG_ENABLED
#define DEBUG_LOG(fmt, ...) \
    fprintf(stderr, "[DEBUG] " fmt "\n", ##__VA_ARGS__)
#else
#define DEBUG_LOG(fmt, ...) ((void)0)
#endif

// Debug-mode runtime assertion macro
// Enabled in Debug builds (NDEBUG not defined) or when DEBUG_ASSERT_ENABLED=1
// Use for internal consistency checks that should be optimized out in release builds
#ifndef DEBUG_ASSERT_ENABLED
    #ifdef NDEBUG
        #define DEBUG_ASSERT_ENABLED 0
    #else
        #define DEBUG_ASSERT_ENABLED 1
    #endif
#endif

#if DEBUG_ASSERT_ENABLED
    #include <cassert>
    #define DEBUG_ASSERT(condition, msg) \
        do { \
            if (!(condition)) { \
                fprintf(stderr, "[ASSERT] %s:%d: %s\n", __FILE__, __LINE__, msg); \
                assert(condition); \
            } \
        } while (0)
#else
    #define DEBUG_ASSERT(condition, msg) ((void)0)
#endif

// Legacy print macro for debugging (only in debug builds)
#ifdef DEBUG
    #define CUDA_DEBUG_PRINT(fmt, ...) \
        printf("[DEBUG %s:%d] " fmt "\n", __FILE__, __LINE__, ##__VA_ARGS__)
#else
    #define CUDA_DEBUG_PRINT(fmt, ...)
#endif

// Device-side assert (requires -G flag)
#ifdef __CUDA_ARCH__
    #define CUDA_ASSERT(condition) \
        if (!(condition)) { \
            printf("Assertion failed at %s:%d\n", __FILE__, __LINE__); \
            assert(condition); \
        }
#else
    #define CUDA_ASSERT(condition) assert(condition)
#endif

//==================================================//
//           Performance Metrics                    //
//==================================================//

// Calculate bandwidth in GB/s
inline float calculate_bandwidth_gb(size_t bytes, float time_ms) {
    return (bytes / (1024.0 * 1024.0 * 1024.0)) / (time_ms / 1000.0);
}

// Calculate effective bandwidth utilization (simplified version)
// Note: For accurate peak bandwidth, check device specifications
inline float bandwidth_efficiency_percent(float achieved_gb) {
    // Typical modern GPU peak bandwidth is ~500-900 GB/s
    // This is a rough estimate - check your specific GPU specs
    const float typical_peak_gb = 600.0;
    return (achieved_gb / typical_peak_gb) * 100.0;
}

// Calculate GFLOPS
inline float calculate_gflops(size_t operations, float time_ms) {
    return (operations / 1e9) / (time_ms / 1000.0);
}

//==================================================//
//           Memory Pool Utilities                  //
//==================================================//

// Simple memory pool for frequent allocations
template<typename T>
class CudaMemoryPool {
private:
    T* pool;
    size_t capacity;
    size_t current_offset;

public:
    CudaMemoryPool(size_t total_elements)
        : capacity(total_elements), current_offset(0) {
        pool = cuda_malloc<T>(capacity);
    }

    ~CudaMemoryPool() {
        cuda_free(pool);
    }

    T* allocate(size_t count) {
        if (current_offset + count > capacity) {
            fprintf(stderr, "Memory pool exhausted!\n");
            return nullptr;
        }
        T* ptr = pool + current_offset;
        current_offset += count;
        return ptr;
    }

    void reset() {
        current_offset = 0;
    }

    size_t used() const {
        return current_offset;
    }

    size_t available() const {
        return capacity - current_offset;
    }
};
