# 🛡️ Part 16: Error Handling and Debugging

**Goal**: Build robust CUDA applications with comprehensive error handling strategies and debugging techniques.

## Project Structure

```
16.Error_Handling_and_Debugging/
├── CMakeLists.txt                   # Root CMake configuration
├── README.md                        # This documentation
├── src/                             # Source code directory
│   ├── CMakeLists.txt              # Library build configuration
│   └── kernels/                    # Core CUDA kernels (reusable across parts)
│       ├── vector_add_2d.cu        # Core implementation with error examples
│       └── vector_add_2d.h         # Header with kernel declarations
└── test/                            # Test directory
    ├── CMakeLists.txt              # Test build configuration
    └── unit/                        # Unit tests
        ├── kernels/                # Kernel tests (reusable across parts)
        │   └── test_vector_add_2d.cu  # Unit tests for vector operations
        └── part_specific/          # Module-specific tests
            └── test_error_handling.cu # Comprehensive error handling demos
```

**Note:** All code examples shown in this README are implemented and tested in `test/unit/part_specific/test_error_handling.cu`

## CMake Structure Overview

This project follows a modular CMake structure for better organization and maintainability:

### **Root CMakeLists.txt**
```cmake
project(16_Error_Handling_And_Debugging)
set(MODULE ${PROJECT_NAME})
add_subdirectory(src)   # Build source library
add_subdirectory(test)  # Build test executables
```

### **src/CMakeLists.txt - Library Configuration**
The source directory creates two libraries:
1. **Interface Library** (`${MODULE}_lib_INTERFACE`): Header-only interface for includes
2. **Static Library** (`${MODULE}_lib`): Compiled CUDA kernels

```cmake
# Interface library for headers
add_library(${MODULE}_lib_INTERFACE INTERFACE)
target_include_directories(${MODULE}_lib_INTERFACE
    INTERFACE ${CMAKE_CURRENT_LIST_DIR}
)

# Static library with CUDA kernels
add_library(${MODULE}_lib STATIC
    kernels/vector_add_2d.cu
)
target_link_libraries(${MODULE}_lib
    PUBLIC ${MODULE}_lib_INTERFACE
)
```

### **test/CMakeLists.txt - Test Configuration**
The test directory builds two test executables with different purposes:

```cmake
# Main error handling test suite
add_executable(${MODULE}_test
    test_error_handling.cu
)
target_link_libraries(${MODULE}_test PRIVATE
    GTest::gtest_main      # Google Test framework
    GTestCudaGenerator     # GPU testing utilities
    CudaCustomLib          # cuda_utils.h utilities
    ${MODULE}_lib_INTERFACE
)

# Long-term/stress testing
add_executable(${MODULE}_long_term_test
    test_vector_add_2d.cu
)

# Register with CTest and add profiling
gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
```

### **Key CMake Features**

1. **Modular Design**: Separates source and test code for clarity
2. **Interface Libraries**: Clean header-only dependencies
3. **Debug Support**: Conditional compilation with `-G` flag for device debugging
4. **Profiling Integration**: Automatic sanitizer targets (memcheck, racecheck)
5. **Test Discovery**: Automatic GTest integration with CTest

### **Benefits of This Structure**

The modular CMake structure provides several advantages:

- **Separation of Concerns**: Source code and tests are clearly separated
- **Reusability**: Libraries can be linked by other projects
- **Scalability**: Easy to add new source files or test cases
- **Build Control**: Can build/test individual components
- **Professional Organization**: Follows industry best practices for C++/CUDA projects

This structure mirrors real-world CUDA projects where:
- `src/` contains production code
- `test/` contains comprehensive testing
- CMake manages dependencies and build configurations
- Interface libraries provide clean API boundaries

## Quick Navigation
- [16.1 CUDA Error Types and Codes](#161-cuda-error-types-and-codes)
- [16.2 Error Checking Macros](#162-error-checking-macros-from-cuda_utilsh)
- [16.3 Synchronous vs Asynchronous Errors](#163-synchronous-vs-asynchronous-errors)
- [16.4 Debugging Memory Errors](#164-debugging-memory-errors)
- [16.5 Race Condition Detection](#165-race-condition-detection)
- [16.6 Deadlock Prevention](#166-deadlock-prevention)
- [16.7 Error Recovery Strategies](#167-error-recovery-strategies)
- [16.8 Logging and Diagnostics](#168-logging-and-diagnostics)
- [16.9 Production Error Handling](#169-production-error-handling)
- [16.10 Troubleshooting Common Issues](#1610-troubleshooting-common-issues)
- [16.11 Tool Usage Guide](#1611-tool-usage-guide)
- [16.12 CUDA Error Glossary](#1612-cuda-error-glossary)
- [16.13 Running the Examples](#1613-running-the-examples)
- [16.14 Summary](#1614-summary)

---

## **16.1 CUDA Error Types and Codes**

### **16.1.1 Error Categories**

CUDA errors fall into several categories:

1. **Synchronous Errors**: Returned immediately by CUDA API calls
2. **Asynchronous Errors**: Occur during kernel execution or async operations
3. **Sticky Errors**: Persist until explicitly cleared
4. **Driver Errors**: Related to CUDA driver issues

### **16.1.2 Common Error Codes**

```cpp
// Common CUDA error codes
cudaSuccess                    // No errors (0)
cudaErrorInvalidValue          // Invalid argument
cudaErrorMemoryAllocation      // Out of memory
cudaErrorInvalidDevice         // Invalid device ordinal
cudaErrorInvalidConfiguration  // Invalid kernel configuration
cudaErrorLaunchFailure        // Kernel launch failed
cudaErrorIllegalAddress       // Out-of-bounds memory access
cudaErrorMisalignedAddress    // Misaligned memory access
cudaErrorInvalidPitchValue    // Invalid pitch for cudaMemcpy2D
cudaErrorNotReady            // Async operation not complete
```

### **16.1.3 Getting Error Strings**

```cpp
cudaError_t error = cudaMalloc(&d_ptr, size);
if (error != cudaSuccess) {
    // Get human-readable error string
    const char* errorString = cudaGetErrorString(error);
    fprintf(stderr, "CUDA Error: %s\n", errorString);

    // Get detailed error description
    const char* errorName = cudaGetErrorName(error);
    fprintf(stderr, "Error Code: %s\n", errorName);
}
```

---

## **16.2 Error Checking Macros (from cuda_utils.h)**

The project uses comprehensive error checking macros from our custom CUDA utilities library (`00.cuda_custom_lib/cuda_utils.h`):

### **16.2.1 Available Error Checking Macros**

These macros catch CUDA errors immediately when they occur, preventing silent failures that could lead to incorrect results or crashes later in execution.

```cpp
// Basic CUDA error checking
#define CHECK_CUDA(call)  // Checks CUDA API calls and exits on error

// Extended error checking with custom message
#define CHECK_CUDA_MSG(call, msg)  // Adds custom message to error output

// Check last CUDA error (useful after kernel launches)
#define CHECK_LAST_CUDA_ERROR()  // Gets and checks cudaGetLastError()

// Check both launch and execution errors
#define CHECK_KERNEL_LAUNCH()  // Combines CHECK_LAST_CUDA_ERROR() and sync
```

**Key point:** Kernel launches are asynchronous and don't return errors directly. Always use `CHECK_KERNEL_LAUNCH()` after `kernel<<<grid,block>>>()` to catch both configuration and runtime errors.

```cpp
// Usage examples from our tests
CHECK_CUDA(cudaGetDeviceCount(&deviceCount));
CHECK_CUDA(cudaMemset(d_output, 0, sizeof(float)));
CHECK_KERNEL_LAUNCH();  // After kernel launch
```

### **16.2.2 Advanced Error Handling with C++ Exceptions**

While the basic macros terminate the program on errors, C++ exception handling provides more flexible error recovery options. This approach allows higher-level code to catch and handle CUDA errors gracefully without terminating the entire application.

```cpp
#include <stdexcept>
#include <sstream>

class CudaException : public std::runtime_error {
public:
    CudaException(cudaError_t error, const char* file, int line)
        : std::runtime_error(buildErrorMessage(error, file, line)),
          error_(error) {}

    cudaError_t getError() const { return error_; }

private:
    cudaError_t error_;

    static std::string buildErrorMessage(cudaError_t error,
                                        const char* file, int line) {
        std::ostringstream oss;
        oss << "CUDA Error at " << file << ":" << line
            << " - " << cudaGetErrorString(error);
        return oss.str();
    }
};

#define CHECK_CUDA_THROW(call) do { \
    cudaError_t error = call; \
    if (error != cudaSuccess) { \
        throw CudaException(error, __FILE__, __LINE__); \
    } \
} while(0)
```

### **16.2.3 Memory Management Utilities**

The `cuda_utils.h` library provides safe memory management functions that **automatically include CHECK_CUDA error checking**:

```cpp
// Safe memory allocation with built-in error checking
template<typename T>
T* cuda_malloc(size_t count);  // Internally calls CHECK_CUDA(cudaMalloc(...))

template<typename T>
T* cuda_calloc(size_t count);  // Allocates and zeros memory using:
                               // CHECK_CUDA(cudaMalloc(...))
                               // CHECK_CUDA(cudaMemset(...))

// Safe memory copy with built-in error checking
template<typename T>
void cuda_memcpy(T* dst, const T* src, size_t count, cudaMemcpyKind kind);
// Internally calls CHECK_CUDA(cudaMemcpy(...))

// Safe memory set with built-in error checking
template<typename T>
void cuda_memset(T* ptr, int value, size_t count);
// Internally calls CHECK_CUDA(cudaMemset(...))

// Safe memory free with nullptr checking
void cuda_free(void* ptr);  // Checks for nullptr, then calls CHECK_CUDA(cudaFree(...))

// Usage in tests - NO need for additional CHECK_CUDA!
float* d_a = cuda_malloc<float>(size);        // Error checking included
float* d_b = cuda_calloc<float>(size);        // Error checking included (zeros memory)
cuda_memcpy(d_a, h_a.data(), size, cudaMemcpyHostToDevice);  // Error checking included
cuda_memset(d_output, 0, 1);                  // Error checking included (NEW!)
cuda_free(d_a);                               // Error checking included
```

**Key Point:** All these utility functions include automatic error checking, so you don't need to wrap them with CHECK_CUDA.

**Example Usage:**
```cpp
// Traditional CUDA (verbose, error-prone)
float* d_data;
cudaError_t err = cudaMalloc(&d_data, n * sizeof(float));
if (err != cudaSuccess) { /* handle error */ }
err = cudaMemset(d_data, 0, n * sizeof(float));
if (err != cudaSuccess) { /* handle error */ }

// With our library (clean, safe)
float* d_data = cuda_calloc<float>(n);  // Allocates AND zeros in one call
// Automatic error checking included - exits on failure
```

### **16.2.4 Grid/Block Size Calculation Helpers**

These helpers prevent common off-by-one errors in grid size calculations using the ceiling division formula.

```cpp
// Calculate optimal grid sizes
int grid_size_1d(int total_threads, int block_size);
dim3 grid_size_2d(int width, int height, dim3 block);
dim3 grid_size_3d(int width, int height, int depth, dim3 block);

// Usage in tests
dim3 blockSize(16, 16);
dim3 gridSize = grid_size_2d(width, height, blockSize);
kernel<<<gridSize, blockSize>>>(args...);
```

**Example: Avoiding Common Mistakes**
```cpp
// Error-prone manual calculation
int gridSize = width * height / (blockSize.x * blockSize.y);  // Wrong! Drops remainder

// Correct but verbose
int gridX = (width + blockSize.x - 1) / blockSize.x;
int gridY = (height + blockSize.y - 1) / blockSize.y;

// Clean with our helper
dim3 gridSize = grid_size_2d(width, height, blockSize);  // Always correct
```

### **16.2.5 Debug-Only Checks**

These macros enable comprehensive error checking in debug builds while maintaining performance in release builds. They help catch issues during development without impacting production performance.

```cpp
#ifdef DEBUG
    #define CHECK_CUDA_DEBUG(call) CHECK_CUDA(call)
    #define CHECK_LAST_CUDA_ERROR() CHECK_CUDA(cudaGetLastError())
#else
    #define CHECK_CUDA_DEBUG(call) (call)
    #define CHECK_LAST_CUDA_ERROR()
#endif
```

**Usage Example:**
```cpp
// Extra validation only in debug mode
CHECK_CUDA_DEBUG(cudaMemset(d_debug_buffer, 0, debug_size));

// Performance-critical section
for (int i = 0; i < iterations; i++) {
    kernel<<<grid, block>>>(d_data);
    CHECK_CUDA_DEBUG(cudaGetLastError());  // Only checks in debug builds
}

// Always check critical operations
CHECK_CUDA(cudaMemcpy(h_results, d_data, size, cudaMemcpyDeviceToHost));
```

### **16.2.6 Additional Utilities from cuda_utils.h**

The library provides essential tools for performance measurement and debugging. The CudaTimer class offers precise GPU timing using CUDA events, while performance metrics help you evaluate whether your kernels are achieving good memory bandwidth and compute throughput:

```cpp
// CUDA Event Timer Class
class CudaTimer {
public:
    void start();
    void stop();
    float elapsed_ms();  // Get elapsed time in milliseconds
    float elapsed_s();   // Get elapsed time in seconds
};

// Device Query Utilities
cudaDeviceProp get_device_props(int device = 0);
void print_device_info(int device = 0);

// Performance Metrics
float calculate_bandwidth_gb(size_t bytes, float time_ms);
float calculate_gflops(size_t operations, float time_ms);

// Debug Utilities (requires -G flag for device-side)
#define CUDA_DEBUG_PRINT(fmt, ...)  // Printf for debug builds
#define CUDA_ASSERT(condition)      // Device-side assert

// Example usage
CudaTimer timer;
timer.start();
kernel<<<grid, block>>>(args...);
timer.stop();
float bandwidth = calculate_bandwidth_gb(bytes_transferred, timer.elapsed_ms());
```

**Practical Example: Performance Analysis**
```cpp
// Measure and evaluate kernel performance
CudaTimer timer;
size_t data_size = n * sizeof(float);

timer.start();
vectorAdd<<<gridSize, blockSize>>>(d_a, d_b, d_c, n);
timer.stop();

// Calculate metrics
float time_ms = timer.elapsed_ms();
float bandwidth = calculate_bandwidth_gb(3 * data_size, time_ms);  // 3 arrays accessed
float gflops = calculate_gflops(n, time_ms);  // n additions

printf("Kernel time: %.3f ms\n", time_ms);
printf("Bandwidth: %.2f GB/s\n", bandwidth);
printf("Performance: %.2f GFLOPS\n", gflops);

// Query device capabilities
print_device_info();  // Shows GPU specs for comparison
```

---

## **16.3 Synchronous vs Asynchronous Errors**

Understanding the difference between synchronous and asynchronous errors is crucial for proper CUDA error handling. Synchronous errors occur immediately, while asynchronous errors may not manifest until later, making them harder to debug.

### **16.3.1 Synchronous Error Handling**

These errors are returned immediately by CUDA API calls, making them straightforward to handle. Memory allocation, device queries, and most CUDA runtime functions fall into this category.

```cpp
// Synchronous errors are returned immediately
cudaError_t err = cudaMalloc(&d_ptr, size);
if (err != cudaSuccess) {
    // Handle error immediately
    handleError(err);
}
```

### **16.3.2 Asynchronous Error Handling**

Kernel launches and async memory operations return immediately without error codes. Errors only appear when you query for them or synchronize, requiring explicit checking after launches.

```cpp
// Kernel launch (asynchronous)
myKernel<<<blocks, threads>>>(d_data, size);

// Check for launch errors (synchronous check)
CHECK_CUDA(cudaGetLastError());

// Wait for kernel completion and check for runtime errors
CHECK_CUDA(cudaDeviceSynchronize());

// Alternative: Check without synchronizing
cudaError_t err = cudaPeekAtLastError();
if (err != cudaSuccess) {
    fprintf(stderr, "Kernel error: %s\n", cudaGetErrorString(err));
}
```

### **16.3.3 Stream-Based Error Handling**

Streams enable concurrent operations but complicate error handling. Each stream maintains its own error state that must be checked independently.

```cpp
cudaStream_t stream;
CHECK_CUDA(cudaStreamCreate(&stream));

// Launch kernel on stream
myKernel<<<blocks, threads, 0, stream>>>(d_data, size);

// Query stream status without blocking
cudaError_t err = cudaStreamQuery(stream);
if (err == cudaErrorNotReady) {
    // Stream operations still in progress
} else if (err != cudaSuccess) {
    // Handle error
}

// Synchronize and check for errors
CHECK_CUDA(cudaStreamSynchronize(stream));
```

---

## **16.4 Debugging Memory Errors**

Memory errors are the most common and difficult CUDA bugs to debug. They can cause silent data corruption, random crashes, or incorrect results that only appear under specific conditions.

### **16.4.1 Common Memory Errors**

These are the most frequent memory-related bugs in CUDA programs. Each can lead to undefined behavior that may not immediately crash your program.

1. **Out-of-bounds access**
2. **Use after free**
3. **Double free**
4. **Memory leaks**
5. **Uninitialized memory access**

### **16.4.2 Memory Error Detection Strategies**

Use CUDA-memcheck tools and runtime limits to catch memory errors early. These strategies help identify issues before they cause data corruption.

```cpp
// Enable memory checking in debug builds
void enableMemoryChecking() {
#ifdef DEBUG
    // Enable CUDA memory checking
    cudaDeviceSetLimit(cudaLimitMallocHeapSize, 128*1024*1024);

    // Enable device-side assertions
    cudaDeviceSetLimit(cudaLimitDevRuntimeSyncDepth, 2);
#endif
}

// Safe memory allocation with tracking
template<typename T>
class CudaMemory {
private:
    T* ptr_ = nullptr;
    size_t size_ = 0;

public:
    CudaMemory(size_t count) : size_(count * sizeof(T)) {
        CHECK_CUDA(cudaMalloc(&ptr_, size_));
    }

    ~CudaMemory() {
        if (ptr_) {
            cudaFree(ptr_);  // Ignore errors in destructor
        }
    }

    // Prevent copying
    CudaMemory(const CudaMemory&) = delete;
    CudaMemory& operator=(const CudaMemory&) = delete;

    // Allow moving
    CudaMemory(CudaMemory&& other) noexcept
        : ptr_(other.ptr_), size_(other.size_) {
        other.ptr_ = nullptr;
        other.size_ = 0;
    }

    T* get() { return ptr_; }
    size_t size() const { return size_; }
};
```

### **16.4.3 Bounds Checking in Kernels**

Add explicit bounds checking in debug builds to catch out-of-bounds accesses immediately rather than experiencing random crashes.

```cpp
__device__ void assertInBounds(int index, int size,
                              const char* file, int line) {
#ifdef DEBUG
    if (index < 0 || index >= size) {
        printf("CUDA Assert: Index %d out of bounds [0, %d) at %s:%d\n",
               index, size, file, line);
        __trap();  // Trigger a trap
    }
#endif
}

#define CUDA_ASSERT_BOUNDS(idx, size) \
    assertInBounds(idx, size, __FILE__, __LINE__)

__global__ void safeKernel(float* data, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Bounds checking in debug mode
    CUDA_ASSERT_BOUNDS(idx, size);

    if (idx < size) {
        data[idx] = idx * 2.0f;
    }
}
```

---

## **16.5 Race Condition Detection**

Race conditions occur when multiple threads access shared data without proper synchronization. They cause non-deterministic behavior that may work sometimes but fail unpredictably in production.

### **16.5.1 Common Race Conditions**

Understanding typical race condition patterns helps prevent them in your code. Missing `__syncthreads()` calls are the most common cause.

```cpp
// Example of race condition in shared memory
// See test_error_handling.cu for working implementation
__global__ void raceyKernel(float* result) {
    __shared__ float sdata[256];

    int tid = threadIdx.x;
    sdata[tid] = tid;

    // RACE CONDITION: Missing synchronization
    // __syncthreads();  // <-- This is needed!

    if (tid < 128) {
        sdata[tid] += sdata[tid + 128];  // Race condition!
    }

    if (tid == 0) {
        *result = sdata[0];
    }
}
```

### **16.5.2 Detecting Race Conditions**

Tools like cuda-memcheck's racecheck can detect some races, but adding your own detection logic helps catch application-specific issues.

```cpp
// Use atomic operations to detect races
__device__ int raceDetector = 0;

__global__ void detectRace(int* data, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < size) {
        // Increment before access
        int accessCount = atomicAdd(&raceDetector, 1);

        // Simulated work
        data[idx] = idx;

        // Decrement after access
        atomicSub(&raceDetector, 1);

        // Check for concurrent access
        if (raceDetector > 1) {
            printf("Race detected at index %d\n", idx);
        }
    }
}
```

---

## **16.6 Deadlock Prevention**

Deadlocks freeze kernel execution when threads wait indefinitely for each other. The most dangerous aspect is that deadlocks in conditional synchronization may only occur with specific input data.

### **16.6.1 Common Deadlock Scenarios**

Conditional `__syncthreads()` is the primary cause of deadlocks. All threads in a block must reach the same synchronization point or the kernel will hang.

```cpp
// Deadlock example: Conditional synchronization
__global__ void deadlockKernel() {
    int tid = threadIdx.x;

    // DEADLOCK: Not all threads reach sync point
    if (tid < 16) {
        __syncthreads();  // Only threads 0-15 reach here
    }
    // Threads 16+ never reach the barrier -> deadlock!
}

// Correct version
__global__ void correctKernel() {
    int tid = threadIdx.x;
    __shared__ int flag;

    if (tid < 16) {
        // Do work for threads 0-15
        flag = 1;
    }

    __syncthreads();  // All threads reach this

    // All threads can now safely use flag
}
```

### **16.6.2 Deadlock Detection and Prevention**

Prevent deadlocks by ensuring all threads in a block follow the same control flow for synchronization points.

```cpp
class DeadlockDetector {
private:
    cudaEvent_t start_, stop_;
    float timeout_ms_;

public:
    DeadlockDetector(float timeout_ms = 5000.0f)
        : timeout_ms_(timeout_ms) {
        CHECK_CUDA(cudaEventCreate(&start_));
        CHECK_CUDA(cudaEventCreate(&stop_));
    }

    ~DeadlockDetector() {
        cudaEventDestroy(start_);
        cudaEventDestroy(stop_);
    }

    void startTiming() {
        CHECK_CUDA(cudaEventRecord(start_));
    }

    bool checkDeadlock() {
        cudaError_t err = cudaEventQuery(stop_);
        if (err == cudaErrorNotReady) {
            float elapsed;
            CHECK_CUDA(cudaEventElapsedTime(&elapsed, start_, stop_));
            if (elapsed > timeout_ms_) {
                return true;  // Potential deadlock
            }
        }
        return false;
    }
};
```

---

## **16.7 Error Recovery Strategies**

Production systems need robust error recovery mechanisms. Instead of crashing on GPU errors, applications should gracefully handle failures and continue operating with degraded performance if necessary.

### **16.7.1 Graceful Degradation**

Implement fallback mechanisms to CPU computation when GPU operations fail. This ensures your application remains functional even when CUDA resources are unavailable.

```cpp
class CudaComputation {
private:
    bool useCuda_ = true;

public:
    void compute(float* data, int size) {
        if (useCuda_) {
            cudaError_t err = computeOnGPU(data, size);
            if (err != cudaSuccess) {
                fprintf(stderr, "GPU computation failed: %s\n",
                       cudaGetErrorString(err));
                fprintf(stderr, "Falling back to CPU\n");
                useCuda_ = false;
                computeOnCPU(data, size);
            }
        } else {
            computeOnCPU(data, size);
        }
    }

private:
    cudaError_t computeOnGPU(float* data, int size);
    void computeOnCPU(float* data, int size);
};
```

### **16.7.2 Retry Mechanism**

Implement intelligent retry logic for transient failures like temporary resource exhaustion or device busy states.

```cpp
// Implemented in test_error_handling.cu with test cases
template<typename Func>
bool retryOperation(Func operation, int maxRetries = 3) {
    for (int attempt = 0; attempt < maxRetries; ++attempt) {
        cudaError_t err = operation();

        if (err == cudaSuccess) {
            return true;
        }

        fprintf(stderr, "Attempt %d failed: %s\n",
                attempt + 1, cudaGetErrorString(err));

        // Reset CUDA context for certain errors
        if (err == cudaErrorIllegalAddress ||
            err == cudaErrorLaunchFailure) {
            cudaDeviceReset();
        }

        // Wait before retry
        std::this_thread::sleep_for(
            std::chrono::milliseconds(100 * (attempt + 1)));
    }

    return false;
}

// Usage
bool success = retryOperation([&]() {
    return launchKernel(data, size);
});
```

---

## **16.8 Logging and Diagnostics**

Effective logging is essential for debugging production issues that can't be reproduced in development. A good logging system captures enough detail to diagnose problems without impacting performance.

### **16.8.1 Comprehensive Logging System**

Implement multi-level logging to control verbosity in different environments. Debug logs help development while production logs focus on critical issues.

```cpp
enum LogLevel {
    LOG_DEBUG = 0,
    LOG_INFO = 1,
    LOG_WARNING = 2,
    LOG_ERROR = 3
};

class CudaLogger {
private:
    LogLevel level_;
    std::ofstream logFile_;

public:
    CudaLogger(const std::string& filename, LogLevel level = LOG_INFO)
        : level_(level), logFile_(filename, std::ios::app) {}

    void log(LogLevel level, const std::string& message) {
        if (level >= level_) {
            auto now = std::chrono::system_clock::now();
            auto time_t = std::chrono::system_clock::to_time_t(now);

            logFile_ << "[" << std::put_time(std::localtime(&time_t),
                                            "%Y-%m-%d %H:%M:%S") << "] ";
            logFile_ << levelToString(level) << ": " << message << std::endl;
        }
    }

    void logCudaError(cudaError_t error, const std::string& context) {
        if (error != cudaSuccess) {
            std::ostringstream oss;
            oss << context << " - " << cudaGetErrorString(error);
            log(LOG_ERROR, oss.str());
        }
    }

private:
    const char* levelToString(LogLevel level) {
        switch(level) {
            case LOG_DEBUG: return "DEBUG";
            case LOG_INFO: return "INFO";
            case LOG_WARNING: return "WARNING";
            case LOG_ERROR: return "ERROR";
            default: return "UNKNOWN";
        }
    }
};
```

### **16.8.2 Device-Side Printf Debugging**

Device-side printf enables debugging kernel execution directly, though it has performance impact and buffer limitations.

```cpp
__global__ void debugKernel(float* data, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Device-side printf (limited buffer size)
    if (idx == 0) {
        printf("Block %d, Thread %d: Starting kernel\n",
               blockIdx.x, threadIdx.x);
    }

    if (idx < size) {
        float oldVal = data[idx];
        data[idx] = idx * 2.0f;

        // Conditional debug output
        if (idx % 1000 == 0) {
            printf("idx=%d: %f -> %f\n", idx, oldVal, data[idx]);
        }
    }
}

// Host code to flush printf buffer
void flushPrintfBuffer() {
    CHECK_CUDA(cudaDeviceSynchronize());
}
```

---

## **16.9 Production Error Handling**

Production environments require sophisticated error handling that balances reliability, performance, and observability. Implement comprehensive error tracking while maintaining system stability under failure conditions.

### **16.9.1 Production-Ready Error Handler**

A centralized error handler provides consistent error management across your application. It tracks error statistics, implements recovery strategies, and provides monitoring hooks.

```cpp
class CudaErrorHandler {
private:
    struct ErrorStats {
        std::atomic<int> totalErrors{0};
        std::atomic<int> recoveredErrors{0};
        std::unordered_map<cudaError_t, int> errorCounts;
        std::mutex mutex;
    } stats_;

    CudaLogger logger_;

public:
    CudaErrorHandler(const std::string& logFile)
        : logger_(logFile, LOG_WARNING) {}

    bool handleError(cudaError_t error, const std::string& context) {
        if (error == cudaSuccess) return true;

        stats_.totalErrors++;

        {
            std::lock_guard<std::mutex> lock(stats_.mutex);
            stats_.errorCounts[error]++;
        }

        logger_.logCudaError(error, context);

        // Attempt recovery based on error type
        bool recovered = attemptRecovery(error);

        if (recovered) {
            stats_.recoveredErrors++;
        }

        return recovered;
    }

    void printStatistics() {
        std::cout << "=== CUDA Error Statistics ===" << std::endl;
        std::cout << "Total errors: " << stats_.totalErrors << std::endl;
        std::cout << "Recovered: " << stats_.recoveredErrors << std::endl;

        std::lock_guard<std::mutex> lock(stats_.mutex);
        for (const auto& [error, count] : stats_.errorCounts) {
            std::cout << cudaGetErrorName(error) << ": " << count << std::endl;
        }
    }

private:
    bool attemptRecovery(cudaError_t error) {
        switch(error) {
            case cudaErrorMemoryAllocation:
                // Try to free unused memory
                cudaDeviceReset();
                return true;

            case cudaErrorLaunchTimeout:
                // Kernel took too long, might recover
                cudaDeviceReset();
                return true;

            case cudaErrorIllegalAddress:
            case cudaErrorIllegalInstruction:
                // Serious errors, cannot recover
                return false;

            default:
                return false;
        }
    }
};
```

### **16.9.2 Health Monitoring**

Continuous health monitoring helps detect degradation before complete failure occurs, enabling proactive maintenance.

```cpp
class CudaHealthMonitor {
private:
    struct DeviceHealth {
        size_t freeMemory;
        size_t totalMemory;
        float temperature;
        int smClock;
        int memoryClock;
        bool isHealthy;
    };

public:
    DeviceHealth checkHealth(int device = 0) {
        DeviceHealth health;

        CHECK_CUDA(cudaSetDevice(device));

        // Check memory
        CHECK_CUDA(cudaMemGetInfo(&health.freeMemory, &health.totalMemory));

        // Check if we have enough free memory (e.g., 10% threshold)
        float memoryUsage = 1.0f - (float)health.freeMemory / health.totalMemory;

        health.isHealthy = (memoryUsage < 0.9f);

        if (!health.isHealthy) {
            fprintf(stderr, "Warning: Low GPU memory (%.1f%% used)\n",
                   memoryUsage * 100);
        }

        return health;
    }

    void continuous Monitoring(std::chrono::seconds interval) {
        while (true) {
            auto health = checkHealth();

            if (!health.isHealthy) {
                // Send alert, log, or take action
                handleUnhealthyState(health);
            }

            std::this_thread::sleep_for(interval);
        }
    }

private:
    void handleUnhealthyState(const DeviceHealth& health) {
        // Log the issue
        // Send notification
        // Attempt cleanup
        // Scale down workload
    }
};
```

---

## **16.10 Troubleshooting Common Issues**

This section provides practical solutions to the most frequently encountered CUDA errors. Each issue includes symptoms, root causes, diagnostic steps, and proven fixes.

### **16.10.1 "cudaErrorInvalidConfiguration" - Invalid Kernel Launch**

**Symptoms:**
- Kernel fails immediately at launch
- Error message: "invalid configuration argument"

**Common Causes:**
1. Block size exceeds device limits (usually max 1024 threads)
2. Shared memory request exceeds available shared memory per block
3. Too many registers requested per thread

**Diagnostic Steps:**
```cpp
// Check device limits
cudaDeviceProp prop;
cudaGetDeviceProperties(&prop, 0);
printf("Max threads per block: %d\n", prop.maxThreadsPerBlock);
printf("Shared memory per block: %zu bytes\n", prop.sharedMemPerBlock);
printf("Registers per block: %d\n", prop.regsPerBlock);
```

**Solutions:**
```cpp
// Problem: Block size too large
dim3 blockSize(32, 32);  // 1024 threads - might exceed limit on some GPUs

// Solution: Reduce block size
dim3 blockSize(16, 16);  // 256 threads - safe for all modern GPUs

// Problem: Too much shared memory
__shared__ float sdata[2048];  // 8KB - might exceed limit

// Solution: Check and reduce shared memory usage
extern __shared__ float sdata[];  // Use dynamic allocation
// Launch with: kernel<<<grid, block, shared_size>>>
```

### **16.10.2 "cudaErrorIllegalAddress" - Memory Access Violation**

**Symptoms:**
- Kernel fails during execution
- Crash or incorrect results
- Error message: "an illegal memory access was encountered"

**Common Causes:**
1. Out-of-bounds array access
2. Accessing freed memory
3. Null pointer dereference
4. Misaligned memory access

**Diagnostic Steps:**
```bash
# Use compute-sanitizer to pinpoint exact location
compute-sanitizer --tool memcheck ./your_program

# Look for output like:
# Invalid __global__ write of size 4 bytes
#     at kernel.cu:45 in myKernel
```

**Solutions:**
```cpp
// Problem: Missing bounds check
__global__ void kernel(float* data, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    data[idx] = idx;  // ❌ Out of bounds if idx >= N
}

// Solution: Always check bounds
__global__ void kernel(float* data, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {  // ✅ Boundary check
        data[idx] = idx;
    }
}

// Problem: Null pointer
float* d_data = nullptr;
kernel<<<1, 256>>>(d_data, 256);  // ❌ Crash

// Solution: Validate pointers
if (d_data != nullptr) {
    kernel<<<1, 256>>>(d_data, 256);  // ✅ Safe
}
```

### **16.10.3 "cudaErrorLaunchTimeout" - Kernel Execution Timeout**

**Symptoms:**
- Kernel fails after running for several seconds
- Display driver stops responding
- Error message: "the launch timed out and was terminated"

**Common Causes:**
1. Infinite loop in kernel
2. Computation takes too long (>2 seconds on display GPU)
3. Watchdog timer triggered

**Diagnostic Steps:**
```cpp
// Add timing to identify slow kernels
CudaTimer timer;
timer.start();
myKernel<<<grid, block>>>(args...);
cudaDeviceSynchronize();
timer.stop();
printf("Kernel took %.2f ms\n", timer.elapsed_ms());
```

**Solutions:**
```cpp
// Solution 1: Break work into smaller chunks
// Instead of processing all data at once
for (int offset = 0; offset < total_size; offset += chunk_size) {
    kernel<<<grid, block>>>(data + offset, chunk_size);
    cudaDeviceSynchronize();  // Allow GPU to rest between launches
}

// Solution 2: Use non-display GPU if available
int deviceCount;
cudaGetDeviceCount(&deviceCount);
if (deviceCount > 1) {
    cudaSetDevice(1);  // Use secondary GPU
}

// Solution 3: Disable timeout (on non-display GPUs)
// This requires system configuration changes
// See: nvidia-smi -pm 1 (persistence mode)
```

### **16.10.4 "cudaErrorMemoryAllocation" - Out of Memory**

**Symptoms:**
- cudaMalloc fails
- Error message: "out of memory"
- Application cannot allocate GPU memory

**Diagnostic Steps:**
```cpp
// Check available memory
size_t free_mem, total_mem;
cudaMemGetInfo(&free_mem, &total_mem);
printf("GPU Memory: %.2f GB free / %.2f GB total\n",
       free_mem / 1e9, total_mem / 1e9);

// Check memory fragmentation
cudaDeviceReset();  // Clear all allocations
cudaMemGetInfo(&free_mem, &total_mem);  // Check again
```

**Solutions:**
```cpp
// Solution 1: Reduce memory usage
// Problem: Allocating too much at once
float* big_array = cuda_malloc<float>(1000000000);  // 4GB

// Solution: Use streaming/batching
const size_t batch_size = 10000000;  // 40MB batches
for (size_t i = 0; i < total; i += batch_size) {
    float* batch = cuda_malloc<float>(batch_size);
    processBatch<<<grid, block>>>(batch, batch_size);
    cuda_free(batch);
}

// Solution 2: Free unused memory
cudaFree(d_temp_array);  // Free temporary buffers immediately

// Solution 3: Use unified memory for large datasets
float* data;
cudaMallocManaged(&data, size);  // Automatically paged
```

### **16.10.5 Race Conditions and Non-Deterministic Results**

**Symptoms:**
- Results vary between runs
- Correct results sometimes, incorrect other times
- Different results on different GPUs

**Diagnostic Steps:**
```bash
# Use racecheck to detect data races
compute-sanitizer --tool racecheck ./your_program

# Look for output like:
# Hazard detected: write-after-write
#     at kernel.cu:23 in myKernel
```

**Solutions:**
```cpp
// Problem: Missing synchronization
__global__ void racey_kernel(float* data) {
    __shared__ float sdata[256];
    int tid = threadIdx.x;

    sdata[tid] = data[tid];
    // ❌ Missing __syncthreads()

    if (tid < 128) {
        sdata[tid] += sdata[tid + 128];  // Race condition!
    }
}

// Solution: Add proper synchronization
__global__ void safe_kernel(float* data) {
    __shared__ float sdata[256];
    int tid = threadIdx.x;

    sdata[tid] = data[tid];
    __syncthreads();  // ✅ Ensure all writes complete

    if (tid < 128) {
        sdata[tid] += sdata[tid + 128];  // Safe
    }
}

// Problem: Global memory race
__global__ void atomic_needed(int* counter) {
    *counter += 1;  // ❌ Race condition
}

// Solution: Use atomic operations
__global__ void atomic_safe(int* counter) {
    atomicAdd(counter, 1);  // ✅ Thread-safe
}
```

### **16.10.6 Debugging Checklist**

When encountering CUDA errors, follow this systematic checklist:

**Step 1: Identify Error Type**
- [ ] Check return codes from all CUDA API calls
- [ ] Check `cudaGetLastError()` after kernel launches
- [ ] Identify if error is synchronous or asynchronous

**Step 2: Reproduce Reliably**
- [ ] Can you reproduce the error consistently?
- [ ] Does it occur with specific input sizes or patterns?
- [ ] Does it vary between debug and release builds?

**Step 3: Isolate the Problem**
- [ ] Comment out code sections to narrow down the issue
- [ ] Test with minimal example
- [ ] Check if error occurs with different launch configurations

**Step 4: Use Debug Tools**
```bash
# Memory errors
compute-sanitizer --tool memcheck ./program

# Race conditions
compute-sanitizer --tool racecheck ./program

# Synchronization errors
compute-sanitizer --tool synccheck ./program

# Interactive debugging
cuda-gdb ./program
```

**Step 5: Verify Assumptions**
- [ ] Print device capabilities and compare with requirements
- [ ] Verify memory allocation succeeded before use
- [ ] Check that grid/block dimensions are within limits
- [ ] Ensure pointers are valid device pointers

**Step 6: Add Instrumentation**
```cpp
// Add debug output
#ifdef DEBUG
    printf("Thread (%d,%d): value = %f\n",
           blockIdx.x, threadIdx.x, value);
#endif

// Add assertions
CUDA_ASSERT_BOUNDS(idx, size);

// Add timing
CudaTimer timer;
timer.start();
kernel<<<grid, block>>>(args);
timer.stop();
printf("Kernel time: %.2f ms\n", timer.elapsed_ms());
```

---

## **16.11 Tool Usage Guide**

This section provides detailed instructions for using CUDA debugging and profiling tools effectively.

### **16.11.1 Compute Sanitizer - Memory Error Detection**

Compute Sanitizer is NVIDIA's comprehensive tool for detecting memory errors, race conditions, and synchronization issues in CUDA applications.

**Basic Usage:**
```bash
# Memory error detection (most common)
compute-sanitizer --tool memcheck ./your_program

# Detailed output with line numbers
compute-sanitizer --tool memcheck \
    --print-level info \
    --log-file memcheck.log \
    ./your_program

# Continue execution after error (find all errors)
compute-sanitizer --tool memcheck \
    --error-exitcode 0 \
    ./your_program
```

**Race Condition Detection:**
```bash
# Basic race detection
compute-sanitizer --tool racecheck ./your_program

# Detailed hazard analysis
compute-sanitizer --tool racecheck \
    --racecheck-report all \
    --print-level info \
    ./your_program

# Focus on specific hazards
compute-sanitizer --tool racecheck \
    --racecheck-report hazard \
    ./your_program
```

**Synchronization Checking:**
```bash
# Detect deadlocks and sync issues
compute-sanitizer --tool synccheck ./your_program

# Verbose synchronization analysis
compute-sanitizer --tool synccheck \
    --print-level info \
    --synccheck-max-errors 100 \
    ./your_program
```

**Initialization Checking:**
```bash
# Detect uninitialized memory usage
compute-sanitizer --tool initcheck ./your_program

# Track initialization precisely
compute-sanitizer --tool initcheck \
    --track-unused-memory yes \
    ./your_program
```

**Example Output Interpretation:**
```
========= COMPUTE-SANITIZER
========= Invalid __global__ write of size 4 bytes
=========     at 0x2a0 in myKernel(float*, int)
=========     by thread (0,0,0) in block (16,0,0)
=========     Address 0x7f8c40000400 is out of bounds
=========     Device Frame:myKernel(float*, int) (mykernel.cu:45)
=========     Saved host backtrace up to driver entry point at kernel launch time
=========     Host Frame: [0x2e3e57]
```

**Interpretation:**
- Thread (0,0,0) in block (16,0,0) tried to write 4 bytes
- Access occurred at line 45 of mykernel.cu
- Address 0x7f8c40000400 is outside allocated memory

### **16.11.2 CUDA-GDB - Interactive Debugging**

CUDA-GDB is an extension of GDB for debugging CUDA applications. It allows setting breakpoints in kernels, inspecting GPU state, and stepping through device code.

**Setup and Basic Usage:**
```bash
# Compile with debug symbols
nvcc -g -G -o program program.cu

# Start cuda-gdb
cuda-gdb ./program

# Basic commands
(cuda-gdb) break myKernel          # Break at kernel entry
(cuda-gdb) break myKernel.cu:45    # Break at specific line
(cuda-gdb) run                     # Start execution
(cuda-gdb) cuda thread             # Show current CUDA thread
(cuda-gdb) cuda block              # Show current block
```

**CUDA-Specific Commands:**
```bash
# Thread navigation
(cuda-gdb) cuda kernel             # List all kernels
(cuda-gdb) cuda block 5            # Switch to block 5
(cuda-gdb) cuda thread 32          # Switch to thread 32
(cuda-gdb) cuda thread (2,3)       # Switch to thread at 2D index

# Memory inspection
(cuda-gdb) print threadIdx.x       # Print thread ID
(cuda-gdb) print blockIdx.x        # Print block ID
(cuda-gdb) print data[threadIdx.x] # Print array element
(cuda-gdb) print @sdata[0]@64      # Print 64 elements of shared mem

# Execution control
(cuda-gdb) cuda device 0           # Switch to device 0
(cuda-gdb) info cuda kernels       # Show running kernels
(cuda-gdb) info cuda blocks        # Show blocks in current kernel
(cuda-gdb) info cuda threads       # Show threads in current block
```

**Advanced Debugging Techniques:**
```bash
# Conditional breakpoints
(cuda-gdb) break myKernel.cu:45 if threadIdx.x == 0

# Watch expressions
(cuda-gdb) watch data[idx]         # Break when data[idx] changes

# Backtrace for GPU threads
(cuda-gdb) backtrace              # Show call stack

# Inspect shared memory
(cuda-gdb) print/x *(int(*)[256])sdata  # View shared array
```

**Example Debug Session:**
```bash
$ cuda-gdb ./matrix_multiply
(cuda-gdb) break matrixMul.cu:67
Breakpoint 1 at 0x408e40: file matrixMul.cu, line 67.

(cuda-gdb) run
[Switching to CUDA kernel 0, grid 1, block (0,0,0), thread (0,0,0)]
Breakpoint 1, matrixMulKernel(float*, float*, float*, int) at matrixMul.cu:67

(cuda-gdb) print threadIdx.x
$1 = 0

(cuda-gdb) cuda thread (5,5)
[Switching to CUDA kernel 0, grid 1, block (0,0,0), thread (5,5,0)]

(cuda-gdb) print sum
$2 = 42.5

(cuda-gdb) continue
```

### **16.11.3 Nsight Compute - Kernel Profiling**

Nsight Compute provides detailed performance analysis of individual CUDA kernels.

**Command-Line Usage:**
```bash
# Basic profiling
ncu ./your_program

# Profile specific kernel
ncu --kernel-name myKernel ./your_program

# Full metric collection
ncu --set full --launch-skip 0 --launch-count 1 ./your_program

# Export to file for GUI analysis
ncu --set full -o profile_output ./your_program
# Then open in nsight-compute GUI
```

**Focus on Specific Metrics:**
```bash
# Memory bandwidth analysis
ncu --metrics dram__throughput.avg.pct_of_peak_sustained_elapsed \
    ./your_program

# Occupancy analysis
ncu --metrics sm__warps_active.avg.pct_of_peak_sustained_active \
    ./your_program

# Instruction throughput
ncu --metrics smsp__inst_executed.avg.per_cycle_active \
    ./your_program
```

**Generate Reports:**
```bash
# HTML report
ncu --set full --export report ./your_program
# Creates report.ncu-rep

# CSV export for custom analysis
ncu --csv --metrics dram__throughput,smsp__inst_executed \
    ./your_program > metrics.csv
```

### **16.11.4 Nsight Systems - Application Profiling**

Nsight Systems provides system-wide performance analysis, showing CPU and GPU activity over time.

**Basic Profiling:**
```bash
# Profile application with default settings
nsys profile ./your_program

# Profile with specific duration
nsys profile --duration 30 ./your_program

# Profile with NVTX markers
nsys profile --trace cuda,nvtx,osrt ./your_program
```

**Advanced Options:**
```bash
# Export to specific format
nsys profile -o my_profile --export sqlite ./your_program

# Sample CPU stacks
nsys profile --sample=cpu --backtrace=dwarf ./your_program

# Profile multi-process application
nsys profile --trace-fork-before-exec=true ./launcher
```

**Analyzing Results:**
```bash
# View in GUI
nsys-ui my_profile.nsys-rep

# Generate report
nsys stats my_profile.nsys-rep

# Export to SQLite for custom queries
nsys export --type sqlite --output profile.sqlite my_profile.nsys-rep
```

**NVTX Markers for Custom Regions:**
```cpp
#include <nvToolsExt.h>

// Mark specific code regions
nvtxRangePush("Data Transfer");
cudaMemcpy(d_data, h_data, size, cudaMemcpyHostToDevice);
nvtxRangePop();

nvtxRangePush("Kernel Execution");
myKernel<<<grid, block>>>(d_data);
nvtxRangePop();
```

### **16.11.5 Tool Selection Guide**

**Choose the Right Tool:**

| Problem | Tool | Command |
|---------|------|---------|
| Memory errors (out-of-bounds, leaks) | Compute Sanitizer (memcheck) | `compute-sanitizer --tool memcheck` |
| Race conditions | Compute Sanitizer (racecheck) | `compute-sanitizer --tool racecheck` |
| Synchronization issues | Compute Sanitizer (synccheck) | `compute-sanitizer --tool synccheck` |
| Kernel crashes | CUDA-GDB | `cuda-gdb ./program` |
| Performance bottlenecks | Nsight Compute | `ncu --set full ./program` |
| CPU-GPU interaction | Nsight Systems | `nsys profile ./program` |
| Algorithm correctness | CUDA-GDB + printf | `cuda-gdb`, `printf()` in kernel |

**Workflow Recommendation:**
1. **Development**: Use compute-sanitizer regularly to catch errors early
2. **Debugging**: Use cuda-gdb for interactive debugging
3. **Optimization**: Use Nsight Systems for overall performance, Nsight Compute for kernel tuning
4. **Production**: Implement error logging and monitoring

---

## **16.12 CUDA Error Glossary**

This glossary provides quick reference for CUDA error codes, their meanings, and common solutions.

### **Memory Errors**

| Error Code | Name | Description | Common Cause | Solution |
|------------|------|-------------|--------------|----------|
| 2 | `cudaErrorMemoryAllocation` | Memory allocation failed | Out of GPU memory | Reduce allocation size, free unused memory, use batching |
| 11 | `cudaErrorInvalidValue` | Invalid argument | Null pointer or invalid size | Check pointer validity, verify sizes |
| 77 | `cudaErrorIllegalAddress` | Illegal memory access | Out-of-bounds access | Add bounds checking, use compute-sanitizer |
| 74 | `cudaErrorMisalignedAddress` | Misaligned access | Pointer not properly aligned | Ensure alignment (use `__align__` or check allocation) |
| 700 | `cudaErrorUnknown` | Unknown error | Various causes | Use compute-sanitizer, check device state |

### **Kernel Launch Errors**

| Error Code | Name | Description | Common Cause | Solution |
|------------|------|-------------|--------------|----------|
| 9 | `cudaErrorInvalidConfiguration` | Invalid launch config | Block size > 1024 or too much shared memory | Reduce block size or shared memory usage |
| 4 | `cudaErrorLaunchFailure` | Kernel launch failed | Assert failure, illegal instruction | Use cuda-gdb to debug kernel |
| 6 | `cudaErrorLaunchTimeout` | Kernel timeout | Kernel runs too long | Break into smaller chunks, use non-display GPU |
| 98 | `cudaErrorLaunchOutOfResources` | Insufficient resources | Too many registers or shared memory | Reduce resource usage per thread |

### **Device Errors**

| Error Code | Name | Description | Common Cause | Solution |
|------------|------|-------------|--------------|----------|
| 10 | `cudaErrorInvalidDevice` | Invalid device ordinal | Device ID out of range | Check device count, use valid device ID |
| 38 | `cudaErrorNoDevice` | No CUDA-capable device | No GPU available | Check hardware, drivers |
| 100 | `cudaErrorNoKernelImageForDevice` | No kernel image for device | Architecture mismatch | Compile for correct architecture |
| 46 | `cudaErrorDeviceAlreadyInUse` | Device in exclusive mode | Another process using GPU | Use different GPU or close other applications |

### **Synchronization Errors**

| Error Code | Name | Description | Common Cause | Solution |
|------------|------|-------------|--------------|----------|
| 35 | `cudaErrorNotReady` | Operation not complete | Async operation still running | Call `cudaDeviceSynchronize()` or wait |
| 52 | `cudaErrorLaunchPendingCountExceeded` | Too many launches | Queue overflow | Add synchronization points |
| 68 | `cudaErrorSyncDepthExceeded` | Synchronization depth exceeded | Nested kernel launches | Reduce nesting depth |

### **API Errors**

| Error Code | Name | Description | Common Cause | Solution |
|------------|------|-------------|--------------|----------|
| 3 | `cudaErrorInitializationError` | Initialization failed | Driver/runtime mismatch | Update drivers, reinstall CUDA |
| 30 | `cudaErrorNotSupported` | Feature not supported | Using unsupported API | Check compute capability |
| 1 | `cudaErrorMissingConfiguration` | Missing config info | Internal error | Update CUDA toolkit |

### **Common Error Patterns**

**Pattern 1: Sticky Errors**
```cpp
// Error persists until explicitly cleared
cudaError_t err = cudaGetLastError();  // Get error
err = cudaGetLastError();              // Get same error again!

// Solution: Clear error state
cudaGetLastError();  // Clear error
// Now error state is clean
```

**Pattern 2: Async Error Reporting**
```cpp
// Error occurs in kernel, but reported later
kernel<<<grid, block>>>(args);  // Returns cudaSuccess
cudaMemcpy(...);                // Returns cudaErrorLaunchFailure!

// Solution: Check after kernel
kernel<<<grid, block>>>(args);
cudaGetLastError();             // Check immediately
cudaDeviceSynchronize();        // Wait for completion
```

**Pattern 3: Multiple Errors**
```cpp
// First error masks subsequent errors
cudaMalloc(&ptr1, huge_size);   // Fails
cudaMalloc(&ptr2, small_size);  // Also fails due to sticky error

// Solution: Check and handle each error
if (cudaMalloc(&ptr1, huge_size) != cudaSuccess) {
    cudaGetLastError();  // Clear error
    // Handle error
}
```

### **Quick Diagnostic Commands**

```bash
# Check CUDA installation
nvidia-smi

# Check device capabilities
deviceQuery  # CUDA samples

# Check for memory leaks
cuda-memcheck --leak-check full ./program

# Check for race conditions
compute-sanitizer --tool racecheck ./program

# Profile kernel
ncu --set full ./program

# System-wide profile
nsys profile ./program
```

### **Error Code Categories**

**Fatal Errors** (Require cudaDeviceReset):
- `cudaErrorIllegalAddress` (77)
- `cudaErrorLaunchFailure` (4)
- `cudaErrorAssert` (710)

**Recoverable Errors** (Can retry):
- `cudaErrorMemoryAllocation` (2)
- `cudaErrorNotReady` (35)
- `cudaErrorLaunchTimeout` (6)

**Configuration Errors** (Fix and relaunch):
- `cudaErrorInvalidConfiguration` (9)
- `cudaErrorInvalidValue` (11)
- `cudaErrorInvalidDevice` (10)

---

## **16.13 Running the Examples**

All examples from this README are implemented in the test files. The modular structure allows for targeted building and testing.

### **Build Commands**

```bash
# From the project root (cuda_exercise/)
cmake -B build
cmake --build build

# Or build only this module
cmake --build build --target 16_Error_Handling_And_Debugging_test
```

### **Test Executables**

After building, two test executables are available:

1. **Error Handling Tests** (`16_Error_Handling_And_Debugging_test`)
   - Located at: `build/10.cuda_basic/16.Error_Handling_and_Debugging/test/`
   - Contains all error handling examples from this README

2. **Long-term Tests** (`16_Error_Handling_And_Debugging_long_term_test`)
   - Stress testing and performance validation

### **Running Tests**

```bash
# Run all error handling tests
./build/10.cuda_basic/16.Error_Handling_and_Debugging/test/16_Error_Handling_And_Debugging_test

# Run specific test cases
./build/.../16_Error_Handling_And_Debugging_test --gtest_filter=ErrorHandlingTest.RaceConditionDetection
./build/.../16_Error_Handling_And_Debugging_test --gtest_filter=ErrorHandlingTest.RetryMechanism

# Run with CTest (from build directory)
ctest -R "16_Error_Handling" --verbose
```

### **Profiling and Sanitization**

The CMake configuration automatically creates sanitizer targets:

```bash
# Memory error detection
cmake --build build --target 16_Error_Handling_And_Debugging_test_memcheck

# Race condition detection
cmake --build build --target 16_Error_Handling_And_Debugging_test_racecheck

# Synchronization checking
cmake --build build --target 16_Error_Handling_And_Debugging_test_synccheck

# Or run manually
compute-sanitizer --tool memcheck ./build/.../16_Error_Handling_And_Debugging_test
compute-sanitizer --tool racecheck ./build/.../16_Error_Handling_And_Debugging_test
```

### **Debug Build**

```bash
# Build with debug symbols
cmake -B build_debug -DCMAKE_BUILD_TYPE=Debug
cmake --build build_debug

# The debug build automatically includes:
# - Device debug symbols (-G flag)
# - DEBUG macro definition
# - Assertions enabled

# Debug with cuda-gdb
cuda-gdb ./build_debug/.../16_Error_Handling_And_Debugging_test
(cuda-gdb) break raceyKernel  # Set breakpoint in kernel
(cuda-gdb) run
```

### **Build Options**

```bash
# Release build (optimized)
cmake -B build_release -DCMAKE_BUILD_TYPE=Release

# Debug build (with device symbols)
cmake -B build_debug -DCMAKE_BUILD_TYPE=Debug

# Custom CUDA architecture
cmake -B build -DCMAKE_CUDA_ARCHITECTURES=86  # For RTX 3090
```

## **16.14 Summary**

### **Key Takeaways**

1. **Always Check CUDA API Calls**: Use error checking macros consistently
2. **Handle Both Sync and Async Errors**: Understand the difference and check appropriately
3. **Use Debugging Tools**: Leverage compute-sanitizer and cuda-gdb
4. **Implement Recovery Strategies**: Plan for graceful degradation
5. **Monitor Production Systems**: Track errors and system health

### **Best Practices Checklist**

✅ Use `CHECK_CUDA` macro for all CUDA API calls
✅ Check kernel launch errors with `cudaGetLastError()`
✅ Synchronize and check after kernel execution
✅ Implement proper error logging
✅ Use RAII for CUDA resource management
✅ Test with compute-sanitizer regularly
✅ Have fallback CPU implementations for critical paths
✅ Monitor GPU health in production

### **Error Handling Flow**

```
1. API Call → CHECK_CUDA → Log Error → Attempt Recovery → Fallback/Exit
2. Kernel Launch → Check Launch → Sync → Check Runtime Errors
3. Async Operations → Query Status → Handle Timeout → Check Errors
```

---

## **Example Code**

### Unit Testing with Google Test

The project uses Google Test framework (`test_error_handling.cu`) for comprehensive error handling testing:

1. **Host-side error testing** using Google Test framework
2. **GPU-side error testing** using GPU_TEST macros
3. **Parameterized tests** for different error scenarios
4. **Direct .cu inclusion** for testing device functions
5. **Error checking utilities** from `cuda_utils.h` library

### Building and Running

```bash
# Build with Debug mode for assertion testing
cmake -DCMAKE_BUILD_TYPE=Debug -B build
cmake --build build --target 16_Error_Handling_And_Debugging_test

# Run all tests
./build/10.cuda_basic/16.Error_Handling_and_Debugging/16_Error_Handling_And_Debugging_test

# Run specific test suite
./build/10.cuda_basic/16.Error_Handling_and_Debugging/16_Error_Handling_And_Debugging_test --gtest_filter="ErrorHandlingTest.*"

# Run with compute-sanitizer for memory error detection
compute-sanitizer --tool memcheck ./build/10.cuda_basic/16.Error_Handling_and_Debugging/16_Error_Handling_And_Debugging_test

# Run with race condition detection
compute-sanitizer --tool racecheck ./build/10.cuda_basic/16.Error_Handling_and_Debugging/16_Error_Handling_And_Debugging_test

# Run with synchronization checking
compute-sanitizer --tool synccheck ./build/10.cuda_basic/16.Error_Handling_and_Debugging/16_Error_Handling_And_Debugging_test

# Use the comprehensive sanitizer target
make 16_Error_Handling_And_Debugging_sanitize_all
```

### Test Coverage

The test suite covers:
- ✅ Basic error checking with CUDA API calls
- ✅ Kernel launch error detection
- ✅ Out-of-bounds memory access detection
- ✅ Assertion-based debugging (debug builds)
- ✅ Error recovery mechanisms
- ✅ Reduction kernel error handling
- ✅ Parameterized testing with various dimensions
- ✅ GPU-side boundary checking
- ✅ Device function testing via direct inclusion

### Testing Approach

This project follows the **direct .cu file inclusion** pattern established in Part 15:
- The test file includes `vector_add_2d.cu` directly
- This allows testing of all device functions, including private `__device__` functions
- Provides complete white-box testing capabilities
- Simplifies build configuration compared to library-based testing

### Error Handling Best Practices Used

The implementation demonstrates proper use of:
- ✅ `CHECK_CUDA()` for all CUDA API calls
- ✅ `CHECK_KERNEL_LAUNCH()` after kernel invocations
- ✅ `cuda_malloc()/cuda_free()` for safe memory management
- ✅ `cuda_memcpy()` with automatic size calculation
- ✅ `grid_size_2d()` for optimal grid configuration
- ✅ `CudaTimer` for performance measurements (available)
- ✅ Debug-only assertions with `CUDA_ASSERT()`

---

**Next**: Part 7 - Memory Hierarchy (Planned)