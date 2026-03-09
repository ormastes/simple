# ⚙️ Part 12: Your First CUDA Kernel

**Goal**: Write, compile, launch, and debug your first CUDA kernel using modern development tools and best practices.

---

## Project Structure
```
12.Your_First_CUDA_Kernel/
├── README.md          - This comprehensive guide
├── CMakeLists.txt     - Build configuration
└── vector_add_2d.cu   - Your first CUDA kernel example
```

## Quick Navigation
- [12.1 Host vs Device Code Separation](#121-host-vs-device-code-separation)
- [12.2 `__global__`, `__device__`, and `dim3` API](#122-__global__-__device__-and-dim3-api)
- [12.3 Launch Configuration with `dim3`](#123-launch-configuration-with-dim3)
- [12.4 CUDA Memory Management APIs](#124-cuda-memory-management-apis)
- [12.5 Complete Vector Add Example](#125-complete-vector-add-example)
- [12.6 CMake Root Configuration](#126-cmake-root-configuration)
- [12.7 Building and Running the Code](#127-building-and-running-the-code)
- [12.8 VSCode Setup and Configuration](#128-vscode-setup-and-configuration)
- [12.9 Configuration Files Explained](#129-configuration-files-explained)
- [12.10 Troubleshooting Common Issues](#1210-troubleshooting-common-issues)
- [12.11 API Recap](#1211-api-recap)
- [12.12 Summary](#1212-summary)

---

## **12.1 Host vs Device Code Separation**

CUDA programs consist of two distinct execution contexts: host code that runs on the CPU and device code that runs on the GPU. Understanding how to properly separate and interact between these two contexts is fundamental to CUDA programming.

### **Execution Space Qualifiers**

CUDA functions are separated by **execution location** and **call origin**:

| Qualifier      | Executes On | Callable From | Description |
|----------------|-------------|----------------|-------------|
| `__host__`     | CPU         | CPU            | Default for all C/C++ functions (can be omitted) |
| `__device__`   | GPU         | GPU            | Helper functions inside kernels, device-only |
| `__global__`   | GPU         | CPU            | Kernel entry point, launched from host |

### **Key Characteristics**

**`__global__` Functions (Kernels):**
- Must return `void`
- Cannot be called from device code (only from host)
- Executed by many threads in parallel
- Can have arguments (passed by value)
- Launch configuration specified with `<<<...>>>`

**`__device__` Functions:**
- Can return any type
- Only callable from device code (other `__device__` or `__global__` functions)
- Execute in the context of a single thread
- Can be inlined for performance

**`__host__ __device__` Functions:**
- Can be combined to compile for both CPU and GPU
- Useful for code reuse
- Different implementations can be selected with `#ifdef __CUDA_ARCH__`

### **Usage Patterns**

You typically use:
- `__global__` for launching kernels (main GPU computation entry points)
- `__device__` for GPU-side helper logic (utility functions within kernels)
- `__host__` (or nothing) for CPU code

**Example:**
```cpp
// Device helper function (GPU only)
__device__ float square(float x) {
    return x * x;
}

// Kernel function (GPU, launched from CPU)
__global__ void vectorSquare(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = square(data[idx]);  // Call device function
    }
}

// Host function (CPU)
int main() {
    // ... allocate memory ...
    vectorSquare<<<blocks, threads>>>(d_data, n);  // Launch kernel
    // ... copy results back ...
}
```

---

## **12.2 `__global__`, `__device__`, and `dim3` API**

This section introduces the core syntax elements for writing GPU kernels, including function qualifiers and the dimensional configuration types that organize thread execution.

### **12.2.1 `__global__` Kernel Functions**

Kernels are the entry points for GPU computation, callable from the host (CPU) but executed on the device (GPU):

```cpp
__global__ void myKernel(float* input, float* output, int n) {
    // Kernel code executes on GPU
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = input[idx] * 2.0f;
    }
}
```

**Important Rules:**
- Must return `void` (no return value)
- Parameters are passed by value (pointers are fine)
- Cannot be called from device code
- Launch with `<<<grid, block>>>` syntax

### **12.2.2 `__device__` Helper Functions**

Helper functions usable **only** inside other device functions or kernels:

```cpp
__device__ float square(float x) {
    return x * x;
}

__device__ float compute(float a, float b) {
    return square(a) + square(b);
}

__global__ void kernel(float* data) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    data[idx] = compute(data[idx], 2.0f);  // Call device function
}
```

**Advantages:**
- Can return values (unlike `__global__`)
- Compiler can inline for zero overhead
- Keeps code organized and reusable
- Can use recursion (with limited depth)

### **12.2.3 `dim3`: Multi-Dimensional Thread Organization**

CUDA provides the `dim3` type to specify grid and block dimensions in 1D, 2D, or 3D structures:

```cpp
// 1D example: 1,048,576 threads in 1D grid
dim3 blocks(4096, 1, 1);    // 4096 blocks
dim3 threads(256, 1, 1);    // 256 threads per block
kernel<<<blocks, threads>>>(...);

// 2D example: Process 1024x1024 image
dim3 blocks2D((1024+15)/16, (1024+15)/16);  // Grid of blocks
dim3 threads2D(16, 16);                      // 256 threads per block (16x16)
imageKernel<<<blocks2D, threads2D>>>(...);

// 3D example: Process volumetric data
dim3 blocks3D(8, 8, 8);     // 8x8x8 grid
dim3 threads3D(8, 8, 8);    // 512 threads per block (8x8x8)
volumeKernel<<<blocks3D, threads3D>>>(...);
```

**Shortcuts for 1D cases:**
```cpp
// These are equivalent
kernel<<<4096, 256>>>(...);
kernel<<<dim3(4096), dim3(256)>>>(...);
```

### **12.2.4 Built-in Thread Position Variables**

Inside kernels, you can access thread position using built-in variables:

| Variable | Description | Range |
|----------|-------------|-------|
| `threadIdx.x/y/z` | Thread index within block | 0 to (blockDim - 1) |
| `blockIdx.x/y/z` | Block index within grid | 0 to (gridDim - 1) |
| `blockDim.x/y/z` | Dimensions of block (threads per block) | Configured at launch |
| `gridDim.x/y/z` | Dimensions of grid (blocks per grid) | Configured at launch |

**Calculating Global Thread Position:**

For 1D:
```cpp
int idx = blockIdx.x * blockDim.x + threadIdx.x;
```

For 2D:
```cpp
int x = blockIdx.x * blockDim.x + threadIdx.x;
int y = blockIdx.y * blockDim.y + threadIdx.y;
```

For 3D:
```cpp
int x = blockIdx.x * blockDim.x + threadIdx.x;
int y = blockIdx.y * blockDim.y + threadIdx.y;
int z = blockIdx.z * blockDim.z + threadIdx.z;
```

This helps map GPU threads to 2D/3D data structures like images, matrices, or volumes.

---

## **12.3 Launch Configuration with `dim3`**

Properly configuring the grid and block dimensions is crucial for effective GPU utilization. This section explains how to calculate launch configurations for different problem sizes and data layouts.

### **12.3.1 Why Configuration Matters**

The launch configuration determines:
- **Total threads**: `gridDim.x × blockDim.x` (for 1D)
- **Occupancy**: How many threads run concurrently on each SM
- **Performance**: Proper sizing maximizes GPU utilization
- **Correctness**: Must cover all data elements

### **12.3.2 1D Launch Configuration**

For processing arrays or vectors:

```cpp
// Problem: Process N elements
int N = 1000000;  // 1 million elements

// Choose block size (typically 128, 256, or 512)
int threads = 256;

// Calculate grid size (round up to cover all elements)
int blocks = (N + threads - 1) / threads;  // Ceiling division

// Launch kernel
kernel<<<blocks, threads>>>(data, N);
```

**Inside kernel:**
```cpp
__global__ void kernel(float* data, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Boundary check (may have more threads than elements)
    if (idx < N) {
        data[idx] = data[idx] * 2.0f;
    }
}
```

### **12.3.3 2D Launch Configuration**

For processing images, matrices, or 2D grids:

```cpp
// Problem: Process width × height image
int width = 1024;
int height = 1024;

// Use 2D blocks (common: 16x16 = 256 threads, or 32x32 = 1024 threads)
dim3 threadsPerBlock(16, 16);

// Calculate 2D grid size
dim3 blocksPerGrid(
    (width + threadsPerBlock.x - 1) / threadsPerBlock.x,
    (height + threadsPerBlock.y - 1) / threadsPerBlock.y
);

// Launch kernel
kernel2D<<<blocksPerGrid, threadsPerBlock>>>(image, width, height);
```

**Inside kernel:**
```cpp
__global__ void kernel2D(float* image, int width, int height) {
    // Calculate 2D position
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    // Boundary check
    if (x < width && y < height) {
        // Convert 2D coordinates to 1D array index
        int idx = y * width + x;
        image[idx] = image[idx] * 2.0f;
    }
}
```

### **12.3.4 3D Launch Configuration**

For processing volumetric data or 3D grids:

```cpp
// Problem: Process depth × height × width volume
int width = 256, height = 256, depth = 256;

// Use 3D blocks (e.g., 8x8x8 = 512 threads)
dim3 threadsPerBlock(8, 8, 8);

// Calculate 3D grid size
dim3 blocksPerGrid(
    (width + 7) / 8,
    (height + 7) / 8,
    (depth + 7) / 8
);

// Launch kernel
kernel3D<<<blocksPerGrid, threadsPerBlock>>>(volume, width, height, depth);
```

**Inside kernel:**
```cpp
__global__ void kernel3D(float* volume, int width, int height, int depth) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;
    int z = blockIdx.z * blockDim.z + threadIdx.z;

    if (x < width && y < height && z < depth) {
        // 3D to 1D index: z * (height * width) + y * width + x
        int idx = z * height * width + y * width + x;
        volume[idx] = volume[idx] * 2.0f;
    }
}
```

### **12.3.5 Choosing Block Size**

**Common block sizes:**
- **1D**: 128, 256, 512 threads
- **2D**: 16×16 (256), 32×32 (1024)
- **3D**: 8×8×8 (512)

**Guidelines:**
- Block size should be a multiple of warp size (32)
- Typical range: 128-1024 threads per block
- Balance between occupancy and resource usage
- 256 is often a good default for 1D
- 16×16 is common for 2D (good for shared memory tiling)

**Resource Limits (per block):**
- Maximum threads: 1024 (most GPUs)
- Maximum x/y/z dimensions: 1024/1024/64
- Shared memory: 48-164 KB depending on GPU
- Registers: Limited per thread, affects occupancy

---

## **12.4 CUDA Memory Management APIs**

Before executing kernels, you need to allocate memory on the GPU and transfer data between host and device. This section covers the fundamental CUDA memory management APIs.

### **12.4.1 Memory Allocation & Transfer APIs**

These functions manage GPU memory and data transfer:

| API Function | Description | Example Usage |
|--------------|-------------|---------------|
| `cudaMalloc()` | Allocates memory on GPU device | `cudaMalloc(&d_ptr, size)` |
| `cudaFree()` | Frees GPU memory | `cudaFree(d_ptr)` |
| `cudaMemcpy()` | Copies data between host and device | `cudaMemcpy(dst, src, size, direction)` |
| `cudaMemset()` | Sets GPU memory to a value | `cudaMemset(d_ptr, 0, size)` |
| `cudaDeviceSynchronize()` | Waits for all GPU operations to complete | `cudaDeviceSynchronize()` |

### **12.4.2 Memory Allocation Example**

```cpp
// Allocate host memory (CPU)
int N = 1024 * 1024;
size_t bytes = N * sizeof(float);
float* h_data = (float*)malloc(bytes);

// Allocate device memory (GPU)
float* d_data;
cudaError_t err = cudaMalloc(&d_data, bytes);
if (err != cudaSuccess) {
    printf("cudaMalloc failed: %s\n", cudaGetErrorString(err));
    return -1;
}

// ... use memory ...

// Free memory
free(h_data);       // Free host memory
cudaFree(d_data);   // Free device memory
```

### **12.4.3 cudaMemcpy Direction Flags**

The direction parameter specifies the transfer direction:

| Flag | Direction | Usage |
|------|-----------|-------|
| `cudaMemcpyHostToDevice` | CPU → GPU | Upload input data before kernel |
| `cudaMemcpyDeviceToHost` | GPU → CPU | Download results after kernel |
| `cudaMemcpyDeviceToDevice` | GPU → GPU | Copy between GPU buffers |
| `cudaMemcpyHostToHost` | CPU → CPU | Rarely used (just use memcpy) |

### **12.4.4 Complete Workflow Example**

```cpp
// Step 1: Allocate and initialize host data
int N = 1024;
size_t bytes = N * sizeof(float);
float* h_input = (float*)malloc(bytes);
float* h_output = (float*)malloc(bytes);

for (int i = 0; i < N; i++) {
    h_input[i] = (float)i;
}

// Step 2: Allocate device memory
float *d_input, *d_output;
cudaMalloc(&d_input, bytes);
cudaMalloc(&d_output, bytes);

// Step 3: Copy input data to device
cudaMemcpy(d_input, h_input, bytes, cudaMemcpyHostToDevice);

// Step 4: Launch kernel
int threads = 256;
int blocks = (N + threads - 1) / threads;
kernel<<<blocks, threads>>>(d_input, d_output, N);

// Step 5: Wait for kernel to finish
cudaDeviceSynchronize();

// Step 6: Copy results back to host
cudaMemcpy(h_output, d_output, bytes, cudaMemcpyDeviceToHost);

// Step 7: Verify results
for (int i = 0; i < 10; i++) {
    printf("output[%d] = %f\n", i, h_output[i]);
}

// Step 8: Free memory
cudaFree(d_input);
cudaFree(d_output);
free(h_input);
free(h_output);
```

### **12.4.5 Kernel Launch Syntax**

The triple angle bracket syntax launches kernels:

```cpp
kernelName<<<gridDim, blockDim, sharedMemBytes, stream>>>(args);
```

**Parameters:**
- **gridDim**: Number of blocks (int or dim3)
- **blockDim**: Threads per block (int or dim3)
- **sharedMemBytes**: Dynamic shared memory (optional, default 0)
- **stream**: CUDA stream for async execution (optional, default 0)

**Examples:**
```cpp
// Simple 1D launch
kernel<<<100, 256>>>(data, n);

// 2D launch
dim3 grid(32, 32);
dim3 block(16, 16);
kernel<<<grid, block>>>(data, width, height);

// With shared memory
kernel<<<blocks, threads, sharedBytes>>>(data, n);

// With stream
cudaStream_t stream;
cudaStreamCreate(&stream);
kernel<<<blocks, threads, 0, stream>>>(data, n);
```

### **12.4.6 Built-in Variables (Available in Kernels)**

Inside any kernel or device function, these variables provide thread position information:

| Variable | Type | Description |
|----------|------|-------------|
| `threadIdx.x/y/z` | uint3 | Thread index within block (0-based) |
| `blockIdx.x/y/z` | uint3 | Block index within grid (0-based) |
| `blockDim.x/y/z` | dim3 | Number of threads per block |
| `gridDim.x/y/z` | dim3 | Number of blocks in grid |

**Typical usage:**
```cpp
__global__ void kernel(float* data) {
    // Calculate unique thread ID
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    // Process data
    data[tid] = data[tid] * 2.0f;
}
```

---

## **12.5 Complete Vector Add Example**

This section presents a complete, working CUDA program that demonstrates all the concepts covered so far. The example computes `C[i] = A[i]² + B[i]` for a 2D grid of data.

### **12.5.1 Full Code with Detailed Explanations**

The complete program is available in [`vector_add_2d.cu`](vector_add_2d.cu). Here's the annotated version:

```cpp
// vector_add_2d.cu - Complete first CUDA kernel example
#include <iostream>
#include <cuda_runtime.h>

//==============================================================================
// DEVICE FUNCTIONS (GPU-only helper functions)
//==============================================================================

// Device function: runs on GPU, callable only from GPU
// This demonstrates code reuse within device code
__device__ float square(float x) {
    return x * x;
}

//==============================================================================
// KERNEL FUNCTIONS (GPU entry points, callable from CPU)
//==============================================================================

// Kernel function: runs on GPU, launched from CPU
// Computes: C[i] = A[i]² + B[i] for all elements
__global__ void vector_add_2d(const float* A, const float* B, float* C,
                              int width, int height) {
    // Step 1: Calculate this thread's 2D position in the grid
    int x = blockIdx.x * blockDim.x + threadIdx.x;  // Column
    int y = blockIdx.y * blockDim.y + threadIdx.y;  // Row

    // Step 2: Convert 2D position to 1D array index
    // Row-major order: idx = row * width + col
    int i = y * width + x;

    // Step 3: Boundary check to prevent out-of-bounds access
    // Grid may be larger than data due to rounding in block calculation
    if (x < width && y < height) {
        // Step 4: Perform computation
        // Each thread computes exactly one element
        C[i] = square(A[i]) + B[i];
    }
}

//==============================================================================
// HOST CODE (CPU)
//==============================================================================

int main() {
    // Define problem size: 1024x1024 = 1,048,576 elements
    int width = 1024;
    int height = 1024;
    int N = width * height;
    size_t size = N * sizeof(float);

    std::cout << "Computing vector operation on " << N << " elements" << std::endl;
    std::cout << "Grid size: " << width << "x" << height << std::endl;

    //==========================================================================
    // STEP 1: Allocate host (CPU) memory
    //==========================================================================

    float *h_A = (float*)malloc(size);  // h_ prefix = host memory
    float *h_B = (float*)malloc(size);
    float *h_C = (float*)malloc(size);

    if (!h_A || !h_B || !h_C) {
        std::cerr << "Host memory allocation failed!" << std::endl;
        return -1;
    }

    //==========================================================================
    // STEP 2: Initialize input data on host
    //==========================================================================

    for (int i = 0; i < N; ++i) {
        h_A[i] = static_cast<float>(i);      // A[i] = i
        h_B[i] = static_cast<float>(2 * i);  // B[i] = 2*i
    }
    std::cout << "Initialized input data" << std::endl;

    //==========================================================================
    // STEP 3: Allocate device (GPU) memory
    //==========================================================================

    float *d_A, *d_B, *d_C;  // d_ prefix = device memory

    cudaError_t err;
    err = cudaMalloc(&d_A, size);
    if (err != cudaSuccess) {
        std::cerr << "cudaMalloc d_A failed: " << cudaGetErrorString(err) << std::endl;
        free(h_A); free(h_B); free(h_C);
        return -1;
    }

    cudaMalloc(&d_B, size);
    cudaMalloc(&d_C, size);
    std::cout << "Allocated GPU memory: " << (size * 3 / (1024*1024)) << " MB" << std::endl;

    //==========================================================================
    // STEP 4: Copy input data from host to device
    //==========================================================================

    cudaMemcpy(d_A, h_A, size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B, size, cudaMemcpyHostToDevice);
    std::cout << "Copied input data to GPU" << std::endl;

    //==========================================================================
    // STEP 5: Configure kernel launch parameters
    //==========================================================================

    // Use 16x16 threads per block (256 total threads)
    dim3 threads(16, 16);

    // Calculate number of blocks needed
    // Round up: (width + threads.x - 1) / threads.x ensures we cover all elements
    dim3 blocks(
        (width + threads.x - 1) / threads.x,    // Blocks in x direction
        (height + threads.y - 1) / threads.y    // Blocks in y direction
    );

    std::cout << "Launch config: " << blocks.x << "x" << blocks.y << " blocks, "
              << threads.x << "x" << threads.y << " threads per block" << std::endl;
    std::cout << "Total threads: " << (blocks.x * threads.x * blocks.y * threads.y) << std::endl;

    //==========================================================================
    // STEP 6: Launch kernel
    //==========================================================================

    vector_add_2d<<<blocks, threads>>>(d_A, d_B, d_C, width, height);

    // Check for kernel launch errors
    err = cudaGetLastError();
    if (err != cudaSuccess) {
        std::cerr << "Kernel launch failed: " << cudaGetErrorString(err) << std::endl;
        cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
        free(h_A); free(h_B); free(h_C);
        return -1;
    }

    std::cout << "Kernel launched" << std::endl;

    //==========================================================================
    // STEP 7: Wait for kernel completion and copy results back
    //==========================================================================

    // Wait for all GPU operations to complete
    cudaDeviceSynchronize();
    std::cout << "Kernel completed" << std::endl;

    // Copy results back from device to host
    cudaMemcpy(h_C, d_C, size, cudaMemcpyDeviceToHost);
    std::cout << "Copied results back to CPU" << std::endl;

    //==========================================================================
    // STEP 8: Verify results
    //==========================================================================

    std::cout << "\nVerifying results (first 10 elements):" << std::endl;
    bool correct = true;

    for (int i = 0; i < 10; i++) {
        float expected = h_A[i] * h_A[i] + h_B[i];  // A[i]² + B[i]
        std::cout << "C[" << i << "] = " << h_C[i]
                  << " (expected: " << expected << ")";

        if (h_C[i] != expected) {
            std::cout << " MISMATCH!";
            correct = false;
        }
        std::cout << std::endl;
    }

    if (correct) {
        std::cout << "\n✓ All results correct!" << std::endl;
    } else {
        std::cout << "\n✗ Results incorrect!" << std::endl;
    }

    //==========================================================================
    // STEP 9: Free memory
    //==========================================================================

    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
    free(h_A);
    free(h_B);
    free(h_C);

    std::cout << "\nProgram completed successfully" << std::endl;
    return 0;
}
```

### **12.5.2 Key Concepts Demonstrated**

This example demonstrates all essential CUDA programming concepts:

| Concept | Code Location | Purpose |
|---------|---------------|---------|
| **Device Function** | `__device__ float square()` | Reusable GPU helper function |
| **Kernel Function** | `__global__ void vector_add_2d()` | Main GPU computation entry point |
| **Thread Indexing** | `blockIdx.x * blockDim.x + threadIdx.x` | Calculate global thread position |
| **2D to 1D Mapping** | `y * width + x` | Convert 2D coordinates to array index |
| **Grid Configuration** | `dim3 blocks((width+15)/16, ...)` | Calculate number of blocks (round up) |
| **Boundary Check** | `if (x < width && y < height)` | Prevent out-of-bounds access |
| **Memory Allocation** | `cudaMalloc(&d_A, size)` | Allocate GPU memory |
| **Data Transfer** | `cudaMemcpy(..., cudaMemcpyHostToDevice)` | Copy data to/from GPU |
| **Synchronization** | `cudaDeviceSynchronize()` | Wait for GPU to finish |
| **Error Checking** | `cudaGetLastError()` | Detect kernel launch errors |

### **12.5.3 Expected Output**

```
Computing vector operation on 1048576 elements
Grid size: 1024x1024
Initialized input data
Allocated GPU memory: 12 MB
Copied input data to GPU
Launch config: 64x64 blocks, 16x16 threads per block
Total threads: 1048576
Kernel launched
Kernel completed
Copied results back to CPU

Verifying results (first 10 elements):
C[0] = 0 (expected: 0)
C[1] = 3 (expected: 3)
C[2] = 8 (expected: 8)
C[3] = 15 (expected: 15)
C[4] = 24 (expected: 24)
C[5] = 35 (expected: 35)
C[6] = 48 (expected: 48)
C[7] = 63 (expected: 63)
C[8] = 80 (expected: 80)
C[9] = 99 (expected: 99)

✓ All results correct!

Program completed successfully
```

### **12.5.4 Computation Breakdown**

The computation `C[i] = A[i]² + B[i]` produces:

| Index i | A[i] | B[i] | A[i]² | C[i] = A[i]² + B[i] |
|---------|------|------|-------|---------------------|
| 0 | 0 | 0 | 0 | 0 |
| 1 | 1 | 2 | 1 | 3 |
| 2 | 2 | 4 | 4 | 8 |
| 3 | 3 | 6 | 9 | 15 |
| 4 | 4 | 8 | 16 | 24 |
| 5 | 5 | 10 | 25 | 35 |

### **12.5.5 Memory Layout**

For 1024×1024 2D grid stored in row-major order:

```
Element [y][x] is at 1D index: y * width + x

Example for 1024×1024 grid:
[0][0] → index 0
[0][1] → index 1
[0][1023] → index 1023
[1][0] → index 1024
[1][1] → index 1025
...
[1023][1023] → index 1048575
```

---

## **12.6 CMake Root Configuration**

Proper CMake configuration is essential for building CUDA projects. This section covers the root-level CMakeLists.txt setup that configures the CUDA build environment.

### **12.6.1 Root CMakeLists.txt Setup**

Before building CUDA projects, ensure your root `CMakeLists.txt` (in the project root directory) is properly configured:

```cmake
cmake_minimum_required(VERSION 3.18 FATAL_ERROR)

#===============================================================================
# CUDA Toolkit Configuration
#===============================================================================

# Set CUDA toolkit root (adjust path for your system)
set(CMAKE_CUDA_COMPILER /usr/local/cuda/bin/nvcc)
set(CUDAToolkit_ROOT /usr/local/cuda)

# Set CUDA architectures before project() call
# 75=Turing, 80=Ampere A100, 86=Ampere RTX 30 series, 89=Ada RTX 40 series
# You can use 'native' to auto-detect your current GPU
set(CMAKE_CUDA_ARCHITECTURES 75;80;86)

#===============================================================================
# Project Declaration
#===============================================================================

# Enable CUDA language support
project(cuda_project LANGUAGES CXX CUDA)

#===============================================================================
# C++ and CUDA Standards
#===============================================================================

# Set C++20 standard for both host and device code
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(CMAKE_CUDA_STANDARD 20)
set(CMAKE_CUDA_STANDARD_REQUIRED ON)

#===============================================================================
# Find CUDA Toolkit
#===============================================================================

find_package(CUDAToolkit REQUIRED)

#===============================================================================
# Global CUDA Settings
#===============================================================================

# Enable separate compilation for device code (allows linking device code)
set(CMAKE_CUDA_SEPARABLE_COMPILATION ON)

# Resolve device symbols during linking
set(CMAKE_CUDA_RESOLVE_DEVICE_SYMBOLS ON)

# Position-independent code (required for shared libraries)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

#===============================================================================
# Build Type Configurations
#===============================================================================

# Set default build type if not specified
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Debug" CACHE STRING "Build type" FORCE)
endif()

# Compiler flags for different build types
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    # Debug: Enable device debugging, disable optimizations
    add_compile_options(
        "$<$<COMPILE_LANGUAGE:CUDA>:-G;-g;-O0>"      # CUDA debug flags
        "$<$<COMPILE_LANGUAGE:CXX>:-g3;-O0;-Wall>"   # C++ debug flags
    )
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
    # Release: Full optimizations
    add_compile_options(
        "$<$<COMPILE_LANGUAGE:CUDA>:-O3;-use_fast_math;--ptxas-options=-v>"
        "$<$<COMPILE_LANGUAGE:CXX>:-O3;-march=native>"
    )
endif()

#===============================================================================
# Subdirectories
#===============================================================================

add_subdirectory(10.cuda_basic)
add_subdirectory(20.cuda_intermediate)
# ... other subdirectories
```

### **12.6.2 Key Configuration Elements**

These settings configure the CUDA build environment:

| Setting | Purpose | Example Value |
|---------|---------|---------------|
| `CMAKE_CUDA_COMPILER` | Path to nvcc compiler | `/usr/local/cuda/bin/nvcc` |
| `CUDAToolkit_ROOT` | CUDA installation directory | `/usr/local/cuda` |
| `CMAKE_CUDA_ARCHITECTURES` | Target GPU architectures | `75;80;86` or `native` |
| `CMAKE_CUDA_STANDARD` | C++ standard for CUDA code | `20` (C++20) |
| `CMAKE_CUDA_SEPARABLE_COMPILATION` | Enable device code linking | `ON` |
| `CMAKE_CUDA_RESOLVE_DEVICE_SYMBOLS` | Resolve device symbols at link time | `ON` |
| `CMAKE_POSITION_INDEPENDENT_CODE` | Generate position-independent code | `ON` (required for libraries) |

### **12.6.3 GPU Architecture Selection**

The `CMAKE_CUDA_ARCHITECTURES` setting determines which GPU architectures your code supports:

**Common Architecture Values:**

| Architecture | Compute Capability | GPU Examples |
|--------------|-------------------|--------------|
| `60` | 6.0 | Pascal (P100, GTX 1080) |
| `70` | 7.0 | Volta (V100, Titan V) |
| `75` | 7.5 | Turing (RTX 2080, T4, GTX 1660) |
| `80` | 8.0 | Ampere (A100, A40) |
| `86` | 8.6 | Ampere (RTX 3090, RTX 3080, RTX 3070) |
| `89` | 8.9 | Ada Lovelace (RTX 4090, RTX 4080) |
| `90` | 9.0 | Hopper (H100, H200) |
| `native` | Auto-detect | Current GPU |

**Setting Architecture:**

```cmake
# Single architecture (compile for one GPU type)
set(CMAKE_CUDA_ARCHITECTURES 86)

# Multiple architectures (fat binary, larger executable)
set(CMAKE_CUDA_ARCHITECTURES 75;80;86;89)

# Auto-detect current GPU (requires GPU present at build time)
set(CMAKE_CUDA_ARCHITECTURES native)

# All supported architectures (very large binary)
set(CMAKE_CUDA_ARCHITECTURES all)

# Mix real and virtual architectures
set(CMAKE_CUDA_ARCHITECTURES 75-real;80-real;86-virtual)
```

**Real vs Virtual Architectures:**
- **Real** (`XX-real` or just `XX`): Compiles to SASS (executable binary for specific GPU)
- **Virtual** (`XX-virtual`): Compiles to PTX (intermediate representation, JIT compiled at runtime)

### **12.6.4 Build Type Configuration**

Customize compiler flags for Debug and Release builds:

```cmake
# Debug build: Enable debugging, disable optimizations
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    add_compile_options(
        # CUDA flags
        "$<$<COMPILE_LANGUAGE:CUDA>:-G>"           # Enable device debugging
        "$<$<COMPILE_LANGUAGE:CUDA>:-g>"           # Generate debug info
        "$<$<COMPILE_LANGUAGE:CUDA>:-O0>"          # No optimization
        "$<$<COMPILE_LANGUAGE:CUDA>:-lineinfo>"    # Line number info for profiler

        # C++ flags
        "$<$<COMPILE_LANGUAGE:CXX>:-g3>"           # Max debug info
        "$<$<COMPILE_LANGUAGE:CXX>:-O0>"           # No optimization
        "$<$<COMPILE_LANGUAGE:CXX>:-Wall>"         # All warnings
        "$<$<COMPILE_LANGUAGE:CXX>:-Wextra>"       # Extra warnings
    )
# Release build: Maximum performance
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
    add_compile_options(
        # CUDA flags
        "$<$<COMPILE_LANGUAGE:CUDA>:-O3>"                    # Max optimization
        "$<$<COMPILE_LANGUAGE:CUDA>:-use_fast_math>"         # Fast math operations
        "$<$<COMPILE_LANGUAGE:CUDA>:--ptxas-options=-v>"     # Verbose PTX assembler
        "$<$<COMPILE_LANGUAGE:CUDA>:-maxrregcount=32>"       # Limit registers (optional)

        # C++ flags
        "$<$<COMPILE_LANGUAGE:CXX>:-O3>"                     # Max optimization
        "$<$<COMPILE_LANGUAGE:CXX>:-march=native>"           # CPU-specific optimizations
        "$<$<COMPILE_LANGUAGE:CXX>:-DNDEBUG>"                # Disable assertions
    )
endif()
```

### **12.6.5 Project Structure Example**

```
cuda_exercise/
├── CMakeLists.txt                     # Root configuration (above)
├── CMakePresets.json                  # Build presets (see section 12.8.5)
├── .vscode/                           # VSCode configuration
│   ├── settings.json
│   └── launch.json
├── 10.cuda_basic/
│   ├── CMakeLists.txt                 # add_subdirectory() calls
│   └── 12.Your_First_CUDA_Kernel/
│       ├── CMakeLists.txt             # Target definition
│       └── vector_add_2d.cu           # CUDA source
└── build/                              # Build directory (created by CMake)
    ├── CMakeCache.txt
    ├── compile_commands.json          # For IntelliSense
    └── 10.cuda_basic/
        └── 12.Your_First_CUDA_Kernel/
            └── 12_YourFirstCUDAKernel # Executable
```

---

## **12.7 Building and Running the Code**

This section covers multiple ways to build and run CUDA programs, from VSCode integration to command-line builds.

### **12.7.1 Building with VSCode (Recommended)**

VSCode with CMake Tools extension provides the best development experience for CUDA projects.

#### **Quick Build with Keyboard Shortcuts**

1. **Configure CMake** (first time only):
   - Press `Ctrl+Shift+P` (Cmd+Shift+P on Mac) to open Command Palette
   - Type "CMake: Configure" and select it
   - Choose your preset (e.g., "default" for Debug build, "release" for Release)

2. **Build the Project**:
   - Press `Ctrl+Shift+B` or `F7` to build all targets
   - Or use Command Palette: `Ctrl+Shift+P` → "CMake: Build"
   - Build output appears in the terminal pane

3. **Select Build Target** (optional):
   - Click on the target name in the status bar (bottom)
   - Or Command Palette: `Ctrl+Shift+P` → "CMake: Set Build Target"
   - Choose which executable to build

4. **Run without Debugging**:
   - Press `Ctrl+F5` to run the current target
   - Or Command Palette: `Ctrl+Shift+P` → "CMake: Run Without Debugging"
   - Output appears in terminal

5. **Debug the Program**:
   - Press `F5` to start debugging (requires `launch.json` configuration)
   - Set breakpoints by clicking on line numbers
   - Use debug toolbar to step through code

#### **VSCode Status Bar Controls**

The bottom status bar provides quick access to CMake functions:

| Control | Function |
|---------|----------|
| **Build Preset** | Click to select CMake preset (default, release, etc.) |
| **Build Target** | Click to select which executable to build |
| **Build Button** | Click "Build" to compile |
| **Debug/Run Button** | Click play icon (▶) to run, bug icon (🐛) to debug |
| **Build Status** | Shows build progress and status |

### **12.7.2 Building with Command Line**

For those who prefer command-line workflows or CI/CD integration:

#### **Using CMake Commands**

```bash
# Navigate to project root
cd /path/to/cuda_exercise

# Create build directory (first time only)
mkdir -p build
cd build

# Configure CMake with default preset
cmake --preset=default

# OR configure without preset (manual)
cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug ..

# Build the project
cmake --build .

# OR use Ninja directly (if using Ninja generator)
ninja

# Run the executable
./10.cuda_basic/12.Your_First_CUDA_Kernel/12_YourFirstCUDAKernel
```

#### **Using CMake Presets from CLI**

CMakePresets.json simplifies command-line builds:

```bash
# List available presets
cmake --list-presets

# Configure with specific preset
cmake --preset=default          # Debug with system compiler
cmake --preset=default-clang    # Debug with Clang
cmake --preset=release          # Release build

# Build with preset (from project root, not build dir)
cmake --build --preset=default

# Clean build
cmake --build --preset=default --target clean

# Build specific target
cmake --build --preset=default --target 12_YourFirstCUDAKernel
```

#### **Direct NVCC Compilation (Simple Projects)**

For quick testing without CMake (single-file projects):

```bash
# Basic compilation
nvcc vector_add_2d.cu -o vector_add

# With debug symbols (for cuda-gdb)
nvcc -G -g vector_add_2d.cu -o vector_add

# With optimizations
nvcc -O3 -use_fast_math vector_add_2d.cu -o vector_add

# Specify compute capability
nvcc -arch=sm_86 vector_add_2d.cu -o vector_add

# Verbose output (see compilation steps)
nvcc -v vector_add_2d.cu -o vector_add

# Generate PTX intermediate code
nvcc -ptx vector_add_2d.cu -o vector_add.ptx

# Run the program
./vector_add
```

### **12.7.3 Build Output Structure**

After building, your directory structure will look like:

```
build/
├── CMakeCache.txt                 # CMake configuration cache
├── CMakeFiles/                    # CMake internal files
├── compile_commands.json          # For IntelliSense/clangd
├── cmake_install.cmake
├── build.ninja                    # Ninja build rules (if using Ninja)
├── 10.cuda_basic/
│   ├── CMakeFiles/
│   └── 12.Your_First_CUDA_Kernel/
│       ├── CMakeFiles/
│       ├── 12_YourFirstCUDAKernel # <-- Executable
│       └── ...
└── ...
```

### **12.7.4 Running and Verifying**

```bash
# Navigate to build directory
cd build

# Run the executable (adjust path as needed)
./10.cuda_basic/12.Your_First_CUDA_Kernel/12_YourFirstCUDAKernel

# Check exit code
echo $?  # Should be 0 on success

# Run with cuda-memcheck (detects memory errors)
cuda-memcheck ./10.cuda_basic/12.Your_First_CUDA_Kernel/12_YourFirstCUDAKernel

# Run with profiler
nsys profile --stats=true ./10.cuda_basic/12.Your_First_CUDA_Kernel/12_YourFirstCUDAKernel
```

---

## **12.8 VSCode Setup and Configuration**

VSCode provides excellent support for CUDA development when properly configured. This section covers the installation and configuration of necessary extensions and settings files.

### **12.8.1 Install Required Extensions**

Install these extensions from the VSCode marketplace:

1. **CUDA Nsight for VSCode** (by NVIDIA)
   - CUDA syntax highlighting
   - cuda-gdb integration for GPU debugging
   - Kernel launch configuration inspection

2. **CMake Tools** (by Microsoft)
   - CMake project configuration
   - Build target selection
   - Integration with VSCode tasks

3. **C/C++ IntelliSense** (by Microsoft)
   - Code completion and navigation
   - Error detection
   - Symbol information

4. **CMake Language Support** (optional)
   - Syntax highlighting for CMakeLists.txt
   - IntelliSense for CMake functions

**Installation:**
- Press `Ctrl+Shift+X` to open Extensions view
- Search for each extension by name
- Click "Install"

### **12.8.2 VSCode Folder Structure**

Your project should have this structure:

```
cuda_exercise/
├── .vscode/                        # VSCode workspace configuration
│   ├── settings.json               # Workspace settings
│   ├── launch.json                 # Debug configurations
│   └── tasks.json                  # Custom tasks (optional)
├── CMakePresets.json               # CMake build presets
├── CMakeLists.txt                  # Root CMake configuration
├── 10.cuda_basic/
│   └── 12.Your_First_CUDA_Kernel/
│       ├── CMakeLists.txt
│       └── vector_add_2d.cu
└── build/                          # Build output (git-ignored)
```

### **12.8.3 `settings.json` (VSCode Workspace Settings)**

Create `.vscode/settings.json` in your project root:

```json
{
    //==========================================================================
    // CMake Configuration
    //==========================================================================

    // Arguments passed to CMake during configuration
    "cmake.configureArgs": [
        "-DCMAKE_BUILD_TYPE=Debug",
        "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON"  // For IntelliSense
    ],

    // Build directory (where compiled binaries go)
    "cmake.buildDirectory": "${workspaceFolder}/build",

    // Generator to use (Ninja is faster than Make)
    "cmake.generator": "Ninja",

    // Configure on opening project
    "cmake.configureOnOpen": false,

    //==========================================================================
    // C++ IntelliSense Configuration
    //==========================================================================

    // Use CMake Tools to provide IntelliSense configuration
    "C_Cpp.default.configurationProvider": "ms-vscode.cmake-tools",

    // IntelliSense engine (Default is usually best)
    "C_Cpp.intelliSenseEngine": "Default",

    //==========================================================================
    // File Associations
    //==========================================================================

    // Map CUDA file extensions to proper language mode
    "files.associations": {
        "*.cu": "cuda-cpp",
        "*.cuh": "cuda-cpp",
        "*.h": "c",
        "*.c": "c"
    },

    //==========================================================================
    // Editor Settings
    //==========================================================================

    // Show whitespace for debugging indentation issues
    "editor.renderWhitespace": "boundary",

    // Ruler at 80/100 characters
    "editor.rulers": [80, 100],

    // Format on save (optional)
    "editor.formatOnSave": false,

    //==========================================================================
    // CUDA-Specific Settings
    //==========================================================================

    // CUDA device selection for debugging (default: 0)
    "cuda-gdb.deviceSelection": 0,

    //==========================================================================
    // Terminal Settings
    //==========================================================================

    // Use bash in WSL2
    "terminal.integrated.defaultProfile.windows": "WSL",

    //==========================================================================
    // Search Exclusions
    //==========================================================================

    // Exclude build directories from search
    "files.exclude": {
        "**/build": true,
        "**/build-*": true
    },

    "search.exclude": {
        "**/build": true,
        "**/build-*": true,
        "**/.git": true
    }
}
```

**What each setting does:**

- `cmake.configureArgs`: Passes build type and enables compile_commands.json
- `cmake.buildDirectory`: Where CMake puts build files
- `C_Cpp.default.configurationProvider`: Connects IntelliSense to CMake
- `files.associations`: Maps `.cu` files to CUDA C++ language mode for proper syntax highlighting

### **12.8.4 `launch.json` (Debug Configurations)**

Create `.vscode/launch.json` for debugging support:

```json
{
  "version": "0.2.0",
  "configurations": [
    //==========================================================================
    // CUDA Debugging Configuration (cuda-gdb)
    //==========================================================================
    {
      "name": "CUDA C++: Launch (cuda-gdb)",
      "type": "cuda-gdb",
      "request": "launch",

      // Program to debug (resolved by CMake)
      "program": "${command:cmake.launchTargetPath}",

      // Command-line arguments
      "args": [],

      // Working directory
      "cwd": "${workspaceFolder}",

      // Stop at entry point
      "stopAtEntry": false,

      // Stop on CUDA API errors
      "onAPIError": "stop",

      // Linux-specific cuda-gdb path
      "linux": {
        "debuggerPath": "/usr/local/cuda/bin/cuda-gdb"
      },

      // Windows WSL cuda-gdb path
      "windows": {
        "debuggerPath": "/usr/local/cuda/bin/cuda-gdb"
      },

      // Environment variables
      "environment": [],

      // Set breakpoints early
      "setupCommands": [
        {
          "description": "Enable pretty-printing",
          "text": "set print pretty on",
          "ignoreFailures": true
        }
      ]
    },

    //==========================================================================
    // CUDA Unit Test Debugging (cuda-gdb)
    //==========================================================================
    {
      "name": "CUDA C++: CTest Launch (cuda-gdb)",
      "type": "cuda-gdb",
      "request": "launch",

      // Test program (resolved by CMake)
      "program": "${cmake.testProgram}",

      // Test arguments
      "args": ["${cmake.testArgs}"],

      // Test working directory
      "cwd": "${cmake.testWorkingDirectory}",

      "stopAtEntry": false,
      "onAPIError": "stop",

      "linux": {
        "debuggerPath": "/usr/local/cuda/bin/cuda-gdb"
      },

      "environment": []
    },

    //==========================================================================
    // Regular GDB Debugging (for host-only code)
    //==========================================================================
    {
      "name": "C++: Launch (gdb)",
      "type": "cppdbg",
      "request": "launch",
      "program": "${command:cmake.launchTargetPath}",
      "args": [],
      "cwd": "${workspaceFolder}",
      "MIMode": "gdb",
      "setupCommands": [
        {
          "description": "Enable pretty-printing",
          "text": "-enable-pretty-printing",
          "ignoreFailures": true
        }
      ]
    }
  ]
}
```

**Key configuration options:**

- `type: "cuda-gdb"`: Uses NVIDIA's CUDA-aware debugger
- `program`: Path to executable (dynamically resolved by CMake)
- `debuggerPath`: Location of cuda-gdb binary
- `onAPIError: "stop"`: Breaks execution when CUDA API errors occur
- `${command:cmake.launchTargetPath}`: CMake Tools variable for current target

### **12.8.5 `CMakePresets.json` (Build Presets)**

Create `CMakePresets.json` in project root for build configurations:

```json
{
    "version": 3,
    "cmakeMinimumRequired": {
        "major": 3,
        "minor": 18,
        "patch": 0
    },

    //==========================================================================
    // Configure Presets
    //==========================================================================

    "configurePresets": [
        {
            "name": "default",
            "displayName": "Default Config (Debug)",
            "description": "Debug build using Ninja with system compiler",
            "generator": "Ninja",
            "binaryDir": "${sourceDir}/build",
            "cacheVariables": {
                "CMAKE_BUILD_TYPE": "Debug",
                "CMAKE_EXPORT_COMPILE_COMMANDS": "ON",
                "CMAKE_CUDA_ARCHITECTURES": "native"
            }
        },
        {
            "name": "default-clang",
            "displayName": "Default Config (Clang, Debug)",
            "description": "Debug build using Ninja and Clang for C++ host code",
            "generator": "Ninja",
            "binaryDir": "${sourceDir}/build-clang",
            "cacheVariables": {
                "CMAKE_C_COMPILER": "clang",
                "CMAKE_CXX_COMPILER": "clang++",
                "CMAKE_CUDA_COMPILER": "nvcc",
                "CMAKE_CUDA_HOST_COMPILER": "clang++",
                "CMAKE_CUDA_FLAGS": "-ccbin=clang++",
                "CMAKE_BUILD_TYPE": "Debug",
                "CMAKE_EXPORT_COMPILE_COMMANDS": "ON",
                "CMAKE_CUDA_ARCHITECTURES": "native"
            }
        },
        {
            "name": "release",
            "displayName": "Release Config",
            "description": "Release build with optimizations using Ninja",
            "generator": "Ninja",
            "binaryDir": "${sourceDir}/build-release",
            "cacheVariables": {
                "CMAKE_BUILD_TYPE": "Release",
                "CMAKE_EXPORT_COMPILE_COMMANDS": "ON",
                "CMAKE_CUDA_ARCHITECTURES": "75;80;86;89"
            }
        }
    ],

    //==========================================================================
    // Build Presets
    //==========================================================================

    "buildPresets": [
        {
            "name": "default",
            "configurePreset": "default"
        },
        {
            "name": "default-clang",
            "configurePreset": "default-clang"
        },
        {
            "name": "release",
            "configurePreset": "release"
        }
    ]
}
```

**What this file does:**
- Defines reusable build configurations for different scenarios
- Eliminates need to manually specify CMake options
- Integrates with VSCode's CMake Tools for easy preset switching
- Ensures consistent build settings across team members

**Available presets:**

| Preset | Compiler | Build Type | Output Dir | Architecture |
|--------|----------|------------|------------|--------------|
| `default` | System default (usually gcc) | Debug | `build/` | Native (auto-detect) |
| `default-clang` | Clang/LLVM | Debug | `build-clang/` | Native |
| `release` | System default | Release | `build-release/` | 75, 80, 86, 89 |

**Selecting presets in VSCode:**
- Click on preset name in status bar, or
- Command Palette: `Ctrl+Shift+P` → "CMake: Select Configure Preset"

### **12.8.6 `CMakeLists.txt` (Module Configuration)**

The CMakeLists.txt in `12.Your_First_CUDA_Kernel/`:

```cmake
# Project name (becomes executable name)
project(12_YourFirstCUDAKernel)

# Create executable from CUDA source
add_executable(${PROJECT_NAME} vector_add_2d.cu)

# Link CUDA runtime (usually automatic)
target_link_libraries(${PROJECT_NAME} CUDA::cudart)

# Optional: Set CUDA-specific properties
set_target_properties(${PROJECT_NAME} PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
)
```

This simple configuration:
- Creates a project/executable named `12_YourFirstCUDAKernel`
- Builds executable from `vector_add_2d.cu`
- CMake automatically detects `.cu` extension and uses nvcc
- Links CUDA runtime library

---

## **12.9 Configuration Files Explained**

This section summarizes how the different configuration files work together to create a complete CUDA development environment.

### **12.9.1 File Purpose Overview**

| File | Purpose | Location |
|------|---------|----------|
| `.vscode/settings.json` | VSCode workspace configuration | Project root |
| `.vscode/launch.json` | Debug configurations | Project root |
| `CMakePresets.json` | Build preset definitions | Project root |
| `CMakeLists.txt` (root) | Project-wide CMake config | Project root |
| `CMakeLists.txt` (module) | Module-specific build config | Each module directory |

### **12.9.2 `.vscode/settings.json` - Workspace Configuration**

Configures how VSCode handles the CUDA project:

| Setting | Purpose |
|---------|---------|
| `cmake.configureArgs` | Passes Debug mode and compile commands export to CMake |
| `cmake.buildDirectory` | Sets build output to `${workspaceFolder}/build` |
| `C_Cpp.default.configurationProvider` | Uses CMake Tools for IntelliSense configuration |
| `files.associations` | Maps `*.cu` and `*.cuh` files to CUDA C++ language mode |
| `cmake.generator` | Specifies build system (Ninja, Make, etc.) |

### **12.9.3 `.vscode/launch.json` - Debug Configurations**

Defines debugging configurations:

**Configuration 1: CUDA C++: Launch (cuda-gdb)**
- Regular CUDA program debugging
- Uses `${command:cmake.launchTargetPath}` to run CMake-built executable
- Breaks on CUDA API errors with `onAPIError: "stop"`
- Uses NVIDIA's cuda-gdb for GPU debugging

**Configuration 2: CUDA C++: CTest Launch (cuda-gdb)**
- For debugging unit tests
- Uses `${cmake.testProgram}` for test executables
- Passes test arguments via `${cmake.testArgs}`

### **12.9.4 `CMakePresets.json` - Build Presets**

Provides reusable build configurations:

| Preset | Compiler | Build Type | Output Directory |
|--------|----------|------------|------------------|
| `default` | System default | Debug | `build/` |
| `default-clang` | Clang/LLVM | Debug | `build-clang/` |
| `release` | System default | Release | `build-release/` |

Each preset specifies:
- Generator (Ninja, Make, etc.)
- Build type (Debug, Release)
- Cache variables (CMake settings)
- Output directory

### **12.9.5 How They Work Together**

```
User Action (F5, Ctrl+Shift+B, etc.)
    ↓
VSCode reads settings.json
    ↓
CMake Tools extension activates
    ↓
Reads CMakePresets.json (selected preset)
    ↓
Configures CMake with preset settings
    ↓
CMake reads CMakeLists.txt files
    ↓
Generates build system (Ninja, Make)
    ↓
Build system compiles .cu files with nvcc
    ↓
Executable is created
    ↓
launch.json configuration runs cuda-gdb on executable
```

**Step-by-Step Process:**

1. **Configuration Phase**: CMake reads root and module CMakeLists.txt, using settings from CMakePresets.json
2. **Generation Phase**: CMake generates build system files (build.ninja, Makefile, etc.)
3. **Build Phase**: Build system invokes nvcc to compile CUDA code
4. **Run/Debug Phase**: launch.json settings determine how to execute or debug the program

---

## **12.10 Troubleshooting Common Issues**

This section covers common problems encountered when building and running CUDA programs, along with their solutions.

### **12.10.1 Build Errors**

| Error Message | Cause | Solution |
|---------------|-------|----------|
| `nvcc: command not found` | CUDA toolkit not installed or not in PATH | Install CUDA and add `/usr/local/cuda/bin` to PATH |
| `CMake Error: CMAKE_CUDA_COMPILER not found` | CMake can't locate nvcc | Set `CMAKE_CUDA_COMPILER=/usr/local/cuda/bin/nvcc` in CMakeLists.txt |
| `undefined reference to cudaMalloc` | Not linking CUDA runtime library | Add `target_link_libraries(target CUDA::cudart)` |
| `unsupported gpu architecture 'compute_XX'` | GPU compute capability mismatch | Check GPU with `nvidia-smi`, set correct `-arch` flag |
| `error: identifier "__global__" is undefined` | File not recognized as CUDA | Ensure file has `.cu` extension |
| `nvcc fatal: Value 'XXX' is not defined for option 'gpu-architecture'` | Invalid architecture specified | Use valid architecture like 75, 80, 86, or 'native' |

### **12.10.2 Runtime Errors**

| Error Message | Cause | Solution |
|---------------|-------|----------|
| `no CUDA-capable device is detected` | No GPU or driver issue | Check `nvidia-smi`, install/update drivers |
| `out of memory` | GPU memory exhausted | Reduce problem size, check for memory leaks, use `cudaFree()` |
| `unspecified launch failure` | Kernel crash (often array bounds) | Add boundary checks, use cuda-memcheck, check grid/block dimensions |
| `invalid device function` | Architecture mismatch | Recompile with correct compute capability for your GPU |
| `invalid argument` | Incorrect kernel launch parameters | Check grid/block dimensions are valid |
| `invalid configuration argument` | Block size too large | Reduce threads per block (max usually 1024) |
| `cudaErrorIllegalAddress` | Out-of-bounds memory access | Use cuda-memcheck to find exact location |

### **12.10.3 VSCode Issues**

**IntelliSense not working for CUDA:**
- Ensure `files.associations` in settings.json maps `.cu` to `cuda-cpp`
- Check that CMake Tools extension is installed and active
- Verify `compile_commands.json` exists in build directory (set `CMAKE_EXPORT_COMPILE_COMMANDS=ON`)
- Reload VSCode window: `Ctrl+Shift+P` → "Reload Window"

**Debugger not stopping at breakpoints:**
- Ensure code is compiled with `-G -g` flags (Debug build)
- Check that you're using Debug configuration, not Release
- Verify cuda-gdb path in launch.json is correct
- Try setting breakpoint in kernel code (device code), not just host code

**CMake configuration fails:**
- Check that CUDA toolkit is installed: `nvcc --version`
- Ensure CMakeLists.txt has `project(name LANGUAGES CUDA CXX)`
- Try manually setting: `cmake -DCMAKE_CUDA_COMPILER=/usr/local/cuda/bin/nvcc ..`
- Delete build directory and reconfigure

**Build target not showing in status bar:**
- Ensure CMake has been configured at least once
- Click "No target selected" in status bar to refresh
- Command Palette: `Ctrl+Shift+P` → "CMake: Set Build Target"

### **12.10.4 Performance Issues**

**Kernel runs slower than expected:**
- Check if you're using Debug build (switch to Release for benchmarking)
- Verify grid/block dimensions are appropriate for your problem size
- Use `nvidia-smi` to monitor GPU utilization (should be high)
- Profile with `nsys profile ./program` to identify bottlenecks
- Check for uncoalesced memory access patterns

**Low GPU utilization:**
- Problem size too small (overhead dominates)
- Block size too small (aim for 128-1024 threads)
- Memory transfer overhead (minimize host-device copies)
- Check occupancy with profiler

### **12.10.5 Memory Issues**

**cuda-memcheck reports errors:**
```bash
cuda-memcheck ./program
```

Common issues detected:
- Out-of-bounds array access
- Use of uninitialized memory
- Race conditions
- Invalid memory operations

**Debugging memory errors:**
1. Run with cuda-memcheck: `cuda-memcheck --leak-check full ./program`
2. Check boundary conditions in kernel code
3. Verify all `cudaMalloc()` calls succeeded
4. Ensure `cudaFree()` is called for all allocations
5. Check that kernel launch parameters don't cause out-of-bounds access

---

## **12.11 API Recap**

This section summarizes the key CUDA APIs and features covered in this part:

| API / Feature     | Category | Description |
| ----------------- | -------- | ----------- |
| `__global__`      | Qualifier | GPU kernel callable from host, must return void |
| `__device__`      | Qualifier | GPU-only helper functions, can return values |
| `__host__`        | Qualifier | CPU functions (default, can be omitted) |
| `dim3`            | Type | 3D dimensions for grid/block configuration |
| `threadIdx.x/y/z` | Built-in Variable | Thread index within block |
| `blockIdx.x/y/z`  | Built-in Variable | Block index within grid |
| `blockDim.x/y/z`  | Built-in Variable | Dimensions of block |
| `gridDim.x/y/z`   | Built-in Variable | Dimensions of grid |
| `cudaMalloc()`    | Memory API | Allocates memory on GPU device |
| `cudaFree()`      | Memory API | Frees GPU memory |
| `cudaMemcpy()`    | Memory API | Transfers memory between host and device |
| `cudaMemset()`    | Memory API | Sets GPU memory to a value |
| `cudaDeviceSynchronize()` | Sync API | Waits for all GPU operations to complete |
| `cudaGetLastError()` | Error API | Returns last CUDA error |
| `cudaGetErrorString()` | Error API | Converts error code to string |
| `<<<grid, block>>>` | Syntax | Kernel launch configuration |

---

## **12.12 Summary**

This comprehensive guide covered all aspects of writing, building, and debugging your first CUDA kernel.

### **Key Takeaways**

1. **Function Qualifiers**: `__global__` for kernels (entry points), `__device__` for GPU helpers, `__host__` (default) for CPU code

2. **Thread Organization**: Use `dim3` to organize threads in 1D/2D/3D grids and blocks, calculate global thread position with built-in variables

3. **Memory Management**: CUDA memory management requires explicit allocation (`cudaMalloc`), transfer (`cudaMemcpy`), and deallocation (`cudaFree`)

4. **Development Workflow**: VSCode + CMake Tools + CUDA Nsight provides excellent development experience with debugging support

5. **Configuration Files**: Proper setup of settings.json, launch.json, and CMakePresets.json streamlines development

### **Complete CUDA Workflow**

```
1. Write Code (vector_add_2d.cu)
   ├── Device functions (__device__)
   ├── Kernel functions (__global__)
   └── Host code (main)

2. Configure Build (CMakeLists.txt, CMakePresets.json)
   ├── Set CUDA architectures
   ├── Configure compiler flags
   └── Define build targets

3. Build Program (VSCode or command line)
   ├── CMake configures project
   ├── nvcc compiles .cu files
   └── Linker creates executable

4. Run/Debug (VSCode or command line)
   ├── Launch executable
   ├── Monitor GPU with nvidia-smi
   └── Debug with cuda-gdb if needed

5. Verify Results
   ├── Check output correctness
   ├── Profile performance
   └── Run cuda-memcheck for errors
```

### **What You Learned**

- ✅ Write CUDA kernels with `__global__` and `__device__` qualifiers
- ✅ Configure 1D, 2D, and 3D thread organizations with `dim3`
- ✅ Manage GPU memory with cudaMalloc/cudaMemcpy/cudaFree
- ✅ Calculate global thread positions from block/thread indices
- ✅ Set up CMake-based CUDA project with proper configuration
- ✅ Use VSCode for CUDA development with debugging support
- ✅ Build and run CUDA programs from VSCode or command line
- ✅ Troubleshoot common build and runtime errors

### **Best Practices**

- Always check boundaries in kernels: `if (idx < N)`
- Use descriptive variable names: `h_` for host, `d_` for device
- Check CUDA errors after critical API calls
- Free all allocated memory to avoid leaks
- Use Debug builds for development, Release for performance testing
- Profile code before optimizing (don't guess what's slow)

### **Next Steps**

- 📚 **Continue to**: [Part 13: Debugging CUDA Programs](../13.Debugging/README.md) - Learn cuda-gdb, cuda-memcheck, and debugging strategies
- 🔧 **Practice**: Modify the vector_add example to perform different operations
- 📊 **Experiment**: Try different grid/block configurations and measure performance
- 💡 **Explore**: Write kernels for 2D image processing or matrix operations

### **References**

- [CUDA Programming Guide - Kernel Execution](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#kernels)
- [CUDA Memory Management](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#memory-management)
- [CMake CUDA Support](https://cmake.org/cmake/help/latest/manual/cmake-language.7.html#cuda)
- [VSCode CMake Tools](https://github.com/microsoft/vscode-cmake-tools)
- [NVIDIA Nsight VSCode Extension](https://developer.nvidia.com/nsight-visual-studio-code-edition)

---

**Congratulations! You've written your first CUDA kernel and set up a complete CUDA development environment. 🚀**

📄 **Next**: [Part 13: Debugging CUDA Programs](../13.Debugging/README.md)
