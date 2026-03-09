# 💾 Part 23: Shared Memory

**Goal**: Master shared memory usage for high-performance CUDA kernels through efficient data sharing and memory access patterns.

## Project Structure
```
23.Shared_Memory/
├── README.md                          - This documentation
├── CMakeLists.txt                     - Build configuration
├── src/
│   ├── CMakeLists.txt                 - Source build configuration
│   ├── kernels/                       - Reusable shared memory kernels
│   │   ├── matrix_multiply_streams.cu - Tiled matrix multiplication
│   │   └── vector_ops_streams.cu      - Shared memory vector operations
│   └── part_specific/                 - Shared memory pattern demonstrations
│       ├── matrix_transpose.cu        - Transpose with bank conflict resolution
│       ├── convolution_1d.cu          - 1D convolution with shared memory
│       ├── reduction.cu               - Parallel reduction patterns
│       └── stencil_1d.cu              - Stencil operations
└── test/
    ├── CMakeLists.txt                 - Test build configuration
    └── unit/
        └── kernels/
            └── test_shared_memory_kernels.cu - Comprehensive tests
```

## Quick Navigation
- [23.1 Overview](#231-overview)
- [23.2 Shared Memory Fundamentals](#232-shared-memory-fundamentals)
- [23.3 Classic Shared Memory Patterns](#233-classic-shared-memory-patterns)
- [23.4 Bank Conflicts](#234-bank-conflicts)
- [23.5 Advanced Optimization Techniques](#235-advanced-optimization-techniques)
- [23.6 Performance Optimization](#236-performance-optimization)
- [23.7 Example Programs](#237-example-programs)
- [23.8 Build & Run](#238-build--run)
- [23.9 Common Pitfalls and Solutions](#239-common-pitfalls-and-solutions)
- [23.10 Best Practices](#2310-best-practices)
- [23.11 Cooperative Groups (Enhanced from Module 25)](#2311-cooperative-groups-enhanced-from-module-25)
- [23.12 Exercises](#2312-exercises)
- [Summary](#-summary)

---

## **23.1 Overview**

Shared memory is a programmable cache that enables fast data sharing among threads within a block. It provides:
- **100x faster** access than global memory
- **User-controlled** caching strategy
- **Inter-thread communication** within blocks
- **Reduced global memory bandwidth** requirements

### **Memory Hierarchy**

| Memory Type | Scope | Latency | Bandwidth | Size |
|------------|-------|---------|-----------|------|
| **Registers** | Thread | ~0 cycles | Highest | 255 per thread |
| **Shared Memory** | Block | ~1-30 cycles | ~10 TB/s | 48-96 KB per SM |
| **L1 Cache** | SM | ~30 cycles | ~4 TB/s | 16-48 KB |
| **L2 Cache** | Device | ~200 cycles | ~2 TB/s | 4-6 MB |
| **Global Memory** | Device | ~400 cycles | ~900 GB/s | 8-80 GB |

---

## **23.2 Shared Memory Fundamentals**

### **23.2.1 Declaration and Allocation**

#### **Static Allocation**
```cuda
__global__ void kernel() {
    // Fixed size known at compile time
    __shared__ float sdata[256];

    // Multi-dimensional arrays
    __shared__ float tile[16][16];
}
```

#### **Dynamic Allocation**
```cuda
__global__ void kernel() {
    // Size specified at kernel launch
    extern __shared__ float sdata[];

    // Access shared memory
    sdata[threadIdx.x] = data[globalIdx];
}

// Launch with dynamic shared memory
kernel<<<blocks, threads, sharedMemSize>>>(...);
```

#### **Multiple Dynamic Arrays**
```cuda
__global__ void kernel(int n) {
    extern __shared__ float shared[];

    // Partition shared memory manually
    float* array1 = shared;
    float* array2 = &shared[n];
    int* array3 = (int*)&shared[2*n];
}
```

### **23.2.2 Memory Configuration**

```cuda
// Query device properties
cudaDeviceProp prop;
cudaGetDeviceProperties(&prop, 0);

printf("Shared memory per block: %zu bytes\n", prop.sharedMemPerBlock);
printf("Shared memory per SM: %zu bytes\n", prop.sharedMemPerMultiprocessor);

// Configure L1/Shared memory split (deprecated in newer GPUs)
cudaFuncSetCacheConfig(kernel, cudaFuncCachePreferShared);
```

---

## **23.3 Classic Shared Memory Patterns**

### **23.3.1 Matrix Multiplication with Tiling**

```cuda
#define TILE_SIZE 16

__global__ void matrixMulShared(float* C, float* A, float* B, int N) {
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int bx = blockIdx.x, by = blockIdx.y;
    int tx = threadIdx.x, ty = threadIdx.y;

    int row = by * TILE_SIZE + ty;
    int col = bx * TILE_SIZE + tx;

    float sum = 0.0f;

    // Loop over tiles
    for (int m = 0; m < (N + TILE_SIZE - 1) / TILE_SIZE; ++m) {
        // Collaborative loading
        if (row < N && m * TILE_SIZE + tx < N)
            As[ty][tx] = A[row * N + m * TILE_SIZE + tx];
        else
            As[ty][tx] = 0.0f;

        if (col < N && m * TILE_SIZE + ty < N)
            Bs[ty][tx] = B[(m * TILE_SIZE + ty) * N + col];
        else
            Bs[ty][tx] = 0.0f;

        __syncthreads();

        // Compute on tile
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; ++k) {
            sum += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    if (row < N && col < N) {
        C[row * N + col] = sum;
    }
}
```

### **23.3.2 1D Stencil Computation**

```cuda
__global__ void stencil1D(float* out, float* in, int N) {
    __shared__ float temp[BLOCK_SIZE + 2 * RADIUS];

    int gindex = blockIdx.x * blockDim.x + threadIdx.x;
    int lindex = threadIdx.x + RADIUS;

    // Load data with halo
    temp[lindex] = in[gindex];

    // Load halo elements
    if (threadIdx.x < RADIUS) {
        temp[lindex - RADIUS] = (gindex >= RADIUS) ?
            in[gindex - RADIUS] : 0.0f;
        temp[lindex + BLOCK_SIZE] = (gindex + BLOCK_SIZE < N) ?
            in[gindex + BLOCK_SIZE] : 0.0f;
    }

    __syncthreads();

    // Apply stencil
    float result = 0.0f;
    #pragma unroll
    for (int offset = -RADIUS; offset <= RADIUS; offset++) {
        result += temp[lindex + offset] * coeff[offset + RADIUS];
    }

    out[gindex] = result;
}
```

### **23.3.3 Parallel Reduction**

```cuda
__global__ void reduce(float* g_idata, float* g_odata, int n) {
    extern __shared__ float sdata[];

    unsigned int tid = threadIdx.x;
    unsigned int i = blockIdx.x * blockDim.x * 2 + threadIdx.x;

    // Load and perform first reduction
    float mySum = (i < n) ? g_idata[i] : 0.0f;
    if (i + blockDim.x < n)
        mySum += g_idata[i + blockDim.x];

    sdata[tid] = mySum;
    __syncthreads();

    // Reduction in shared memory
    for (unsigned int s = blockDim.x / 2; s > 32; s >>= 1) {
        if (tid < s) {
            sdata[tid] = mySum = mySum + sdata[tid + s];
        }
        __syncthreads();
    }

    // Warp reduction
    if (tid < 32) {
        volatile float* smem = sdata;
        if (blockDim.x >= 64) smem[tid] = mySum = mySum + smem[tid + 32];
        if (blockDim.x >= 32) smem[tid] = mySum = mySum + smem[tid + 16];
        if (blockDim.x >= 16) smem[tid] = mySum = mySum + smem[tid + 8];
        if (blockDim.x >= 8)  smem[tid] = mySum = mySum + smem[tid + 4];
        if (blockDim.x >= 4)  smem[tid] = mySum = mySum + smem[tid + 2];
        if (blockDim.x >= 2)  smem[tid] = mySum = mySum + smem[tid + 1];
    }

    // Write result
    if (tid == 0) g_odata[blockIdx.x] = sdata[0];
}
```

---

## **23.4 Bank Conflicts**

### **23.4.1 Understanding Bank Conflicts**

Shared memory is organized into **32 banks** (4-byte wide each). Bank conflicts occur when multiple threads in a warp access different addresses in the same bank.

#### **Conflict-Free Access Patterns**

```cuda
// Linear access - No conflicts
__shared__ float data[256];
float value = data[threadIdx.x];  // Each thread accesses different bank

// Stride-1 access - No conflicts
__shared__ float tile[32][33];  // Padding prevents conflicts
float value = tile[threadIdx.y][threadIdx.x];

// Broadcast - No conflicts
__shared__ float data[256];
float value = data[0];  // All threads read same address
```

#### **Patterns Causing Bank Conflicts**

```cuda
// 2-way bank conflict
__shared__ float data[256];
float value = data[threadIdx.x * 2];  // Even threads conflict

// 32-way bank conflict (worst case)
__shared__ float data[256];
float value = data[threadIdx.x * 32];  // All threads hit same bank

// Matrix transpose - causes conflicts without padding
__shared__ float tile[32][32];
float value = tile[threadIdx.x][threadIdx.y];  // Column access conflicts
```

### **23.4.2 Avoiding Bank Conflicts**

#### **Padding Technique**
```cuda
// Add padding to avoid conflicts in 2D arrays
__shared__ float tile[TILE_SIZE][TILE_SIZE + 1];

__global__ void transposeNoBankConflicts(float* odata, float* idata, int width) {
    __shared__ float tile[TILE_SIZE][TILE_SIZE + 1];  // +1 padding

    int x = blockIdx.x * TILE_SIZE + threadIdx.x;
    int y = blockIdx.y * TILE_SIZE + threadIdx.y;

    // Load tile (coalesced)
    tile[threadIdx.y][threadIdx.x] = idata[y * width + x];
    __syncthreads();

    // Write transposed (no bank conflicts due to padding)
    x = blockIdx.y * TILE_SIZE + threadIdx.x;
    y = blockIdx.x * TILE_SIZE + threadIdx.y;
    odata[y * width + x] = tile[threadIdx.x][threadIdx.y];
}
```

#### **Address Permutation**
```cuda
// Permute thread access pattern to avoid conflicts
__global__ void accessPattern() {
    __shared__ float sdata[256];

    // Original pattern with conflicts
    // int offset = threadIdx.x * STRIDE;

    // Permuted pattern without conflicts
    int offset = ((threadIdx.x + threadIdx.x / 32) * STRIDE) % 256;
    float value = sdata[offset];
}
```

---

## **23.5 Advanced Techniques**

### **23.5.1 Double Buffering**

```cuda
__global__ void pipelineKernel(float* output, float* input, int N) {
    __shared__ float buffer[2][BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = blockIdx.x * blockDim.x + threadIdx.x;

    // Initial load
    int current = 0;
    buffer[current][tid] = input[gid];
    __syncthreads();

    for (int i = 1; i < N / blockDim.x; i++) {
        int next = 1 - current;

        // Load next tile while processing current
        if (gid + i * blockDim.x < N) {
            buffer[next][tid] = input[gid + i * blockDim.x];
        }

        // Process current buffer
        float result = processData(buffer[current][tid]);
        output[gid + (i-1) * blockDim.x] = result;

        __syncthreads();
        current = next;
    }

    // Process last buffer
    output[gid + (N/blockDim.x - 1) * blockDim.x] =
        processData(buffer[current][tid]);
}
```

### **23.5.2 Shared Memory Atomics**

```cuda
__global__ void histogram(int* hist, int* data, int n) {
    __shared__ int smem_hist[256];

    // Initialize shared memory histogram
    if (threadIdx.x < 256) {
        smem_hist[threadIdx.x] = 0;
    }
    __syncthreads();

    // Process data
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        atomicAdd(&smem_hist[data[tid]], 1);
    }
    __syncthreads();

    // Merge to global histogram
    if (threadIdx.x < 256) {
        atomicAdd(&hist[threadIdx.x], smem_hist[threadIdx.x]);
    }
}
```

---

## **23.6 Performance Optimization**

### **23.6.1 Optimization Guidelines**

1. **Maximize Occupancy**
   - Balance shared memory usage with thread count
   - Use dynamic allocation when size varies

2. **Minimize Bank Conflicts**
   - Use padding for 2D arrays
   - Permute access patterns for strided access

3. **Coalesce Global Access**
   - Load to shared memory with coalesced pattern
   - Process in shared memory with any pattern

4. **Hide Latency**
   - Use double buffering
   - Overlap computation with memory access

### **23.6.2 Performance Analysis**

```cuda
// Measure shared memory throughput
__global__ void benchmarkSharedMemory() {
    __shared__ float sdata[1024];

    clock_t start = clock();

    // Perform many shared memory operations
    #pragma unroll
    for (int i = 0; i < 1000; i++) {
        sdata[threadIdx.x] = sdata[threadIdx.x] * 2.0f + 1.0f;
    }

    clock_t end = clock();

    if (threadIdx.x == 0) {
        printf("Cycles: %d\n", (int)(end - start));
    }
}
```

---

## **23.7 Example Programs**

### **23.7.1 Matrix Transpose**

File: `matrix_transpose.cu`
```cuda
#include <cuda_runtime.h>
#include <stdio.h>

#define TILE_DIM 32
#define BLOCK_ROWS 8

// Naive transpose - bank conflicts
__global__ void transposeNaive(float* odata, float* idata, int width, int height) {
    __shared__ float tile[TILE_DIM][TILE_DIM];

    int x = blockIdx.x * TILE_DIM + threadIdx.x;
    int y = blockIdx.y * TILE_DIM + threadIdx.y;

    for (int j = 0; j < TILE_DIM; j += BLOCK_ROWS) {
        if (x < width && (y + j) < height) {
            tile[threadIdx.y + j][threadIdx.x] = idata[(y + j) * width + x];
        }
    }

    __syncthreads();

    x = blockIdx.y * TILE_DIM + threadIdx.x;
    y = blockIdx.x * TILE_DIM + threadIdx.y;

    for (int j = 0; j < TILE_DIM; j += BLOCK_ROWS) {
        if (x < height && (y + j) < width) {
            odata[(y + j) * height + x] = tile[threadIdx.x][threadIdx.y + j];
        }
    }
}

// Optimized transpose - no bank conflicts
__global__ void transposeOptimized(float* odata, float* idata, int width, int height) {
    __shared__ float tile[TILE_DIM][TILE_DIM + 1];  // Padding

    int x = blockIdx.x * TILE_DIM + threadIdx.x;
    int y = blockIdx.y * TILE_DIM + threadIdx.y;

    for (int j = 0; j < TILE_DIM; j += BLOCK_ROWS) {
        if (x < width && (y + j) < height) {
            tile[threadIdx.y + j][threadIdx.x] = idata[(y + j) * width + x];
        }
    }

    __syncthreads();

    x = blockIdx.y * TILE_DIM + threadIdx.x;
    y = blockIdx.x * TILE_DIM + threadIdx.y;

    for (int j = 0; j < TILE_DIM; j += BLOCK_ROWS) {
        if (x < height && (y + j) < width) {
            odata[(y + j) * height + x] = tile[threadIdx.x][threadIdx.y + j];
        }
    }
}
```

### **23.7.2 1D Convolution**

File: `convolution_1d.cu`
```cuda
#define KERNEL_RADIUS 3
#define KERNEL_SIZE (2 * KERNEL_RADIUS + 1)

__constant__ float d_kernel[KERNEL_SIZE];

__global__ void convolution1D(float* output, float* input, int n) {
    __shared__ float s_data[BLOCK_SIZE + 2 * KERNEL_RADIUS];

    int gid = blockIdx.x * blockDim.x + threadIdx.x;
    int lid = threadIdx.x + KERNEL_RADIUS;

    // Load main data
    s_data[lid] = (gid < n) ? input[gid] : 0.0f;

    // Load halo
    if (threadIdx.x < KERNEL_RADIUS) {
        s_data[lid - KERNEL_RADIUS] =
            (gid >= KERNEL_RADIUS) ? input[gid - KERNEL_RADIUS] : 0.0f;
        s_data[lid + BLOCK_SIZE] =
            (gid + BLOCK_SIZE < n) ? input[gid + BLOCK_SIZE] : 0.0f;
    }

    __syncthreads();

    // Compute convolution
    float result = 0.0f;
    #pragma unroll
    for (int i = -KERNEL_RADIUS; i <= KERNEL_RADIUS; i++) {
        result += s_data[lid + i] * d_kernel[KERNEL_RADIUS + i];
    }

    if (gid < n) {
        output[gid] = result;
    }
}
```

---

## **23.8 Build & Run**

This section demonstrates how to build, run, and profile Module 23 using CMake and ninja.

### **Building with Ninja**
```bash
# From project root, configure with ninja
cmake -B build -G Ninja

# Build Module 23 library and tests
ninja -C build 23_Shared_Memory_lib
ninja -C build 23_Shared_Memory_test

# Build demonstration executables
ninja -C build 23_Shared_Memory_transpose_demo
ninja -C build 23_Shared_Memory_convolution_demo
ninja -C build 23_Shared_Memory_reduction_demo
ninja -C build 23_Shared_Memory_stencil_demo

# Or build everything
ninja -C build
```

### **Running Tests**
```bash
# Run all Part 23 tests using ctest
ctest --test-dir build -R 23_Shared_Memory

# Run tests directly for verbose output
./build/20.cuda_intermediate/23.Shared_Memory/test/23_Shared_Memory_test

# Run with GTest filters
./build/20.cuda_intermediate/23.Shared_Memory/test/23_Shared_Memory_test \
    --gtest_filter="*BankConflict*"
```

### **Running Demonstration Executables**
```bash
# Matrix transpose (bank conflict demonstration)
./build/20.cuda_intermediate/23.Shared_Memory/src/23_Shared_Memory_transpose_demo

# 1D Convolution
./build/20.cuda_intermediate/23.Shared_Memory/src/23_Shared_Memory_convolution_demo

# Parallel reduction
./build/20.cuda_intermediate/23.Shared_Memory/src/23_Shared_Memory_reduction_demo

# Stencil operations
./build/20.cuda_intermediate/23.Shared_Memory/src/23_Shared_Memory_stencil_demo
```

### **Profiling with Nsight**
```bash
# Profile tests with Nsight Systems
ninja -C build 23_Shared_Memory_test_nsys

# Profile tests with Nsight Compute (shared memory metrics)
ninja -C build 23_Shared_Memory_test_ncu

# Profile demo executables
ninja -C build 23_Shared_Memory_transpose_demo_nsys
ninja -C build 23_Shared_Memory_reduction_demo_nsys

# Custom profiling for shared memory analysis
nsys profile --stats=true --force-overwrite=true \
    -o transpose_analysis \
    ./build/20.cuda_intermediate/23.Shared_Memory/src/23_Shared_Memory_transpose_demo

# Detailed shared memory metrics
ncu --metrics shared_efficiency,shared_load_throughput,shared_store_throughput \
    --section MemoryWorkloadAnalysis \
    ./build/20.cuda_intermediate/23.Shared_Memory/src/23_Shared_Memory_transpose_demo
```

---

## **23.9 Common Pitfalls and Solutions**

### **Problem 1: Bank Conflicts**
**Symptom**: Poor shared memory throughput
**Solution**: Add padding or permute access patterns

### **Problem 2: Race Conditions**
**Symptom**: Incorrect results
**Solution**: Use proper synchronization with `__syncthreads()`

### **Problem 3: Insufficient Shared Memory**
**Symptom**: Kernel launch failure
**Solution**: Reduce per-block usage or use dynamic allocation

### **Problem 4: Low Occupancy**
**Symptom**: Poor GPU utilization
**Solution**: Balance shared memory usage with thread count

---

## **23.10 Best Practices**

1. **Always profile** shared memory efficiency
2. **Use padding** for 2D arrays to avoid bank conflicts
3. **Minimize synchronization** points
4. **Consider L1 cache** as an alternative for read-only data
5. **Use `__syncthreads()` correctly** - all threads must reach it
6. **Benchmark different configurations** for optimal performance
7. **Document shared memory usage** in kernels

---

## **23.11 Cooperative Groups (Enhanced from Module 25)**

Cooperative Groups is a CUDA programming model extension that provides flexible thread group management beyond traditional `__syncthreads()`. This section enhances Module 25's dynamic parallelism patterns with cooperative groups for better performance and composability.

### **23.11.1 Why Cooperative Groups?**

Traditional CUDA synchronization has limitations:
- `__syncthreads()` only synchronizes entire thread blocks
- No native support for warp-level or sub-block synchronization
- Dynamic parallelism has significant kernel launch overhead (~5-10 μs)
- Grid-wide synchronization requires multiple kernel launches

**Cooperative Groups Benefits:**
- Explicit thread group management at multiple levels
- Warp-level primitives (shuffles, ballots, reductions)
- Grid-wide synchronization in single kernel
- Better composability and code reuse
- Zero overhead for warp operations (vs shared memory)

### **23.11.2 Thread Group Hierarchy**

Cooperative Groups supports multiple synchronization domains:

```cuda
#include <cooperative_groups.h>
namespace cg = cooperative_groups;

__global__ void kernel_with_groups() {
    // Level 1: Grid group (all threads in grid)
    cg::grid_group grid = cg::this_grid();

    // Level 2: Thread block (traditional block)
    cg::thread_block block = cg::this_thread_block();

    // Level 3: Warp-sized tile (32 threads)
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    // Level 4: Custom tile size (e.g., 4, 8, 16 threads)
    cg::thread_block_tile<4> tile4 = cg::tiled_partition<4>(block);

    // Level 5: Coalesced threads (currently active threads in warp)
    cg::coalesced_group active = cg::coalesced_threads();
}
```

**Synchronization Scope:**
| Group Type | Scope | Sync Cost | Use Case |
|------------|-------|-----------|----------|
| `grid_group` | Entire grid | High | Multi-block algorithms |
| `thread_block` | One block | Medium | Block-level operations |
| `thread_block_tile<32>` | One warp | Zero | Warp intrinsics |
| `thread_block_tile<N>` | N threads | Zero | Sub-warp operations |
| `coalesced_group` | Active threads | Zero | Divergent code |

### **23.11.3 Reduction with Cooperative Groups**

**Improvement over Module 25:** No dynamic kernel launches, better warp utilization.

#### **A. Thread Block Reduction**
```cuda
template<int BLOCK_SIZE>
__global__ void reduction_cg_thread_block(const float* input,
                                           float* output,
                                           int n) {
    cg::thread_block block = cg::this_thread_block();
    __shared__ float sdata[BLOCK_SIZE];

    int tid = block.thread_rank();  // Thread index in block
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    // Load with vectorization
    float sum = 0.0f;
    if (gid < n) sum += input[gid];
    if (gid + BLOCK_SIZE < n) sum += input[gid + BLOCK_SIZE];

    sdata[tid] = sum;
    block.sync();  // Explicit synchronization

    // Reduction loop
    for (int s = BLOCK_SIZE / 2; s > 32; s >>= 1) {
        if (tid < s) sdata[tid] += sdata[tid + s];
        block.sync();
    }

    // Warp reduction (no sync needed)
    if (tid < 32) {
        cg::coalesced_group warp = cg::coalesced_threads();
        for (int s = 16; s > 0; s >>= 1) {
            if (tid < s) sdata[tid] += sdata[tid + s];
            warp.sync();
        }
    }

    if (tid == 0) output[blockIdx.x] = sdata[0];
}
```

**Source:** `src/kernels/cooperative_groups_reduction.cu:32-76`

#### **B. Warp-Level Reduction with Shuffles**

Using shuffle intrinsics eliminates shared memory and bank conflicts:

```cuda
__device__ float warp_reduce_shuffle(cg::thread_block_tile<32> warp, float val) {
    // Warp-level reduction using shuffle - NO shared memory!
    for (int offset = 16; offset > 0; offset >>= 1) {
        val += warp.shfl_down(val, offset);  // Get value from lane + offset
    }
    return val;
}

template<int BLOCK_SIZE>
__global__ void reduction_cg_tiled(const float* input, float* output, int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;
    float value = (gid < n) ? input[gid] : 0.0f;

    // Warp-level reduction (register-based, fastest!)
    float warp_sum = warp_reduce_shuffle(warp, value);

    // Inter-warp reduction via shared memory
    __shared__ float warp_results[BLOCK_SIZE / 32];

    if (warp.thread_rank() == 0) {
        warp_results[warp.meta_group_rank()] = warp_sum;
    }
    block.sync();

    // First warp reduces warp results
    if (threadIdx.x < BLOCK_SIZE / 32) {
        warp_sum = warp_reduce_shuffle(warp, warp_results[threadIdx.x]);
        if (threadIdx.x == 0) output[blockIdx.x] = warp_sum;
    }
}
```

**Performance:** 2-3x faster than shared memory reduction (no bank conflicts, register-based)

**Source:** `src/kernels/cooperative_groups_reduction.cu:89-140`

#### **C. Grid-Wide Reduction (Single Kernel!)**

Replaces Module 25's recursive dynamic parallelism with single-kernel grid sync:

```cuda
template<int BLOCK_SIZE>
__global__ void reduction_cg_grid(float* data, float* temp, int n) {
    cg::grid_group grid = cg::this_grid();  // ALL blocks in grid
    cg::thread_block block = cg::this_thread_block();

    __shared__ float sdata[BLOCK_SIZE];
    int tid = threadIdx.x;
    int gid = grid.thread_rank();  // Global thread ID across grid

    // Load and reduce (grid-stride loop)
    float sum = 0.0f;
    for (int i = gid; i < n; i += grid.size()) {
        sum += data[i];
    }

    // Block-level reduction
    sdata[tid] = sum;
    block.sync();

    for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
        if (tid < s) sdata[tid] += sdata[tid + s];
        block.sync();
    }

    if (tid == 0) temp[blockIdx.x] = sdata[0];

    // Grid-wide sync - ALL blocks wait here!
    grid.sync();

    // First block does final reduction (no recursion needed!)
    if (blockIdx.x == 0) {
        sum = (tid < gridDim.x) ? temp[tid] : 0.0f;
        sdata[tid] = sum;
        block.sync();

        for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
            if (tid < s) sdata[tid] += sdata[tid + s];
            block.sync();
        }

        if (tid == 0) data[0] = sdata[0];  // Final result
    }
}
```

**Requirements:**
- Launch with `cudaLaunchCooperativeKernel()` instead of `<<<>>>`
- Device must support `cooperativeLaunch` (check `cudaDeviceProp`)

**Launch Example:**
```cuda
// Check device support
cudaDeviceProp props;
cudaGetDeviceProperties(&props, 0);
if (!props.cooperativeLaunch) {
    printf("Device does not support cooperative launch\n");
    return;
}

// Get maximum blocks for cooperative launch
int num_blocks, block_size = 256;
cudaOccupancyMaxActiveBlocksPerMultiprocessor(
    &num_blocks, reduction_cg_grid<256>, block_size, 0);
num_blocks *= props.multiProcessorCount;

// Launch cooperatively
void* kernel_args[] = {&d_data, &d_temp, &n};
cudaLaunchCooperativeKernel(
    (void*)reduction_cg_grid<256>,
    num_blocks, block_size, kernel_args);
```

**Advantage over Module 25:** No recursive kernel launches, single GPU kernel, ~100x lower overhead.

**Source:** `src/kernels/cooperative_groups_reduction.cu:196-254`

### **23.11.4 Histogram with Warp Aggregation**

**Improvement over Module 25:** Warp-level aggregation dramatically reduces atomic contention.

```cuda
template<int BLOCK_SIZE, int NUM_BINS>
__global__ void histogram_cg_warp_aggregated(const int* data,
                                               int* histogram,
                                               int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ int smem_hist[NUM_BINS];

    // Initialize shared histogram
    for (int i = threadIdx.x; i < NUM_BINS; i += BLOCK_SIZE) {
        smem_hist[i] = 0;
    }
    block.sync();

    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    if (gid < n) {
        int value = data[gid];
        int bin = value % NUM_BINS;

        // Warp aggregation: Count threads targeting each bin
        for (int i = 0; i < NUM_BINS; i++) {
            // Ballot: Get mask of threads in warp targeting bin i
            unsigned int mask = warp.ballot(bin == i);
            int leader = __ffs(mask) - 1;  // First thread in mask

            if (mask != 0) {
                int count = __popc(mask);  // Population count

                // Leader does ONE atomic instead of many!
                if (warp.thread_rank() == leader) {
                    atomicAdd(&smem_hist[i], count);
                }
            }
        }
    }

    block.sync();

    // Merge to global
    for (int i = threadIdx.x; i < NUM_BINS; i += BLOCK_SIZE) {
        if (smem_hist[i] > 0) {
            atomicAdd(&histogram[i], smem_hist[i]);
        }
    }
}
```

**Performance Improvement:** 5-10x fewer atomic operations vs naive histogram.

**How it works:**
1. `warp.ballot(bin == i)` creates bitmask of threads targeting bin `i`
2. `__popc(mask)` counts threads (population count)
3. Leader thread performs single atomic with total count
4. Instead of 32 atomics, only 1 atomic per bin per warp!

**Source:** `src/kernels/cooperative_groups_patterns.cu:60-105`

### **23.11.5 Prefix Sum (Scan) with Shuffles**

Warp-level scan using shuffle intrinsics:

```cuda
__device__ float warp_scan_inclusive(cg::thread_block_tile<32> warp, float val) {
    // Inclusive scan using shuffle
    for (int offset = 1; offset < warp.size(); offset *= 2) {
        float other = warp.shfl_up(val, offset);  // Get from lane - offset
        if (warp.thread_rank() >= offset) {
            val += other;
        }
    }
    return val;
}

template<int BLOCK_SIZE>
__global__ void scan_cg_inclusive(const float* input,
                                   float* output,
                                   int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    float value = (gid < n) ? input[gid] : 0.0f;

    // Level 1: Warp-level scan
    float warp_scan = warp_scan_inclusive(warp, value);

    // Level 2: Scan warp totals
    __shared__ float warp_totals[BLOCK_SIZE / 32];

    if (warp.thread_rank() == 31) {  // Last thread of warp
        warp_totals[warp.meta_group_rank()] = warp_scan;
    }
    block.sync();

    // First warp scans the warp totals
    if (tid < BLOCK_SIZE / 32) {
        float total = warp_totals[tid];
        total = warp_scan_inclusive(warp, total);
        warp_totals[tid] = total;
    }
    block.sync();

    // Add preceding warp totals
    if (warp.meta_group_rank() > 0) {
        warp_scan += warp_totals[warp.meta_group_rank() - 1];
    }

    if (gid < n) output[gid] = warp_scan;
}
```

**Advantage:** No shared memory bank conflicts, uses register shuffles.

**Source:** `src/kernels/cooperative_groups_patterns.cu:183-243`

### **23.11.6 Bitonic Sort (Replaces Quicksort)**

Cooperative groups enable efficient data-parallel sorting without recursion:

```cuda
template<int BLOCK_SIZE>
__global__ void bitonic_sort_cg(int* data, int n) {
    cg::thread_block block = cg::this_thread_block();

    __shared__ int sdata[BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    sdata[tid] = (gid < n) ? data[gid] : INT_MAX;
    block.sync();

    // Bitonic sort pattern
    for (int k = 2; k <= BLOCK_SIZE; k *= 2) {
        for (int j = k / 2; j > 0; j /= 2) {
            int ixj = tid ^ j;  // XOR for swap partner

            if (ixj > tid) {
                bool ascending = ((tid & k) == 0);

                if ((sdata[tid] > sdata[ixj]) == ascending) {
                    // Swap
                    int temp = sdata[tid];
                    sdata[tid] = sdata[ixj];
                    sdata[ixj] = temp;
                }
            }

            block.sync();
        }
    }

    if (gid < n) data[gid] = sdata[tid];
}
```

**Advantage over Module 25 Quicksort:** No recursion, data-parallel, predictable performance.

**Source:** `src/kernels/cooperative_groups_patterns.cu:28-70`

### **23.11.7 Performance Comparison**

| Algorithm | Module 25 (Dynamic) | Module 23 (Coop Groups) | Speedup |
|-----------|-------------------|------------------------|---------|
| **Reduction** | Recursive launches | Grid-wide sync | 100x (lower overhead) |
| **Histogram** | Naive atomics | Warp aggregation | 5-10x (fewer atomics) |
| **Scan** | Multi-kernel | Single-kernel shuffle | 3-5x (no shared mem) |
| **Sort** | Recursive quicksort | Bitonic sort | 2-4x (data-parallel) |

### **23.11.8 When to Use Cooperative Groups**

**Use Cooperative Groups When:**
- ✅ Need warp-level primitives (shuffle, ballot, vote)
- ✅ Implementing reductions, scans, or collectives
- ✅ Reducing atomic contention (warp aggregation)
- ✅ Need grid-wide synchronization in single kernel
- ✅ Writing composable, reusable device code

**Use Dynamic Parallelism When:**
- ✅ Truly irregular/recursive algorithms (tree traversal)
- ✅ Work cannot be determined ahead of time
- ✅ Launch overhead is negligible vs computation
- ✅ Need different kernel configurations dynamically

### **23.11.9 Testing Cooperative Groups**

**Test Coverage:**
All cooperative groups kernels have comprehensive tests in `test/unit/kernels/test_cooperative_groups.cu`:

- ✅ Thread block reduction correctness
- ✅ Tiled (shuffle-based) reduction performance
- ✅ Grid-wide reduction with cooperative launch
- ✅ Segmented reduction with labeled partitions
- ✅ Warp-aggregated histogram
- ✅ Inclusive/exclusive scan (prefix sum)
- ✅ Bitonic sort correctness
- ✅ Matrix operations (transpose, multiply)

**Build and Run:**
```bash
# Build Module 23 with cooperative groups
ninja -C build 23_Shared_Memory_test

# Run cooperative groups tests
./build/20.cuda_intermediate/23.Shared_Memory/test/23_Shared_Memory_test \
    --gtest_filter="CooperativeGroups*"

# Profile with nsys
ninja -C build run_nsys_23_Shared_Memory_test
```

---

## **23.12 Exercises**

1. **Implement 2D convolution** using shared memory tiling
2. **Optimize histogram computation** with shared memory atomics
3. **Create a prefix sum (scan)** algorithm using shared memory
4. **Implement bitonic sort** in shared memory
5. **Profile and eliminate bank conflicts** in provided kernels
6. **NEW: Convert Module 25 quicksort** to cooperative groups bitonic sort
7. **NEW: Implement warp-aggregated atomic max** for finding maximum value
8. **NEW: Create grid-wide barrier** using cooperative groups for multi-block synchronization

---

## ✅ **Summary**

### **Key Takeaways**
1. **Shared Memory Speed**: 100x faster than global memory (~1-30 cycles vs ~400 cycles latency)
2. **User-Controlled Caching**: Programmable cache for explicit data reuse within thread blocks
3. **Bank Conflicts**: Main performance bottleneck when multiple threads access same bank simultaneously
4. **Synchronization Required**: Always use `__syncthreads()` after writing before reading shared memory
5. **Tiling Pattern**: Essential for matrix operations - reduces global memory accesses by reusing data
6. **Padding Technique**: Add extra column to 2D shared arrays to avoid bank conflicts
7. **Cooperative Groups (NEW)**: Enables warp-level primitives, grid-wide sync, and flexible thread group management
8. **Warp Shuffle (NEW)**: 2-3x faster than shared memory for reductions - zero bank conflicts, register-based
9. **Warp Aggregation (NEW)**: 5-10x reduction in atomic contention for histograms and collectives

### **Performance Metrics**

| Pattern | Speedup over Global Memory | Typical Efficiency | Bank Conflicts |
|---------|----------------------------|-------------------|----------------|
| Matrix Multiplication (Tiled) | 10-20x | 85-95% | Low |
| Matrix Transpose (Naive) | 3-5x | 40-60% | High |
| Matrix Transpose (Padded) | 8-12x | 80-90% | None |
| Parallel Reduction (Shared Mem) | 5-8x | 70-85% | Manageable |
| Parallel Reduction (Coop Groups) | 12-20x | 90-95% | **None** |
| Histogram (Naive Atomic) | 2-4x | 30-50% | N/A |
| Histogram (Warp Aggregated) | 15-30x | 80-90% | N/A |
| Scan/Prefix Sum (Shuffle) | 10-15x | 85-92% | **None** |
| 1D Stencil | 4-7x | 75-90% | Low |
| 2D Convolution | 6-10x | 70-85% | Medium |

**Shared Memory Limits (Modern GPUs):**
- Per block: 48-96 KB
- Per SM: 96-164 KB
- Banks: 32 (4-byte wide)
- Bandwidth: ~10 TB/s

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| **Bank conflicts** | Multiple threads access same bank | Add padding (+1 column) or permute indices |
| **Race conditions** | Missing synchronization | Add `__syncthreads()` after all writes complete |
| **Launch failure** | Exceeds shared memory limit | Reduce tile size or use dynamic allocation |
| **Low occupancy** | Too much shared memory per block | Balance shared memory vs thread count |
| **Incorrect results** | `__syncthreads()` in divergent code | Ensure all threads reach synchronization point |
| **Poor performance** | Uncoalesced global memory access | Load contiguous data into shared memory |

### **Optimization Checklist**
1. ✅ Profile with `ncu --metrics shared_efficiency`
2. ✅ Check for bank conflicts (ideal: 0 conflicts)
3. ✅ Verify occupancy (target: 50%+ for memory-bound kernels)
4. ✅ Use padding for 2D arrays
5. ✅ Minimize `__syncthreads()` calls (but don't eliminate needed ones)
6. ✅ Consider double buffering for pipelined operations

### **Next Steps**
- 📚 Continue to Part 24: Advanced Memory Optimization
- 🔧 Implement exercises in section 23.11 (2D convolution, histogram, prefix sum)
- 📊 Profile your code with Nsight Compute: `ninja -C build 23_Shared_Memory_test_ncu`
- 🎯 Experiment with different tile sizes (8x8, 16x16, 32x32)
- 🔍 Study the transpose demo for bank conflict visualization

---

## **23.13 References**

**Shared Memory:**
- [CUDA C++ Programming Guide - Shared Memory](https://docs.nvidia.com/cuda/cuda-c-programming-guide/#shared-memory)
- [CUDA C++ Best Practices - Shared Memory](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/#shared-memory)
- [Using Shared Memory in CUDA](https://developer.nvidia.com/blog/using-shared-memory-cuda-cc/)
- [Optimizing Matrix Transpose in CUDA](https://developer.nvidia.com/blog/efficient-matrix-transpose-cuda-cc/)

**Cooperative Groups (NEW):**
- [CUDA Cooperative Groups Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/#cooperative-groups)
- [Cooperative Groups API Documentation](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#cooperative-groups)
- [Using Cooperative Groups in CUDA](https://developer.nvidia.com/blog/cooperative-groups/)
- [Warp-Level Primitives](https://docs.nvidia.com/cuda/cuda-c-programming-guide/#warp-shuffle-functions)

**Related Modules:**
- Module 25: Dynamic Parallelism (foundation for cooperative groups enhancements)
- Module 24: Memory Coalescing and Bank Conflicts
- Module 22: Streams and Async Operations

---

📄 **Next**: [Part 24: Advanced Memory Optimization](../24.Advanced_Memory_Optimization/README.md)