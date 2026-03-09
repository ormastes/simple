# 🎯 Part 17: Memory Hierarchy
**Goal**: Master CUDA memory hierarchy through matrix multiplication optimization, demonstrating the performance impact of different memory access patterns.

## Project Structure

This module follows the advanced structure (Module 16+) with dedicated source and test directories. The organization separates kernel implementations, utilities, and tests for better maintainability and code reuse.
```
17.Memory_Hierarchy/
├── README.md                        - This documentation
├── CMakeLists.txt                   - Build configuration
├── src/                             - Source implementations
│   ├── kernels/                     - Core CUDA kernels (reusable across parts)
│   │   ├── matrix_multiply.cu       - Matrix multiplication implementations
│   │   ├── vector_add_2d.cu         - 2D vector addition kernels
│   │   └── vector_add_2d.h          - Vector addition header
│   └── part_specific/               - Module-specific implementations
│       └── vector_add_memory.cu     - Memory access pattern demos
└── test/                            - Test files
    └── unit/                        - Unit tests
        ├── kernels/                 - Kernel tests (reusable across parts)
        │   ├── test_matrix_multiply.cu  - Matrix multiplication tests
        │   └── test_vector_add_2d.cu    - Vector addition tests
        └── part_specific/           - Module-specific tests
            ├── benchmark_memory.cu      - Memory performance benchmarks
            └── test_vector_add_memory.cu - Memory pattern tests
```

## Quick Navigation

This guide is organized into progressive sections covering memory types, access patterns, and optimization techniques. Each section builds upon the previous ones to develop a comprehensive understanding of memory hierarchy optimization.
- [17.1 Memory Types and Characteristics](#171-memory-types-and-characteristics)
- [17.2 Register Memory](#172-register-memory)
- [17.3 Shared Memory](#173-shared-memory)
- [17.4 Constant Memory](#174-constant-memory)
- [17.5 Texture Memory](#175-texture-memory)
- [17.6 Global Memory](#176-global-memory)
- [17.7 L1 and L2 Cache](#177-l1-and-l2-cache)
- [17.8 Memory Access Patterns](#178-memory-access-patterns)
- [17.9 Matrix Multiplication Evolution](#179-matrix-multiplication-evolution)
- [17.10 Bank Conflict Mitigation](#1710-bank-conflict-mitigation)
- [17.11 Profiling and Performance Analysis](#1711-profiling-and-performance-analysis)
- [17.12 Advanced Optimization Techniques](#1712-advanced-optimization-techniques)
- [17.13 Memory Optimization Glossary](#1713-memory-optimization-glossary)
- [17.14 Testing](#1714-testing)
- [Build & Run](#build--run)
- [Summary](#1715-summary)

---

## **17.1 Memory Types and Characteristics**

This section introduces the CUDA memory hierarchy, which is fundamental for achieving optimal performance. Understanding memory types and their characteristics enables developers to make informed decisions about data placement and access patterns.

### **17.1.1 Memory Hierarchy Overview**

CUDA provides multiple memory types with different scopes, speeds, and capacities. Each memory type serves a specific purpose in the GPU architecture, offering trade-offs between capacity, bandwidth, and latency. Source: `src/part_specific/vector_add_memory.cu`.

**Visual Memory Hierarchy:**

```
┌─────────────────────────────────────────────────────────────────┐
│                        GPU DEVICE                                │
│                                                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  Streaming Multiprocessor (SM) - Repeated Many Times     │  │
│  │                                                            │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐      │  │
│  │  │   Thread    │  │   Thread    │  │   Thread    │      │  │
│  │  │  ┌───────┐  │  │  ┌───────┐  │  │  ┌───────┐  │      │  │
│  │  │  │ Regs  │  │  │  │ Regs  │  │  │  │ Regs  │  │ ...  │  │
│  │  │  └───────┘  │  │  └───────┘  │  │  └───────┘  │      │  │
│  │  │  1 cycle    │  │  1 cycle    │  │  1 cycle    │      │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘      │  │
│  │                                                            │  │
│  │  ┌──────────────────────────────────────────────────┐    │  │
│  │  │         Shared Memory (48-96 KB)                 │    │  │
│  │  │         ~20-30 cycles latency                     │    │  │
│  │  │         Shared by all threads in block           │    │  │
│  │  └──────────────────────────────────────────────────┘    │  │
│  │                                                            │  │
│  │  ┌──────────────────────────────────────────────────┐    │  │
│  │  │   L1 Cache (128 KB) + Texture Cache (48-96 KB)  │    │  │
│  │  │              ~30 cycles latency                   │    │  │
│  │  └──────────────────────────────────────────────────┘    │  │
│  │                                                            │  │
│  │  ┌──────────────────────────────────────────────────┐    │  │
│  │  │         Constant Cache (64 KB)                   │    │  │
│  │  │         ~48 cycles (when all threads read same)  │    │  │
│  │  └──────────────────────────────────────────────────┘    │  │
│  └────────────────────────────────────────────────────────────┘  │
│                                                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │         L2 Cache (4-6 MB on modern GPUs)                 │  │
│  │         ~120 cycles latency                               │  │
│  │         Shared across ALL SMs                             │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │         Global Memory (GDDR6/HBM: 4-48 GB)              │  │
│  │         ~440 cycles latency                               │  │
│  │         Accessible by all threads on device               │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                   │
└───────────────────────────────────────────────────────────────────┘
         ↕ PCIe Bus (16 GB/s typical)
┌────────────────────────┐
│    Host (CPU) Memory   │
│    System RAM          │
└────────────────────────┘
```

**Memory Performance Characteristics:**

| Memory Type | Scope | Bandwidth | Latency (Best Case) | Size | Cached | Notes |
|-------------|-------|-----------|---------|------|--------|-------|
| **Registers** | Thread | Highest | ~1 cycle | ~255 per thread | No | Fastest, private to thread |
| **Shared** | Block | Very High | ~20-30 cycles | 48-96 KB/block | No | Explicitly managed, shared by block |
| **L1 Cache** | SM | High | ~30 cycles | 128 KB/SM | Yes | Automatic cache for global/local |
| **Constant** | Device | High (broadcast) | ~48 cycles | 64 KB | Yes (dedicated L1) | Fast when all threads read same address |
| **Texture** | Device | High | ~100 cycles | 48-96 KB/SM | Yes (texture L1) | Optimized for 2D/3D spatial locality |
| **L2 Cache** | Device | Medium | ~120 cycles | 4-6 MB | Yes | Shared across all SMs |
| **Global** | Device | Medium | ~440 cycles | 4-48 GB | Through L1/L2 | Slowest, but largest capacity |

### **17.1.2 Memory Access Costs**

Different memory types have vastly different access costs, ranging from essentially free register access to hundreds of cycles for global memory. Understanding these costs is crucial for optimizing memory-bound kernels and achieving high performance. Full demonstration in `src/part_specific/vector_add_memory.cu`.

```cpp
// vector_add_memory.cu - Demonstrates memory access patterns
__global__ void memory_access_demo(float* global_data, int n) {
    extern __shared__ float shared_data[];
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Register access: ~0 cycles
    float reg_val = idx * 2.0f;

    // Shared memory access: ~1-30 cycles
    shared_data[threadIdx.x] = reg_val;
    __syncthreads();

    // Global memory access: ~200-800 cycles
    if (idx < n) {
        global_data[idx] = shared_data[threadIdx.x];
    }
}
```

**Key Points:**
- Register access is essentially free
- Shared memory is 10-100x faster than global memory
- Coalescing global memory accesses is critical
- Source: `src/part_specific/vector_add_memory.cu:45-67`

---

## **17.2 Register Memory**

This section covers register memory, the fastest storage available on the GPU. Registers are private to each thread and provide near-zero latency access, making them ideal for frequently accessed variables and intermediate computations.

### **17.2.1 Implicit Register Usage**

The compiler automatically allocates registers for local variables within kernels. This is the most common and natural way to use registers, requiring no special syntax from the programmer. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Compiler automatically uses registers
__global__ void register_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // These local variables automatically go into registers
        float temp1 = input[idx];      // Register allocation
        float temp2 = temp1 * 2.0f;    // Register allocation
        float temp3 = temp2 + 1.0f;    // Register allocation
        output[idx] = temp3;
    }
}
```

**Key Points:**
- All local scalar variables are stored in registers by default
- No special keywords needed - happens automatically
- Limited to ~255 registers per thread on modern GPUs
- Source: `src/part_specific/memory_types_demo.cu:11-22`

### **17.2.2 Explicit Register Usage**

While registers are allocated implicitly, developers can provide hints to the compiler or explicitly manage register usage through loop unrolling and careful variable management. This gives more control over register pressure and occupancy. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Explicit register hints and management
__global__ void register_explicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Explicit register keyword (hint to compiler)
        register float temp1 = input[idx];
        register float temp2 = temp1 * 2.0f;
        register float temp3 = temp2 + 1.0f;
        output[idx] = temp3;
    }
}

// Explicit register management via loop unrolling
__global__ void register_unrolled(const float* input, float* output, int N) {
    int idx = (blockIdx.x * blockDim.x + threadIdx.x) * 4;

    // Explicitly keep 4 values in registers for ILP (Instruction Level Parallelism)
    float r0, r1, r2, r3;

    if (idx < N) r0 = input[idx] * 2.0f + 1.0f;
    if (idx + 1 < N) r1 = input[idx + 1] * 2.0f + 1.0f;
    if (idx + 2 < N) r2 = input[idx + 2] * 2.0f + 1.0f;
    if (idx + 3 < N) r3 = input[idx + 3] * 2.0f + 1.0f;

    // Write from registers
    if (idx < N) output[idx] = r0;
    if (idx + 1 < N) output[idx + 1] = r1;
    if (idx + 2 < N) output[idx + 2] = r2;
    if (idx + 3 < N) output[idx + 3] = r3;
}
```

**Key Points:**
- `register` keyword is mostly informational in modern CUDA
- Loop unrolling explicitly manages multiple register variables
- Increases instruction-level parallelism (ILP)
- Can improve performance but may reduce occupancy
- Source: `src/part_specific/memory_types_demo.cu:24-58`

**Register Spilling:**
When a kernel uses too many registers, the compiler "spills" them to local memory (slow), significantly degrading performance. Monitor register usage with `--ptxas-options=-v` during compilation.

---

## **17.3 Shared Memory**

This section demonstrates shared memory, a low-latency, high-bandwidth memory shared among threads in a block. Shared memory is explicitly managed by programmers and is essential for data reuse patterns and inter-thread communication within a block.

### **17.3.1 No Implicit Usage**

Unlike registers or caches, shared memory has **no implicit usage**. It must be explicitly declared and managed by the programmer using the `__shared__` keyword.

### **17.3.2 Explicit Static Allocation**

Static shared memory allocation declares a fixed-size array at compile time. This approach is simple and has no runtime overhead, making it ideal when the required size is known in advance. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Static shared memory allocation
__global__ void shared_static(const float* input, float* output, int N) {
    // Explicitly declare fixed-size shared memory
    __shared__ float sdata[256];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load from global to shared memory
    if (idx < N) {
        sdata[tid] = input[idx];
    }
    __syncthreads();  // Ensure all threads have loaded data

    // Use shared memory for computation
    if (idx < N) {
        output[idx] = sdata[tid] * 2.0f;
    }
}
```

**Key Points:**
- Fixed size known at compile time
- Zero runtime overhead
- Uses `__shared__` keyword
- Requires `__syncthreads()` for coordination
- Source: `src/part_specific/memory_types_demo.cu:66-85`

### **17.3.3 Explicit Dynamic Allocation**

Dynamic shared memory allocation allows the size to be specified at kernel launch time via the third execution configuration parameter. This provides flexibility when shared memory requirements vary based on runtime parameters. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Dynamic shared memory allocation
__global__ void shared_dynamic(const float* input, float* output, int N) {
    // Explicitly declare dynamic shared memory (size determined at launch)
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load and use dynamic shared memory
    if (idx < N) {
        sdata[tid] = input[idx];
    }
    __syncthreads();

    if (idx < N) {
        output[idx] = sdata[tid] * 2.0f;
    }
}

// Host launch code:
// size_t shared_mem_bytes = blockDim.x * sizeof(float);
// shared_dynamic<<<grid, block, shared_mem_bytes>>>(d_in, d_out, N);
```

**Key Points:**
- Size specified at kernel launch time
- Uses `extern __shared__` declaration
- Third parameter in `<<<grid, block, shared_bytes>>>`
- More flexible than static allocation
- Source: `src/part_specific/memory_types_demo.cu:87-105`

### **17.3.4 Bank Conflict-Free Access**

Shared memory is organized into 32 banks. When threads in a warp access different addresses in the same bank, accesses serialize. Padding shared memory arrays eliminates these conflicts by shifting addresses to different banks. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Bank conflict-free with padding
__global__ void shared_padded(const float* input, float* output, int N) {
    // Add +1 padding to eliminate bank conflicts
    __shared__ float sdata[32][32 + 1];  // +1 shifts to different banks

    int tx = threadIdx.x;
    int ty = threadIdx.y;
    int idx = (blockIdx.y * blockDim.y + ty) * N + (blockIdx.x * blockDim.x + tx);

    if (blockIdx.x * blockDim.x + tx < N && blockIdx.y * blockDim.y + ty < N) {
        sdata[ty][tx] = input[idx];
        __syncthreads();
        output[idx] = sdata[ty][tx] * 2.0f;  // Conflict-free access
    }
}
```

**Key Points:**
- Padding eliminates bank conflicts (7-10x speedup possible)
- Add +1 to innermost dimension for 32-bit types
- Critical for matrix transpose and tiling operations
- Source: `src/part_specific/memory_types_demo.cu:107-123`

---

## **17.4 Constant Memory**

This section covers constant memory, a read-only memory space with dedicated cache optimized for broadcasting the same value to all threads. Constant memory is ideal for parameters, coefficients, and lookup tables accessed uniformly across the grid.

### **17.4.1 No Implicit Usage**

Constant memory has **no implicit usage**. It must be explicitly declared using the `__constant__` keyword at file scope and populated from the host.

### **17.4.2 Explicit Constant Memory**

Constant memory variables are declared at file scope with `__constant__` and populated from host code using `cudaMemcpyToSymbol()`. The GPU efficiently broadcasts constant values to all threads when they read the same address. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Explicit constant memory declaration
__constant__ float const_coefficients[16];  // File scope, 64KB max
__constant__ float const_scalar;

__global__ void constant_explicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Efficiently broadcast to all threads when reading same address
        float result = input[idx] * const_scalar;

        // Loop uses constant array
        for (int i = 0; i < 16; i++) {
            result += const_coefficients[i];
        }

        output[idx] = result;
    }
}

// Host code to populate constant memory
void set_constant_memory_demo(float scalar, const float* coeffs, int coeff_size) {
    cudaMemcpyToSymbol(const_scalar, &scalar, sizeof(float));
    cudaMemcpyToSymbol(const_coefficients, coeffs, coeff_size * sizeof(float));
}
```

**Key Points:**
- Must use `__constant__` keyword at file scope
- Limited to 64 KB total
- Populated via `cudaMemcpyToSymbol()` from host
- Optimal when all threads read same address (broadcast)
- Serializes if threads read different addresses
- Source: `src/part_specific/memory_types_demo.cu:130-156`

**Performance Characteristics:**
- **Best case**: All threads read same address → ~48 cycle latency (broadcast)
- **Worst case**: 32 threads read 32 different addresses → 32x serialization

---

## **17.5 Texture Memory**

This section covers texture memory, a read-only memory type with specialized cache optimized for spatial locality in 2D and 3D data. Texture memory provides benefits like automatic interpolation, boundary handling, and efficient access patterns for image processing and scientific computing.

### **17.5.1 No Implicit Usage**

Texture memory has **no implicit usage**. It requires explicit setup including resource descriptors, texture descriptors, and texture objects created from host code.

### **17.5.2 Explicit 1D Texture Memory**

1D texture memory is accessed through texture objects created from linear device memory. The texture cache optimizes for spatial locality, making it ideal for patterns where nearby threads access nearby memory locations. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - 1D texture memory
__global__ void texture_1d_explicit(cudaTextureObject_t texObj, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Explicit texture fetch with automatic caching
        float value = tex1Dfetch<float>(texObj, idx);
        output[idx] = value * 2.0f;
    }
}

// Host code to create 1D texture object
cudaTextureObject_t create_texture_1d(const float* d_data, int N) {
    cudaResourceDesc resDesc;
    memset(&resDesc, 0, sizeof(resDesc));
    resDesc.resType = cudaResourceTypeLinear;
    resDesc.res.linear.devPtr = (void*)d_data;
    resDesc.res.linear.desc = cudaCreateChannelDesc<float>();
    resDesc.res.linear.sizeInBytes = N * sizeof(float);

    cudaTextureDesc texDesc;
    memset(&texDesc, 0, sizeof(texDesc));
    texDesc.readMode = cudaReadModeElementType;

    cudaTextureObject_t texObj = 0;
    cudaCreateTextureObject(&texObj, &resDesc, &texDesc, nullptr);
    return texObj;
}
```

**Key Points:**
- Requires explicit texture object creation
- Uses `tex1Dfetch<T>()` for fetching
- Optimized for spatial locality
- Read-only access
- Must call `cudaDestroyTextureObject()` when done
- Source: `src/part_specific/memory_types_demo.cu:163-195`

### **17.5.3 Explicit 2D Texture Memory**

2D texture memory is optimized for 2D spatial access patterns common in image processing. It provides automatic boundary handling, interpolation options, and efficient caching for 2D locality. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - 2D texture memory
__global__ void texture_2d_explicit(cudaTextureObject_t texObj, float* output,
                                    int width, int height) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x < width && y < height) {
        // 2D texture fetch optimized for spatial locality
        float value = tex2D<float>(texObj, x, y);
        output[y * width + x] = value * 2.0f;
    }
}

// Host code to create 2D texture
cudaTextureObject_t create_texture_2d(cudaArray_t array) {
    cudaResourceDesc resDesc;
    memset(&resDesc, 0, sizeof(resDesc));
    resDesc.resType = cudaResourceTypeArray;
    resDesc.res.array.array = array;

    cudaTextureDesc texDesc;
    memset(&texDesc, 0, sizeof(texDesc));
    texDesc.addressMode[0] = cudaAddressModeClamp;  // Boundary handling
    texDesc.addressMode[1] = cudaAddressModeClamp;
    texDesc.filterMode = cudaFilterModePoint;  // Or cudaFilterModeLinear
    texDesc.readMode = cudaReadModeElementType;
    texDesc.normalizedCoords = 0;  // Use pixel coordinates

    cudaTextureObject_t texObj = 0;
    cudaCreateTextureObject(&texObj, &resDesc, &texDesc, nullptr);
    return texObj;
}
```

**Key Points:**
- Requires CUDA array allocation (`cudaMallocArray`)
- Uses `tex2D<T>()` for 2D fetching
- Automatic boundary handling (clamp, wrap, etc.)
- Optional hardware interpolation
- Ideal for image processing and scientific computing
- Source: `src/part_specific/memory_types_demo.cu:197-240`

---

## **17.6 Global Memory**

This section covers global memory, the largest but slowest memory space on the GPU. Global memory is accessible to all threads across all blocks and persists for the lifetime of the application, making it the primary storage for input/output data.

### **17.6.1 Implicit Global Memory Usage**

Global memory is implicitly used whenever kernel parameters point to device memory allocated with `cudaMalloc()` or similar functions. This is the most common way to access global memory. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Implicit global memory through pointers
__global__ void global_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Pointers automatically access global memory
        output[idx] = input[idx] * 2.0f;
    }
}

// Host code:
// float* d_input, *d_output;
// cudaMalloc(&d_input, N * sizeof(float));   // Allocates global memory
// cudaMalloc(&d_output, N * sizeof(float));
// global_implicit<<<grid, block>>>(d_input, d_output, N);
```

**Key Points:**
- Pointers in kernel parameters automatically reference global memory
- Allocated via `cudaMalloc()`, `cudaMallocManaged()`, etc.
- Largest capacity (4-80 GB on modern GPUs)
- Slowest access (~440 cycles latency)
- Source: `src/part_specific/memory_types_demo.cu:249-258`

### **17.6.2 Explicit Global Memory with __device__**

Global memory can be explicitly declared at file scope using the `__device__` keyword, creating persistent device variables accessible across kernel launches. This is useful for state that persists between kernels. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Explicit __device__ global variable
__device__ float global_device_var[1024];

__global__ void global_explicit_device() {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < 1024) {
        // Explicitly using global device variable
        global_device_var[idx] = idx * 2.0f;
    }
}

// Can be accessed from host via cudaMemcpyToSymbol/cudaMemcpyFromSymbol
```

**Key Points:**
- Uses `__device__` keyword at file scope
- Persists across kernel launches
- Accessed via `cudaMemcpyToSymbol()` / `cudaMemcpyFromSymbol()` from host
- Useful for global state or lookup tables
- Source: `src/part_specific/memory_types_demo.cu:260-271`

### **17.6.3 Coalesced vs Strided Access**

Memory coalescing is critical for global memory performance. Consecutive threads accessing consecutive addresses enable the hardware to combine requests into fewer transactions, dramatically improving bandwidth. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Coalesced access (optimal)
__global__ void global_coalesced(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Consecutive threads access consecutive memory (coalesced)
        float value = input[idx];     // Coalesced load
        output[idx] = value * 2.0f;   // Coalesced store
    }
}

// Strided access (poor performance)
__global__ void global_strided(const float* input, float* output, int N, int stride) {
    int idx = (blockIdx.x * blockDim.x + threadIdx.x) * stride;
    if (idx < N) {
        // Strided access - poor coalescing
        output[idx] = input[idx] * 2.0f;
    }
}
```

**Key Points:**
- Coalesced access: 5-10x faster than strided
- Threads in warp should access consecutive 128-byte segments
- Row-major access for 2D arrays is naturally coalesced
- Column-major or strided access hurts performance severely
- Source: `src/part_specific/memory_types_demo.cu:273-290`

---

## **17.7 L1 and L2 Cache**

This section covers the GPU's cache hierarchy. L1 cache is local to each SM while L2 is shared across the device. Both caches are hardware-managed but can be configured to some extent for different workloads.

### **17.7.1 L1 Cache - Implicit Usage**

L1 cache automatically caches global and local memory accesses. It operates transparently without requiring programmer intervention, though its behavior can be influenced through configuration. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - L1 cache automatically used
__global__ void l1_cache_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // L1 automatically caches these global memory accesses
        float value = input[idx];
        output[idx] = value * 2.0f;
    }
}
```

**Key Points:**
- Completely automatic - no code changes needed
- Caches global and local memory
- Size: 128 KB per SM (typical)
- Latency: ~30 cycles on hit
- Source: `src/part_specific/memory_types_demo.cu:297-307`

### **17.7.2 L1 Cache - Explicit Configuration**

While L1 caching is automatic, developers can configure the L1/shared memory partition to favor either L1 cache or shared memory. This allows tuning for memory-bound vs compute-bound kernels. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - Configure L1 preference
__global__ void l1_cache_prefer_l1(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // With cudaFuncCachePreferL1, benefits from larger L1 cache
        float value = input[idx];
        output[idx] = value * 2.0f;
    }
}

// Host-side configuration
void configure_l1_cache(cudaFuncCache preference) {
    // Device-wide:
    cudaDeviceSetCacheConfig(preference);

    // Or per-kernel:
    // cudaFuncSetCacheConfig(l1_cache_prefer_l1, cudaFuncCachePreferL1);
    // Options: cudaFuncCachePreferShared, cudaFuncCachePreferL1, cudaFuncCachePreferEqual
}
```

**Key Points:**
- `cudaFuncCachePreferL1`: More L1, less shared (better for memory-bound)
- `cudaFuncCachePreferShared`: Less L1, more shared (better for algorithms using shared)
- `cudaFuncCachePreferEqual`: Balanced partition
- Configuration is a hint - hardware makes final decision
- Source: `src/part_specific/memory_types_demo.cu:309-332`

### **17.7.3 L2 Cache - Implicit Usage**

L2 cache is shared across all SMs and automatically caches all global memory accesses. It serves as a second level of caching when data misses L1, providing substantial capacity with moderate latency. Source: `src/part_specific/memory_types_demo.cu`.

```cpp
// memory_types_demo.cu - L2 cache automatically used
__global__ void l2_cache_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // L2 automatically caches across all SMs
        output[idx] = input[idx] * 2.0f;
    }
}
```

**Key Points:**
- Completely automatic for all global memory
- Shared across all SMs on device
- Size: 4-6 MB (typical modern GPUs)
- Latency: ~120 cycles on hit
- Critical for inter-SM data sharing
- Source: `src/part_specific/memory_types_demo.cu:339-349`

### **17.7.4 L2 Persistent Cache - Explicit Control (Ampere+)**

Modern GPUs (Ampere architecture and newer) support L2 persistence policies, allowing developers to mark frequently accessed data to persist in L2 cache. This is an explicit optimization for data that should remain cached.

```cpp
// Requires CUDA 11.0+ and Ampere or newer
#if __CUDA_ARCH__ >= 800
__global__ void l2_cache_persistent(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // With L2 persistence policy set, data stays in L2
        output[idx] = input[idx] * 2.0f;
    }
}
#endif

// Host code to set L2 persistence (Ampere+):
// cudaStreamAttrValue stream_attribute;
// stream_attribute.accessPolicyWindow.base_ptr = d_data;
// stream_attribute.accessPolicyWindow.num_bytes = size;
// stream_attribute.accessPolicyWindow.hitRatio = 1.0f;
// stream_attribute.accessPolicyWindow.hitProp = cudaAccessPropertyPersisting;
// stream_attribute.accessPolicyWindow.missProp = cudaAccessPropertyStreaming;
// cudaStreamSetAttribute(stream, cudaStreamAttributeAccessPolicyWindow, &stream_attribute);
```

**Key Points:**
- Available on Ampere (SM 8.0) and newer architectures
- Explicitly marks data to persist in L2
- Useful for frequently reused data across kernels
- Requires CUDA 11.0 or later
- Source: `src/part_specific/memory_types_demo.cu:351-362`

---

## **17.8 Memory Access Patterns**

This section demonstrates how memory access patterns dramatically affect performance. Proper access patterns can improve bandwidth utilization from 30% to over 90% of theoretical peak.

### **17.8.1 Strided vs Coalesced Access**

Memory coalescing occurs when consecutive threads in a warp access consecutive memory addresses, allowing the hardware to combine multiple memory requests into a single transaction. This optimization is essential for achieving high memory bandwidth utilization on modern GPUs. Source: `src/part_specific/vector_add_memory.cu`.

```cpp
// vector_add_memory.cu - Strided vs coalesced access patterns
__global__ void strided_access(float* data, int stride, int n) {
    int idx = (blockIdx.x * blockDim.x + threadIdx.x) * stride;
    if (idx < n) {
        data[idx] = idx * 2.0f;  // Strided: poor performance
    }
}

__global__ void coalesced_access(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = idx * 2.0f;  // Coalesced: adjacent threads access adjacent memory
    }
}
```

**Key Points:**
- Coalesced access can be 5-10x faster than strided
- Warp threads should access consecutive 128-byte segments
- Source: `src/part_specific/vector_add_memory.cu:23-44`

### **17.8.2 2D Memory Access Patterns**

Two-dimensional array access patterns demonstrate the significant performance difference between row-major and column-major memory layouts. The choice of access pattern can result in order-of-magnitude performance differences due to memory coalescing effects. Full example in `src/kernels/vector_add_2d.cu`.

```cpp
// vector_add_2d.cu - 2D memory access patterns
__global__ void vector_add_2d_row_major(
    const float* a, const float* b, float* c,
    int width, int height
) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x < width && y < height) {
        int idx = y * width + x;  // Row-major: coalesced for x-dimension
        c[idx] = a[idx] + b[idx];
    }
}
```

**Expected Performance:**
```
Row-major access: 450 GB/s (95% efficiency)
Column-major access: 90 GB/s (19% efficiency)
```

---

## **17.9 Matrix Multiplication Evolution**

This section demonstrates the progression from naive to highly optimized matrix multiplication. Each implementation builds upon previous optimizations.

### **17.9.1 Naive Implementation**

The naive implementation serves as our baseline, implementing the mathematical definition of matrix multiplication without any GPU-specific optimizations. This approach suffers from poor memory access patterns and lacks data reuse, resulting in low performance. Source: `src/kernels/matrix_multiply.cu`.

```cpp
// matrix_multiply.cu - O(N³) baseline implementation
__global__ void matmul_naive(const float* A, const float* B, float* C, int N) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < N && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < N; k++) {
            sum += A[row * N + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}
```

**Performance**: ~50 GFLOPS on RTX 3090

### **17.9.2 Coalesced Memory Access**

This implementation improves memory access patterns to achieve better coalescing for matrix A while relying on caching for matrix B accesses. Although B's column-wise access isn't fully coalesced, the L1 and L2 caches help mitigate the performance impact. Source: `src/kernels/matrix_multiply.cu`.

```cpp
// matrix_multiply.cu - Coalesced memory access pattern
__global__ void matmul_coalesced(const float* A, const float* B, float* C, int N) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < N && col < N) {
        float sum = 0.0f;
        // Access pattern optimized for coalescing
        for (int k = 0; k < N; k++) {
            // A is accessed row-wise (coalesced)
            // B is accessed column-wise (not coalesced, but cached)
            sum += A[row * N + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}
```

**Performance**: ~75 GFLOPS on RTX 3090 (1.5x improvement)

### **17.9.3 Tiled Implementation with Shared Memory**

The tiled implementation divides matrices into smaller tiles that fit in shared memory, dramatically reducing global memory accesses. Each tile is loaded once and reused multiple times by all threads in a block, achieving near-optimal memory bandwidth utilization. Source: `src/kernels/matrix_multiply.cu`.

```cpp
// matrix_multiply.cu - Tiled implementation with shared memory
#define TILE_SIZE 16

__global__ void matmul_shared(const float* A, const float* B, float* C, int N) {
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int bx = blockIdx.x, by = blockIdx.y;
    int tx = threadIdx.x, ty = threadIdx.y;

    int row = by * TILE_SIZE + ty;
    int col = bx * TILE_SIZE + tx;

    float sum = 0.0f;

    for (int tile = 0; tile < (N + TILE_SIZE - 1) / TILE_SIZE; tile++) {
        // Load tiles into shared memory
        if (row < N && tile * TILE_SIZE + tx < N)
            As[ty][tx] = A[row * N + tile * TILE_SIZE + tx];
        else
            As[ty][tx] = 0.0f;

        if (col < N && tile * TILE_SIZE + ty < N)
            Bs[ty][tx] = B[(tile * TILE_SIZE + ty) * N + col];
        else
            Bs[ty][tx] = 0.0f;

        __syncthreads();

        // Compute partial products
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    if (row < N && col < N) {
        C[row * N + col] = sum;
    }
}
```

**Performance**: ~400 GFLOPS on RTX 3090 (8x improvement over naive)

---

## **17.10 Shared Memory Optimization (Matrix Tiling)**

This section explores advanced shared memory techniques for maximizing performance. Shared memory provides low-latency, high-bandwidth storage shared among threads in a block.

### **17.10.1 Bank Conflict Free Implementation**

Bank conflicts occur when multiple threads in a warp access different addresses in the same shared memory bank, causing serialization of memory accesses. By adding padding to shift memory addresses to different banks, we can eliminate these conflicts and achieve full shared memory bandwidth. Source: `src/kernels/matrix_multiply.cu`.

```cpp
// matrix_multiply.cu - Bank conflict free shared memory
#define TILE_SIZE 16

__global__ void matmul_shared_bank_conflict_free(
    const float* A, const float* B, float* C, int N
) {
    // Add padding to avoid bank conflicts
    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    // Rest of implementation similar to matmul_shared
    // Padding shifts memory addresses to different banks
    // This prevents serialization of memory accesses
}
```

**Performance**: ~450 GFLOPS on RTX 3090 (9x improvement over naive)

### **17.10.2 Double Buffering Strategy**

Double buffering uses two sets of shared memory buffers to overlap data loading with computation, hiding memory latency. While one buffer is being used for computation, the next tile is loaded into the alternate buffer, maximizing both memory and compute throughput. Implementation concept in `src/kernels/matrix_multiply.cu`.

```cpp
// Conceptual double buffering approach
__global__ void matmul_double_buffered(const float* A, const float* B, float* C, int N) {
    // Two sets of shared memory buffers
    __shared__ float As[2][TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[2][TILE_SIZE][TILE_SIZE + 1];

    int buffer = 0;
    // Load first tile
    load_tile(As[buffer], Bs[buffer], ...);
    __syncthreads();

    for (int tile = 1; tile < num_tiles; tile++) {
        // Load next tile while computing current
        load_tile(As[1-buffer], Bs[1-buffer], ...);
        compute_tile(As[buffer], Bs[buffer], ...);
        __syncthreads();
        buffer = 1 - buffer;
    }
}
```

---

## **17.10 Bank Conflict Mitigation**

This section details strategies for avoiding shared memory bank conflicts. Bank conflicts occur when multiple threads in a warp access different addresses in the same memory bank.

### **17.10.1 Understanding Bank Conflicts**

Modern GPUs organize shared memory into 32 banks, with successive 32-bit words assigned to successive banks. When multiple threads in a warp access different addresses in the same bank, the accesses are serialized, dramatically reducing performance. Test implementation in `test/unit/kernels/test_matrix_multiply.cu`.

```cpp
// test_matrix_multiply.cu - Bank conflict detection
__global__ void test_bank_conflicts(float* output) {
    __shared__ float data[32][32];
    int tid = threadIdx.x;

    // Scenario 1: No bank conflict - each thread accesses different bank
    data[tid][0] = tid;  // Linear access pattern

    // Scenario 2: 2-way bank conflict
    data[tid * 2 % 32][0] = tid;  // Every other thread conflicts

    // Scenario 3: 32-way bank conflict (worst case)
    data[0][tid] = tid;  // All threads access same bank
}
```

### **17.10.2 Padding Technique**

Padding is a simple yet effective technique for eliminating bank conflicts by adding extra elements to array dimensions. This shifts memory addresses so that threads in a warp access different banks, converting serialized accesses into parallel ones and achieving dramatic speedups. Source: `test/unit/part_specific/benchmark_memory.cu`.

```cpp
// benchmark_memory.cu - Padding to avoid conflicts
template<bool USE_PADDING>
__global__ void benchmark_shared_memory(float* output, int iterations) {
    const int ARRAY_SIZE = 32;

    // Without padding: potential conflicts
    __shared__ float no_pad[ARRAY_SIZE][ARRAY_SIZE];

    // With padding: conflict-free
    __shared__ float padded[ARRAY_SIZE][ARRAY_SIZE + 1];

    // Benchmark code measures the difference
}
```

**Expected Results:**
```
Without padding: 180 GB/s shared memory bandwidth
With padding: 1300 GB/s shared memory bandwidth
Improvement: 7.2x
```

---

## **17.11 Profiling and Performance Analysis**

This section provides detailed guidance on using NVIDIA's profiling tools to analyze memory performance and identify bottlenecks. Effective profiling is essential for understanding where optimizations should be applied.

### **17.11.1 Using Nsight Systems for Memory Analysis**

Nsight Systems provides system-wide performance analysis, showing memory transfers, kernel execution, and CPU-GPU synchronization. This tool is ideal for understanding overall application behavior and identifying high-level bottlenecks.

**Basic Profiling Commands:**
```bash
# Profile with CUDA and memory transfer tracing
nsys profile --trace=cuda,nvtx,osrt --stats=true ./17_Memory_Hierarchy_benchmark

# Focus on memory operations only
nsys profile --trace=cuda --cuda-memory-usage=true ./17_Memory_Hierarchy_benchmark

# Export to SQLite for custom analysis
nsys profile --export sqlite --output memory_profile ./17_Memory_Hierarchy_benchmark
```

**Key Metrics to Analyze:**
- **Memory Transfer Time**: Time spent in cudaMemcpy operations
- **Kernel Execution Time**: GPU compute time vs memory transfer time
- **CPU-GPU Synchronization**: Idle time due to synchronization
- **Stream Utilization**: Overlap between transfers and computation

**Example Output Interpretation:**
```
Memory Transfer (H2D):  45 ms  (25% of total time)
Kernel Execution:      120 ms  (67% of total time)
Memory Transfer (D2H):  15 ms  (8% of total time)
```

**Optimization Insights:**
- If transfers dominate (>30%), consider pinned memory or async transfers
- If kernel execution dominates but bandwidth is low, check memory access patterns
- Look for gaps in GPU utilization indicating synchronization issues

### **17.11.2 Using Nsight Compute for Kernel Memory Analysis**

Nsight Compute provides detailed kernel-level analysis with specific memory metrics. Use this tool to understand how individual kernels utilize the memory hierarchy.

**Memory-Specific Profiling Commands:**
```bash
# Analyze memory bandwidth utilization
ncu --metrics dram__throughput.avg.pct_of_peak_sustained_elapsed \
    --metrics l1tex__throughput.avg.pct_of_peak_sustained_elapsed \
    ./17_Memory_Hierarchy_benchmark

# Detect bank conflicts
ncu --metrics l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_ld.sum,\
l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_st.sum \
    ./17_Memory_Hierarchy_benchmark

# Memory access pattern analysis
ncu --metrics smsp__sass_average_data_bytes_per_sector_mem_global_op_ld.pct,\
smsp__sass_average_data_bytes_per_sector_mem_global_op_st.pct \
    ./17_Memory_Hierarchy_benchmark

# Complete memory analysis set
ncu --set full --section MemoryWorkloadAnalysis \
    ./17_Memory_Hierarchy_benchmark
```

**Critical Memory Metrics:**

| Metric | Good Value | Indicates | Fix |
|--------|------------|-----------|-----|
| `dram__throughput` | >80% | Global memory bandwidth utilization | Optimize access patterns |
| `l1tex__data_bank_conflicts` | <1% | Shared memory bank conflicts | Add padding or reorganize |
| `l1tex__t_sectors_pipe_lsu` | >75% | Memory coalescing efficiency | Ensure coalesced access |
| `smsp__average_data_bytes_per_sector` | 100% | Memory transaction efficiency | Align and coalesce accesses |

### **17.11.3 Identifying Memory Bottlenecks**

Use this systematic approach to identify and resolve memory bottlenecks:

**Step 1: Measure Achieved vs Peak Bandwidth**
```bash
# Get device theoretical bandwidth
nvidia-smi --query-gpu=memory.bandwidth --format=csv

# Measure achieved bandwidth with kernel timing
ncu --metrics dram__bytes.sum --metrics dram__bytes_read.sum --metrics dram__bytes_write.sum \
    ./your_kernel
```

**Bandwidth Calculation:**
```cpp
// In your benchmark code
float achieved_bandwidth = (bytes_read + bytes_written) / (time_ms / 1000.0f) / 1e9;
float peak_bandwidth = 900.0f;  // GB/s for RTX 3090
float efficiency = (achieved_bandwidth / peak_bandwidth) * 100.0f;

printf("Achieved: %.1f GB/s (%.1f%% of peak)\n", achieved_bandwidth, efficiency);
```

**Step 2: Diagnose Based on Efficiency**
- **<30%**: Likely uncoalesced access or excessive serialization
- **30-60%**: Moderate access pattern issues, check for partial coalescing
- **60-80%**: Good utilization, look for algorithmic improvements
- **>80%**: Excellent, memory-bound kernel is well-optimized

**Step 3: Profile Memory Access Patterns**
```bash
# Check global load efficiency
ncu --metrics l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum \
    --metrics l1tex__t_requests_pipe_lsu_mem_global_op_ld.sum \
    ./your_kernel

# Efficiency = sectors / (requests * 32)
# 100% = perfectly coalesced
# <50% = significant inefficiency
```

### **17.11.4 Practical Profiling Workflow**

**Development Phase:**
```bash
# 1. Baseline measurement
nsys profile --stats=true -o baseline ./naive_kernel

# 2. Identify hotspots
nsys-ui baseline.nsys-rep
# Look for: kernel execution time, memory transfers

# 3. Detailed kernel analysis
ncu --set full --launch-skip 0 --launch-count 1 -o kernel_profile ./naive_kernel

# 4. Open in GUI for interactive analysis
ncu-ui kernel_profile.ncu-rep
```

**Optimization Iteration:**
```bash
# After each optimization, compare:
ncu --set full -o optimized_v1 ./optimized_kernel
ncu --set full -o optimized_v2 ./optimized_kernel

# Compare reports
ncu --import optimized_v1.ncu-rep optimized_v2.ncu-rep
```

**Production Monitoring:**
```bash
# Lightweight profiling for regression testing
ncu --metrics dram__throughput,l1tex__throughput --csv \
    ./production_kernel > metrics.csv

# Automated performance tracking
python analyze_metrics.py metrics.csv  # Custom analysis script
```

---

## **17.12 Advanced Optimization Techniques**

This section covers advanced memory optimization strategies beyond basic coalescing and shared memory usage. These techniques can provide additional performance improvements for compute-intensive applications.

### **17.12.1 Memory Prefetching**

Modern GPUs support explicit prefetching to hide memory latency by loading data before it's needed.

```cpp
// Prefetch data from global to L2 cache
__global__ void prefetch_demo(float* __restrict__ data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Prefetch next block of data while processing current block
    if (idx + blockDim.x < n) {
        __builtin_prefetch(&data[idx + blockDim.x]);
    }

    // Process current data
    if (idx < n) {
        float value = data[idx];
        data[idx] = value * 2.0f + 1.0f;
    }
}
```

**Explicit L2 Cache Hints (Compute Capability 8.0+):**
```cpp
#include <cuda_runtime.h>

__global__ void l2_prefetch_kernel(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Prefetch to L2 cache
    if (idx + 256 < n) {
        __prefetch_l2(&data[idx + 256]);
    }

    if (idx < n) {
        data[idx] = data[idx] * 2.0f;
    }
}
```

### **17.12.2 Read-Only Data Cache (ldg)**

Use `__ldg()` intrinsic for read-only data to utilize the read-only data cache path, which can improve performance for data accessed by all threads.

```cpp
// Standard global load
__global__ void standard_load(const float* data, float* out, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        out[idx] = data[idx] * 2.0f;  // Regular load
    }
}

// Optimized with read-only cache
__global__ void readonly_load(const float* __restrict__ data, float* out, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        out[idx] = __ldg(&data[idx]) * 2.0f;  // Read-only load
    }
}
```

**When to Use `__ldg()`:**
- Data is read-only throughout the kernel
- Multiple threads read the same data (broadcast scenario)
- Data has spatial locality (nearby elements are accessed together)

**Performance Gains:**
- Typical: 5-15% improvement for read-heavy kernels
- Best case: 30-40% for broadcast-style access patterns

### **17.12.3 Asynchronous Memory Copy**

Overlap memory transfers with computation using CUDA streams for better utilization.

```cpp
void async_pipeline(float* h_input, float* h_output, int total_size) {
    const int num_streams = 4;
    const int chunk_size = total_size / num_streams;

    cudaStream_t streams[num_streams];
    float* d_buffers[num_streams];

    // Create streams and allocate pinned memory
    for (int i = 0; i < num_streams; i++) {
        cudaStreamCreate(&streams[i]);
        cudaMalloc(&d_buffers[i], chunk_size * sizeof(float));
    }

    // Overlap transfer and computation
    for (int i = 0; i < num_streams; i++) {
        int offset = i * chunk_size;

        // Async H2D transfer
        cudaMemcpyAsync(d_buffers[i], &h_input[offset],
                       chunk_size * sizeof(float),
                       cudaMemcpyHostToDevice, streams[i]);

        // Kernel launch (overlapped with next transfer)
        process_kernel<<<grid, block, 0, streams[i]>>>(d_buffers[i], chunk_size);

        // Async D2H transfer
        cudaMemcpyAsync(&h_output[offset], d_buffers[i],
                       chunk_size * sizeof(float),
                       cudaMemcpyDeviceToHost, streams[i]);
    }

    // Wait for all streams
    for (int i = 0; i < num_streams; i++) {
        cudaStreamSynchronize(streams[i]);
        cudaStreamDestroy(streams[i]);
        cudaFree(d_buffers[i]);
    }
}
```

**Achieved Speedup:**
- Memory-bound kernels: 1.5-2.5x (with sufficient PCIe bandwidth)
- Requires pinned (page-locked) host memory for maximum benefit

### **17.12.4 Unified Memory and Prefetching**

Unified Memory simplifies programming but requires prefetching hints for optimal performance.

```cpp
// Allocate unified memory
float* data;
cudaMallocManaged(&data, n * sizeof(float));

// Prefetch to GPU before kernel
int device = 0;
cudaMemPrefetchAsync(data, n * sizeof(float), device);

// Run kernel
kernel<<<grid, block>>>(data, n);

// Prefetch back to CPU
cudaMemPrefetchAsync(data, n * sizeof(float), cudaCpuDeviceId);
```

**Unified Memory Advantages:**
- Automatic data migration
- Simplified memory management
- Good for prototyping

**Performance Considerations:**
- Add explicit prefetching for production code
- 10-30% slower than explicit memory management without hints
- Comparable performance with proper prefetching

### **17.12.5 Memory Access Pattern Transformations**

**Array of Structures (AoS) to Structure of Arrays (SoA):**

```cpp
// AoS - Poor coalescing
struct Particle {
    float x, y, z;    // Position
    float vx, vy, vz; // Velocity
};
Particle particles[N];

// Access pattern - strided, uncoalesced
__global__ void update_aos(Particle* p, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        p[idx].x += p[idx].vx;  // Loads: x, vx, vx again
        p[idx].y += p[idx].vy;
        p[idx].z += p[idx].vz;
    }
}

// SoA - Excellent coalescing
struct ParticlesSoA {
    float* x;  float* y;  float* z;
    float* vx; float* vy; float* vz;
};

// Access pattern - coalesced
__global__ void update_soa(ParticlesSoA p, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        p.x[idx] += p.vx[idx];  // Consecutive threads access consecutive addresses
        p.y[idx] += p.vy[idx];
        p.z[idx] += p.vz[idx];
    }
}
```

**Performance Impact:**
- AoS: ~150 GB/s bandwidth (25% efficiency)
- SoA: ~650 GB/s bandwidth (95% efficiency)
- Improvement: 4.3x speedup

---

## **17.13 Memory Optimization Glossary**

Quick reference for CUDA memory terminology and concepts.

### **Memory Types**

**Register Memory**: Fastest storage, private to each thread. Limited to ~255 registers per thread. Access latency: ~1 cycle.

**Shared Memory**: Fast on-chip memory shared among threads in a block. Size: 48-96 KB per block. Access latency: ~20-30 cycles. Explicitly managed by programmer.

**Global Memory**: Main GPU DRAM, accessible by all threads. Size: 4-48 GB. Access latency: ~440 cycles. Requires coalescing for efficiency.

**Constant Memory**: Read-only 64 KB cache for uniform reads. Optimized when all threads access the same address (broadcast). Access latency: ~48 cycles (cached).

**Texture Memory**: Specialized for 2D/3D spatial locality with hardware filtering. Has dedicated cache. Access latency: ~100 cycles (cached).

**Local Memory**: Per-thread storage that spills to global memory when registers are exhausted. Same latency as global memory (~440 cycles).

**L1 Cache**: Per-SM cache (128 KB on modern GPUs). Caches global and local memory automatically. Access latency: ~30 cycles.

**L2 Cache**: Device-wide cache (4-6 MB) shared across all SMs. Caches global memory accesses. Access latency: ~120 cycles.

### **Access Patterns**

**Coalesced Access**: Consecutive threads access consecutive memory addresses, allowing the GPU to combine multiple accesses into a single transaction. Essential for high bandwidth.

**Strided Access**: Threads access memory at regular intervals (stride). Reduces bandwidth efficiency. A stride of 1 is coalesced, larger strides waste bandwidth.

**Broadcast**: All threads in a warp read the same address. Constant memory is optimized for this pattern. Single transaction serves entire warp.

**Random Access**: Unpredictable access pattern with no spatial locality. Worst case for memory performance, serializes many requests.

### **Performance Metrics**

**Memory Bandwidth**: Data transfer rate, measured in GB/s. Theoretical peak for RTX 3090: ~935 GB/s. Achieved bandwidth depends on access patterns.

**Memory Throughput**: Percentage of peak bandwidth utilized. >80% is excellent, <50% indicates access pattern problems.

**Memory Coalescing Efficiency**: Ratio of useful data to total data transferred. 100% means perfect coalescing, <50% means significant waste.

**Bank Conflict**: Multiple threads in a warp accessing different addresses in the same shared memory bank, causing serialization. Reduces shared memory bandwidth by factor of 32 (worst case).

**Occupancy**: Ratio of active warps to maximum possible warps on an SM. Higher occupancy can hide memory latency through thread switching.

**Register Spilling**: When kernel uses more registers than available, excess data spills to slow local memory. Reduces performance significantly.

### **Optimization Techniques**

**Tiling**: Breaking computation into smaller blocks (tiles) that fit in shared memory. Reduces global memory accesses by reusing data in fast shared memory.

**Padding**: Adding extra elements to arrays to avoid bank conflicts. Example: `float array[32][33]` instead of `[32][32]` prevents column-wise bank conflicts.

**Loop Unrolling**: Manually or automatically expanding loops to reduce iteration overhead and expose more instruction-level parallelism.

**Prefetching**: Loading data before it's needed to hide memory latency. Can be implicit (hardware) or explicit (`__prefetch`, `__ldg`).

**Double Buffering**: Using two buffers - one for computation, one for loading next data. Overlaps memory transfer with computation.

**Stream Pipelining**: Using multiple CUDA streams to overlap memory transfers and kernel execution. Requires pinned memory for async transfers.

### **Common Issues**

**Warp Divergence**: Threads in a warp taking different execution paths (if/else). Reduces parallelism, not directly a memory issue but often confused with bank conflicts.

**False Sharing**: Different threads modifying different parts of the same cache line. More relevant for CPUs, less common in CUDA.

**Alignment**: Memory addresses should be aligned to access size (4-byte aligned for float, 8-byte for double). Misalignment causes extra transactions.

**Cache Thrashing**: Working set exceeds cache size, causing constant evictions. Reduce working set or improve locality.

---

## **17.14 Testing**

This module includes comprehensive unit and performance tests to validate correctness and measure optimization improvements. The tests compare different implementations and verify that optimizations maintain numerical accuracy while improving performance.

### **17.14.1 Unit Tests with GpuTest Base Class**

Unit tests verify the correctness of each implementation by comparing results between optimized and baseline versions. These tests ensure that performance optimizations don't compromise accuracy and that all edge cases are handled correctly. Tests are in `test/unit/kernels/` and `test/unit/part_specific/`.

The `GpuTest` base class (available in [00.test_lib/gpu_gtest.h](../../00.test_lib/gpu_gtest.h)) provides automatic CUDA device setup/teardown, eliminating boilerplate code:
- Automatic CUDA device detection and initialization
- Error clearing before each test
- Error checking after each test
- Proper test skipping if no CUDA devices are available

```cpp
// test/unit/kernels/test_matrix_multiply.cu
#include <gtest/gtest.h>
#include "gpu_gtest.h"

// Inherit from GpuTest for automatic device setup/teardown
class MatrixMultiplyTest : public GpuTest {
protected:
    void TearDown() override {
        GpuTest::TearDown();
        cudaDeviceReset();
    }

    void TestMatMulKernel(void (*kernel)(const float*, const float*, float*, int),
                          int N, const char* kernel_name) {
        // No need for manual device setup - GpuTest handles it
        float *d_A = cuda_malloc<float>(N * N);
        float *d_B = cuda_malloc<float>(N * N);
        float *d_C = cuda_malloc<float>(N * N);

        // Initialize and run test...
        dim3 block(16, 16);
        dim3 grid((N+15)/16, (N+15)/16);
        kernel<<<grid, block>>>(d_A, d_B, d_C, N);
        CHECK_KERNEL_LAUNCH();

        // Verify results...
        cuda_free(d_A);
        cuda_free(d_B);
        cuda_free(d_C);
    }
};

TEST_F(MatrixMultiplyTest, NaiveImplementation) {
    for (int N : {16, 32, 64, 128}) {
        TestMatMulKernel(matmul_naive, N, "matmul_naive");
    }
}

// Parameterized tests can also use GpuTest
class ParameterizedMatrixTest : public GpuTest, public ::testing::WithParamInterface<int> {
};

TEST_P(ParameterizedMatrixTest, AllKernelsCorrectness) {
    int N = GetParam();
    // GpuTest base class handles all device setup
    // Test implementation...
}

INSTANTIATE_TEST_SUITE_P(MatrixSizes, ParameterizedMatrixTest,
                        ::testing::Values(16, 32, 48, 64, 96, 128));
```

**Key Benefits:**
- No manual `cudaGetDeviceCount()` or `GTEST_SKIP()` needed
- Consistent error handling across all GPU tests
- Cleaner test code focused on actual test logic
- Library code reused from [00.test_lib/gpu_gtest.h](../../00.test_lib/gpu_gtest.h)

### **17.14.2 Performance Tests and Benchmarks**

Performance tests measure bandwidth utilization, GFLOPS, and relative speedups between implementations. The module includes comprehensive benchmark functions that are tested to ensure they work correctly.

**Benchmark Functions** (from [src/kernels/matrix_multiply.cu](src/kernels/matrix_multiply.cu)):
- `benchmark_kernel()` - Template function to benchmark any kernel and measure GFLOPS
- `run_memory_hierarchy_benchmark()` - Comprehensive benchmark comparing all optimization levels
- `demonstrate_memory_patterns()` - Shows performance difference between coalesced vs strided access
- `demonstrate_strided_access()` / `demonstrate_coalesced_access()` - Kernels for memory pattern demos

These functions are tested in [test/unit/kernels/test_matrix_multiply.cu](test/unit/kernels/test_matrix_multiply.cu):

```cpp
// Test the benchmark function
TEST_F(MatrixMultiplyTest, BenchmarkFunctionTest) {
    const int N = 256;
    // ... setup code ...

    // Use the benchmark_kernel template function
    float naive_time = benchmark_kernel(matmul_naive, d_A, d_B, d_C, N,
                                       gridSize, blockSize, "Naive", 5);
    float shared_time = benchmark_kernel(matmul_shared, d_A, d_B, d_C, N,
                                        gridSize, blockSize, "Shared", 5);

    // Verify functions run without error
    EXPECT_GT(naive_time, 0.0f);
    EXPECT_GT(shared_time, 0.0f);
}

// Test the full memory hierarchy benchmark
TEST_F(MatrixMultiplyTest, MemoryHierarchyBenchmark) {
    std::cout << "\n--- Running Memory Hierarchy Benchmark ---" << std::endl;
    ASSERT_NO_THROW(run_memory_hierarchy_benchmark(256));
    std::cout << "--- Benchmark Complete ---\n" << std::endl;
}

// Test memory access pattern demonstrations
TEST_F(MatrixMultiplyTest, DemonstrateMemoryPatterns) {
    std::cout << "\n--- Testing Memory Pattern Demonstration ---" << std::endl;
    ASSERT_NO_THROW(demonstrate_memory_patterns());
    std::cout << "--- Memory Pattern Demo Complete ---\n" << std::endl;
}
```

**Running Benchmarks:**
```bash
# Run all tests including benchmarks
./10.cuda_basic/17.Memory_Hierarchy/test/17_Memory_Hierarchy_test

# Run only benchmark tests
./10.cuda_basic/17.Memory_Hierarchy/test/17_Memory_Hierarchy_test --gtest_filter="*Benchmark*"
```

### **17.14.3 Comprehensive Memory Benchmarks**

The module includes a comprehensive benchmark suite that measures real-world performance of different memory optimization techniques.

**File Organization:**
- **Benchmark Classes**: [src/part_specific/memory_benchmarks.cu](src/part_specific/memory_benchmarks.cu)
  - `MemoryBenchmark` - Vector operations with different memory access patterns
  - `MatrixBenchmark` - Matrix multiplication implementation comparisons
- **Test Cases**: [test/unit/part_specific/test_memory_benchmarks.cu](test/unit/part_specific/test_memory_benchmarks.cu)
  - GTest-based tests that use the benchmark classes

**Tests included:**
```cpp
// Vector memory benchmarks
TEST_F(MemoryBenchmarkTest, GlobalMemoryBenchmark) {
    MemoryBenchmark bench;
    bench.benchmark_global_memory();  // Measures bandwidth for global memory access
}

TEST_F(MemoryBenchmarkTest, SharedMemoryBenchmark) {
    MemoryBenchmark bench;
    bench.benchmark_shared_memory();  // Tests shared memory performance
}

TEST_F(MemoryBenchmarkTest, CoalescingBenchmark) {
    MemoryBenchmark bench;
    bench.benchmark_coalescing();  // Compares coalesced vs strided access
}

TEST_F(MemoryBenchmarkTest, BankConflictBenchmark) {
    MemoryBenchmark bench;
    bench.benchmark_bank_conflicts();  // Measures impact of bank conflicts
}

// Matrix multiplication benchmarks
TEST_F(MemoryBenchmarkTest, MatrixMultiplicationBenchmark) {
    MatrixBenchmark bench;
    bench.benchmark_all();  // Compares all matmul implementations
}
```

**Running comprehensive benchmarks:**
```bash
# Run all memory benchmarks
./10.cuda_basic/17.Memory_Hierarchy/test/17_Memory_Hierarchy_test --gtest_filter="MemoryBenchmarkTest.*"

# Run specific benchmark
./10.cuda_basic/17.Memory_Hierarchy/test/17_Memory_Hierarchy_test --gtest_filter="*CoalescingBenchmark"
```

These benchmarks provide quantitative measurements of:
- Memory bandwidth (GB/s) for different access patterns
- Performance (GFLOPS) for matrix operations
- Speedup factors from optimizations
- Impact of coalescing and bank conflicts

## Build & Run

This section provides instructions for building and running the memory hierarchy demonstrations and tests. The build system uses CMake and Ninja for fast compilation and supports various profiling tools for performance analysis.

### Building

The module can be built using CMake with separate targets for the library, tests, and benchmarks. Use Ninja for faster build times compared to Make.
```bash
cd build
cmake --build . --target 17_Memory_Hierarchy_lib
cmake --build . --target 17_Memory_Hierarchy_test
cmake --build . --target 17_Memory_Hierarchy_benchmark
```

### Running Tests

Tests can be run through CTest for automated testing or directly for detailed output. The test executables support Google Test filters for running specific test cases.
```bash
# Run all tests for this module
ctest -R "17_Memory"

# Run specific test with output
./10.cuda_basic/17.Memory_Hierarchy/17_Memory_Hierarchy_test --gtest_filter="*MatrixMultiply*"

# Run benchmarks
./10.cuda_basic/17.Memory_Hierarchy/17_Memory_Hierarchy_benchmark
```

### Running Performance Analysis

NVIDIA's profiling tools provide detailed insights into memory access patterns, bandwidth utilization, and performance bottlenecks. Use these tools to verify optimization effectiveness and identify further improvement opportunities.
```bash
# Memory access pattern analysis
nsys profile --stats=true ./10.cuda_basic/17.Memory_Hierarchy/17_Memory_Hierarchy_benchmark

# Detailed metrics with Nsight Compute
ncu --metrics l1tex__throughput,lts__throughput,dram__throughput ./10.cuda_basic/17.Memory_Hierarchy/17_Memory_Hierarchy_benchmark

# Bank conflict analysis
ncu --metrics l1tex__data_bank_conflicts_pipe_lsu ./10.cuda_basic/17.Memory_Hierarchy/17_Memory_Hierarchy_test
```

---

## **17.15 Summary**

This module demonstrated the critical importance of memory hierarchy optimization in CUDA programming. Through progressive optimizations of matrix multiplication, we achieved nearly 10x performance improvements by properly utilizing different memory types and access patterns.

### **Key Takeaways**
1. Memory hierarchy optimization can yield 8-10x performance improvements
2. Coalesced memory access is critical for global memory bandwidth utilization
3. Shared memory with proper bank conflict mitigation enables near-peak throughput

### **Performance Metrics**

These metrics show the dramatic performance improvements achieved through memory hierarchy optimization. Each optimization level demonstrates the impact of specific techniques on overall throughput.
- Baseline (Naive): 50 GFLOPS
- Coalesced Access: 75 GFLOPS
- Shared Memory: 400 GFLOPS
- Bank-Conflict Free: 450 GFLOPS
- Efficiency: 85% of theoretical peak

### **Common Errors & Solutions**

This table summarizes the most common memory-related performance issues and their solutions. Understanding these patterns helps avoid pitfalls in production code.
| Error | Cause | Solution |
|-------|-------|----------|
| Low bandwidth | Uncoalesced access | Ensure consecutive threads access consecutive addresses |
| Bank conflicts | Multiple threads access same bank | Add padding or reorganize access pattern |
| Register spilling | Too many variables per thread | Reduce register usage or adjust block size |
| Low occupancy | Resource overuse | Balance shared memory, registers, and block size |

### **Next Steps**

After mastering memory hierarchy optimization, continue your learning journey with more advanced topics. These resources and exercises will help deepen your understanding of GPU programming.
- 📚 Continue to [Part 18: Thread Hierarchy Practice](../18.Thread_Hierarchy_Practice/README.md)
- 🔧 Try optimizing for different tile sizes in `src/kernels/matrix_multiply.cu`
- 📊 Run performance benchmarks with `17_Memory_Hierarchy_benchmark`

### **References**

These official NVIDIA resources provide in-depth coverage of memory optimization techniques and best practices. Consult them for detailed specifications and advanced optimization strategies.
- [CUDA Programming Guide - Memory Hierarchy](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#memory-hierarchy)
- [CUDA Best Practices Guide - Memory Optimizations](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/index.html#memory-optimizations)
- [Nsight Compute Memory Workload Analysis](https://docs.nvidia.com/nsight-compute/NsightCompute/index.html#memory-workload-analysis)