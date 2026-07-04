# CUDA vs TBB: Programming Model Comparison

## The Core Difference

| Aspect | CUDA | TBB |
|--------|------|-----|
| **Model** | Kernel launch (data-parallel) | Function call (task-parallel) |
| **Entry points** | Multiple `__global__` kernels | Single process, library calls |
| **Thread identity** | `threadIdx`, `blockIdx` | Hidden (optional access) |
| **Parallelism** | Explicit dimensions | Implicit (auto-managed) |
| **Launch syntax** | `kernel<<<blocks, threads>>>(args)` | `parallel_for(range, func)` |

## Visual Comparison

```
CUDA Model:
┌─────────────────────────────────────────────────────────────────┐
│  CPU Code                        GPU Kernels                    │
│  ┌──────────────────┐           ┌──────────────────┐           │
│  │ int main() {     │           │ __global__ void  │           │
│  │   // Setup       │           │ kernelA(...) {   │           │
│  │   kernelA<<<>>>()│──────────►│   int tid = ...  │           │
│  │   kernelB<<<>>>()│──┐        │   process(tid)   │           │
│  │ }                │  │        │ }                │           │
│  └──────────────────┘  │        └──────────────────┘           │
│                        │        ┌──────────────────┐           │
│                        └───────►│ __global__ void  │           │
│                                 │ kernelB(...) {   │           │
│                                 │   ...            │           │
│                                 │ }                │           │
│                                 └──────────────────┘           │
│                                                                 │
│  Multiple "entry points" (kernels) launched explicitly          │
└─────────────────────────────────────────────────────────────────┘

TBB Model:
┌─────────────────────────────────────────────────────────────────┐
│  Single Process                                                  │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ int main() {                                              │   │
│  │   tbb::parallel_for(0, N, [](int i) {                    │   │
│  │     process(i);  // Lambda executed in parallel           │   │
│  │   });                                                     │   │
│  │                                                           │   │
│  │   tbb::parallel_for(0, M, [](int i) {                    │   │
│  │     other_work(i);                                        │   │
│  │   });                                                     │   │
│  │ }                                                         │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                  │
│  Single process, parallel regions via library calls              │
└─────────────────────────────────────────────────────────────────┘
```

## Creating CUDA-like Interface for TBB

Yes! You can create a CUDA-like interface:

### Basic CUDA-style Wrapper

```cpp
#include <tbb/tbb.h>
#include <functional>
#include <cstdint>

namespace cuda_style {

//==============================================================================
// Thread Index (like CUDA's threadIdx, blockIdx)
//==============================================================================
struct Dim3 {
    int x = 0, y = 0, z = 0;
    
    Dim3() = default;
    Dim3(int x_) : x(x_) {}
    Dim3(int x_, int y_) : x(x_), y(y_) {}
    Dim3(int x_, int y_, int z_) : x(x_), y(y_), z(z_) {}
};

// Thread-local indices (like CUDA built-in variables)
struct KernelContext {
    Dim3 threadIdx;
    Dim3 blockIdx;
    Dim3 blockDim;
    Dim3 gridDim;
    
    // Flat global index
    int global_id() const {
        return blockIdx.x * blockDim.x + threadIdx.x;
    }
    
    // 2D global index
    int global_id_2d(int dim_x) const {
        int gx = blockIdx.x * blockDim.x + threadIdx.x;
        int gy = blockIdx.y * blockDim.y + threadIdx.y;
        return gy * dim_x + gx;
    }
};

//==============================================================================
// Kernel Launch (like CUDA <<<blocks, threads>>>)
//==============================================================================
template<typename KernelFunc>
void launch(Dim3 grid, Dim3 block, KernelFunc kernel) {
    const int total_blocks = grid.x * grid.y * grid.z;
    const int threads_per_block = block.x * block.y * block.z;
    
    // Parallel over blocks (like CUDA block scheduling)
    tbb::parallel_for(0, total_blocks, [&](int block_id) {
        // Decode block index
        Dim3 blockIdx;
        blockIdx.z = block_id / (grid.x * grid.y);
        blockIdx.y = (block_id % (grid.x * grid.y)) / grid.x;
        blockIdx.x = block_id % grid.x;
        
        // Execute all "threads" in this block
        for (int tid = 0; tid < threads_per_block; ++tid) {
            Dim3 threadIdx;
            threadIdx.z = tid / (block.x * block.y);
            threadIdx.y = (tid % (block.x * block.y)) / block.x;
            threadIdx.x = tid % block.x;
            
            KernelContext ctx;
            ctx.threadIdx = threadIdx;
            ctx.blockIdx = blockIdx;
            ctx.blockDim = block;
            ctx.gridDim = grid;
            
            kernel(ctx);
        }
    });
}

// Convenience: 1D launch
template<typename KernelFunc>
void launch_1d(int n, int block_size, KernelFunc kernel) {
    int grid_size = (n + block_size - 1) / block_size;
    launch(Dim3(grid_size), Dim3(block_size), kernel);
}

} // namespace cuda_style
```

### Usage: CUDA-style Code on CPU

```cpp
#include <vector>
#include <cmath>
#include <iostream>

using namespace cuda_style;

int main() {
    const int N = 1000000;
    std::vector<float> a(N, 1.0f);
    std::vector<float> b(N, 2.0f);
    std::vector<float> c(N);
    
    float* d_a = a.data();
    float* d_b = b.data();
    float* d_c = c.data();
    
    // CUDA-style kernel definition
    auto vector_add = [=](const KernelContext& ctx) {
        int i = ctx.global_id();
        if (i < N) {
            d_c[i] = d_a[i] + d_b[i];
        }
    };
    
    // CUDA-style launch
    int block_size = 256;
    int grid_size = (N + block_size - 1) / block_size;
    
    launch(Dim3(grid_size), Dim3(block_size), vector_add);
    
    // Verify
    std::cout << "c[0] = " << c[0] << "\n";  // 3.0
    
    return 0;
}
```

## Advanced CUDA-like Interface

### Full Implementation with Shared Memory Simulation

```cpp
#include <tbb/tbb.h>
#include <vector>
#include <array>
#include <functional>
#include <memory>

namespace gpu_sim {

//==============================================================================
// Dim3 and Context
//==============================================================================
struct Dim3 {
    int x = 1, y = 1, z = 1;
    
    Dim3() = default;
    Dim3(int x_) : x(x_) {}
    Dim3(int x_, int y_) : x(x_), y(y_) {}
    Dim3(int x_, int y_, int z_) : x(x_), y(y_), z(z_) {}
    
    int total() const { return x * y * z; }
};

//==============================================================================
// Shared Memory Simulation
//==============================================================================
template<typename T, size_t Size>
class SharedMemory {
    std::array<T, Size> data_;
public:
    T& operator[](size_t i) { return data_[i]; }
    const T& operator[](size_t i) const { return data_[i]; }
    T* data() { return data_.data(); }
};

//==============================================================================
// Kernel Context (passed to every "thread")
//==============================================================================
struct KernelContext {
    Dim3 threadIdx;
    Dim3 blockIdx;
    Dim3 blockDim;
    Dim3 gridDim;
    
    // Synchronization within block (simulated)
    std::function<void()> __syncthreads;
    
    int global_idx() const {
        return blockIdx.x * blockDim.x + threadIdx.x;
    }
    
    int global_idy() const {
        return blockIdx.y * blockDim.y + threadIdx.y;
    }
    
    int global_idz() const {
        return blockIdx.z * blockDim.z + threadIdx.z;
    }
    
    int flat_global_id() const {
        int gx = global_idx();
        int gy = global_idy();
        int gz = global_idz();
        int gx_dim = gridDim.x * blockDim.x;
        int gy_dim = gridDim.y * blockDim.y;
        return gz * gx_dim * gy_dim + gy * gx_dim + gx;
    }
};

//==============================================================================
// Kernel Launcher
//==============================================================================
class KernelLauncher {
public:
    // 1D Launch
    template<typename Kernel>
    static void launch_1d(int n, int block_size, Kernel kernel) {
        int grid_size = (n + block_size - 1) / block_size;
        launch(Dim3(grid_size), Dim3(block_size), std::move(kernel));
    }
    
    // 2D Launch
    template<typename Kernel>
    static void launch_2d(Dim3 grid, Dim3 block, Kernel kernel) {
        launch(grid, block, std::move(kernel));
    }
    
    // Generic Launch (like <<<grid, block>>>)
    template<typename Kernel>
    static void launch(Dim3 grid, Dim3 block, Kernel kernel) {
        const int total_blocks = grid.total();
        
        // Parallel over blocks
        tbb::parallel_for(0, total_blocks, [&](int block_linear_id) {
            // Decode block index
            Dim3 blockIdx;
            blockIdx.z = block_linear_id / (grid.x * grid.y);
            int remainder = block_linear_id % (grid.x * grid.y);
            blockIdx.y = remainder / grid.x;
            blockIdx.x = remainder % grid.x;
            
            // Execute block (all threads in block run sequentially - simulated)
            execute_block(blockIdx, grid, block, kernel);
        });
    }

private:
    template<typename Kernel>
    static void execute_block(Dim3 blockIdx, Dim3 gridDim, Dim3 blockDim, Kernel& kernel) {
        const int threads_in_block = blockDim.total();
        
        // Barrier for __syncthreads simulation
        tbb::spin_barrier barrier(threads_in_block);
        
        // Run all threads in block in parallel (simulates warp execution)
        tbb::parallel_for(0, threads_in_block, [&](int thread_linear_id) {
            // Decode thread index
            Dim3 threadIdx;
            threadIdx.z = thread_linear_id / (blockDim.x * blockDim.y);
            int remainder = thread_linear_id % (blockDim.x * blockDim.y);
            threadIdx.y = remainder / blockDim.x;
            threadIdx.x = remainder % blockDim.x;
            
            // Build context
            KernelContext ctx;
            ctx.threadIdx = threadIdx;
            ctx.blockIdx = blockIdx;
            ctx.blockDim = blockDim;
            ctx.gridDim = gridDim;
            ctx.__syncthreads = [&barrier]() { barrier.wait(); };
            
            // Execute kernel
            kernel(ctx);
        });
    }
};

//==============================================================================
// Convenience Macros (CUDA-like syntax)
//==============================================================================
#define KERNEL_LAUNCH(kernel, grid, block, ...) \
    gpu_sim::KernelLauncher::launch(grid, block, [=](const gpu_sim::KernelContext& ctx) { \
        kernel(ctx, ##__VA_ARGS__); \
    })

#define KERNEL_LAUNCH_1D(kernel, n, block_size, ...) \
    gpu_sim::KernelLauncher::launch_1d(n, block_size, [=](const gpu_sim::KernelContext& ctx) { \
        kernel(ctx, ##__VA_ARGS__); \
    })

} // namespace gpu_sim
```

### Example: Vector Addition (CUDA-style)

```cpp
#include <iostream>
#include <vector>

using namespace gpu_sim;

// Define kernel (like __global__ void)
void vector_add_kernel(const KernelContext& ctx, 
                       float* a, float* b, float* c, int n) {
    int i = ctx.global_idx();
    if (i < n) {
        c[i] = a[i] + b[i];
    }
}

int main() {
    const int N = 1000000;
    
    std::vector<float> a(N, 1.0f);
    std::vector<float> b(N, 2.0f);
    std::vector<float> c(N);
    
    // CUDA-style launch
    int block_size = 256;
    int grid_size = (N + block_size - 1) / block_size;
    
    KERNEL_LAUNCH(vector_add_kernel, 
                  Dim3(grid_size), Dim3(block_size),
                  a.data(), b.data(), c.data(), N);
    
    std::cout << "c[0] = " << c[0] << "\n";       // 3.0
    std::cout << "c[N-1] = " << c[N-1] << "\n";   // 3.0
    
    return 0;
}
```

### Example: Matrix Multiplication (2D Launch)

```cpp
using namespace gpu_sim;

void matmul_kernel(const KernelContext& ctx,
                   float* A, float* B, float* C,
                   int M, int N, int K) {
    int row = ctx.global_idy();
    int col = ctx.global_idx();
    
    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; ++k) {
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

void matrix_multiply(float* A, float* B, float* C, int M, int N, int K) {
    Dim3 block(16, 16);
    Dim3 grid((N + 15) / 16, (M + 15) / 16);
    
    KERNEL_LAUNCH(matmul_kernel, grid, block, A, B, C, M, N, K);
}
```

### Example: Reduction with Shared Memory

```cpp
using namespace gpu_sim;

// Simulated shared memory per block
thread_local std::vector<float> shared_data;

void reduce_kernel(const KernelContext& ctx, float* input, float* output, int n) {
    // Allocate shared memory (simulated)
    if (ctx.threadIdx.x == 0) {
        shared_data.resize(ctx.blockDim.x, 0.0f);
    }
    ctx.__syncthreads();
    
    // Load to shared memory
    int i = ctx.global_idx();
    shared_data[ctx.threadIdx.x] = (i < n) ? input[i] : 0.0f;
    ctx.__syncthreads();
    
    // Reduction in shared memory
    for (int stride = ctx.blockDim.x / 2; stride > 0; stride >>= 1) {
        if (ctx.threadIdx.x < stride) {
            shared_data[ctx.threadIdx.x] += shared_data[ctx.threadIdx.x + stride];
        }
        ctx.__syncthreads();
    }
    
    // Write result
    if (ctx.threadIdx.x == 0) {
        output[ctx.blockIdx.x] = shared_data[0];
    }
}
```

## Comparison: Same Algorithm in Both Styles

### CUDA Original

```cpp
// CUDA Kernel
__global__ void saxpy_cuda(int n, float a, float* x, float* y) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) {
        y[i] = a * x[i] + y[i];
    }
}

// Launch
int block = 256;
int grid = (n + block - 1) / block;
saxpy_cuda<<<grid, block>>>(n, 2.0f, x, y);
cudaDeviceSynchronize();
```

### TBB Traditional

```cpp
// TBB style
tbb::parallel_for(0, n, [=](int i) {
    y[i] = a * x[i] + y[i];
});
```

### TBB with CUDA-like Interface

```cpp
// CUDA-like kernel
void saxpy_kernel(const KernelContext& ctx, int n, float a, float* x, float* y) {
    int i = ctx.global_idx();
    if (i < n) {
        y[i] = a * x[i] + y[i];
    }
}

// CUDA-like launch
int block = 256;
int grid = (n + block - 1) / block;
KERNEL_LAUNCH(saxpy_kernel, Dim3(grid), Dim3(block), n, 2.0f, x, y);
```

## Why Would You Want This?

| Use Case | Benefit |
|----------|---------|
| **Porting CUDA to CPU** | Minimal code changes |
| **Testing GPU kernels** | Debug on CPU first |
| **Hybrid code** | Same interface for CPU/GPU |
| **Learning** | Understand CUDA model on CPU |
| **Fallback** | Run on machines without GPU |

## Unified CPU/GPU Interface

```cpp
#include <tbb/tbb.h>

namespace unified {

enum class Device { CPU, CUDA };

template<Device D>
class Executor;

// CPU Executor (TBB)
template<>
class Executor<Device::CPU> {
public:
    template<typename Kernel>
    static void launch(Dim3 grid, Dim3 block, Kernel kernel) {
        gpu_sim::KernelLauncher::launch(grid, block, kernel);
    }
};

#ifdef __CUDACC__
// CUDA Executor
template<>
class Executor<Device::CUDA> {
public:
    template<typename Kernel>
    static void launch(Dim3 grid, Dim3 block, Kernel kernel) {
        dim3 cuda_grid(grid.x, grid.y, grid.z);
        dim3 cuda_block(block.x, block.y, block.z);
        kernel<<<cuda_grid, cuda_block>>>();
        cudaDeviceSynchronize();
    }
};
#endif

// Unified launch
template<Device D, typename Kernel>
void launch(Dim3 grid, Dim3 block, Kernel kernel) {
    Executor<D>::launch(grid, block, kernel);
}

} // namespace unified

// Usage:
// unified::launch<unified::Device::CPU>(grid, block, my_kernel);
// unified::launch<unified::Device::CUDA>(grid, block, my_kernel);
```

## Performance Considerations

| Aspect | Real CUDA | TBB CUDA-style |
|--------|-----------|----------------|
| **Parallelism** | 1000s-100000s threads | 10s-100s threads |
| **Thread overhead** | ~0 (hardware) | ~100ns per task |
| **Block simulation** | Hardware SM | TBB task |
| **Shared memory** | Fast SRAM | Regular RAM |
| **__syncthreads** | Hardware barrier | TBB barrier |
| **Memory bandwidth** | ~1 TB/s | ~100 GB/s |
| **Use case** | Production GPU | Testing/Porting |

## Libraries That Already Do This

### 1. SYCL / DPC++

```cpp
#include <CL/sycl.hpp>

sycl::queue q;

q.parallel_for(sycl::range<1>(N), [=](sycl::id<1> i) {
    c[i] = a[i] + b[i];
}).wait();

// Works on CPU, GPU, FPGA!
```

### 2. Kokkos

```cpp
#include <Kokkos_Core.hpp>

Kokkos::parallel_for(N, KOKKOS_LAMBDA(int i) {
    c[i] = a[i] + b[i];
});

// Compiles for CPU (OpenMP/TBB) or GPU (CUDA/HIP)
```

### 3. RAJA

```cpp
#include <RAJA/RAJA.hpp>

RAJA::forall<RAJA::cuda_exec<256>>(
    RAJA::RangeSegment(0, N),
    [=] RAJA_DEVICE (int i) {
        c[i] = a[i] + b[i];
    }
);

// Change policy for CPU: RAJA::omp_parallel_for_exec
```

### 4. Thrust (CUDA's STL)

```cpp
#include <thrust/device_vector.h>
#include <thrust/transform.h>

thrust::device_vector<float> a(N), b(N), c(N);

thrust::transform(a.begin(), a.end(), b.begin(), c.begin(),
    thrust::plus<float>());

// Also works on CPU with thrust::host_vector
```

## Summary

| Question | Answer |
|----------|--------|
| Is CUDA multi-entry? | Yes, multiple `__global__` kernels |
| Is TBB single-entry? | Yes, single process with parallel regions |
| Can TBB have CUDA-like interface? | ✅ Yes, via wrapper |
| Should you use wrapper? | For porting/testing, yes |
| For new code? | Use native TBB or Kokkos/SYCL |
| Performance equivalent? | ❌ No, CPU is slower than GPU |

### Recommendation

| Goal | Approach |
|------|----------|
| **Port CUDA to CPU** | Custom wrapper or Kokkos |
| **Write portable code** | SYCL, Kokkos, or RAJA |
| **CPU only** | Native TBB (simpler) |
| **Test GPU kernels** | Custom wrapper for debugging |
| **Production hybrid** | SYCL or Kokkos |
