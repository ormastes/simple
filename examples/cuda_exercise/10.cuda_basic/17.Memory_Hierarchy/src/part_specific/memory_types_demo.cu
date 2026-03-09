// memory_types_demo.cu - Comprehensive demonstration of all CUDA memory types
// Shows both explicit and implicit usage of each memory type
#include <cuda_runtime.h>
#include <stdio.h>
#include "cuda_utils.h"  // From CudaCustomLib, via CMake target_link_libraries

// ============================================================================
// 1. REGISTERS - Implicit and Explicit Usage
// ============================================================================

// 1.1 IMPLICIT: Compiler automatically uses registers for local variables
__global__ void register_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // These local variables are automatically stored in registers
        float temp1 = input[idx];
        float temp2 = temp1 * 2.0f;
        float temp3 = temp2 + 1.0f;
        output[idx] = temp3;
    }
}

// 1.2 EXPLICIT: Using register keyword (hint to compiler, though usually automatic)
__global__ void register_explicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Explicit register hint (mostly informational in modern CUDA)
        register float temp1 = input[idx];
        register float temp2 = temp1 * 2.0f;
        register float temp3 = temp2 + 1.0f;
        output[idx] = temp3;
    }
}

// 1.3 EXPLICIT: Loop unrolling to maximize register usage
__global__ void register_unrolled(const float* input, float* output, int N) {
    int idx = (blockIdx.x * blockDim.x + threadIdx.x) * 4;

    // Explicitly keep multiple values in registers
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

// ============================================================================
// 2. SHARED MEMORY - Explicit Usage Only
// ============================================================================

// 2.1 EXPLICIT: Static shared memory allocation
__global__ void shared_static(const float* input, float* output, int N) {
    // Explicitly declared shared memory with fixed size
    __shared__ float sdata[256];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load to shared memory
    if (idx < N) {
        sdata[tid] = input[idx];
    }
    __syncthreads();

    // Use shared memory
    if (idx < N) {
        output[idx] = sdata[tid] * 2.0f;
    }
}

// 2.2 EXPLICIT: Dynamic shared memory allocation
__global__ void shared_dynamic(const float* input, float* output, int N) {
    // Explicitly declared dynamic shared memory (size specified at launch)
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load to shared memory
    if (idx < N) {
        sdata[tid] = input[idx];
    }
    __syncthreads();

    // Use shared memory
    if (idx < N) {
        output[idx] = sdata[tid] * 2.0f;
    }
}

// 2.3 EXPLICIT: Bank conflict-free shared memory with padding
__global__ void shared_padded(const float* input, float* output, int N) {
    // Explicit padding to avoid bank conflicts
    __shared__ float sdata[32][32 + 1];  // +1 for padding

    int tx = threadIdx.x;
    int ty = threadIdx.y;
    int idx = (blockIdx.y * blockDim.y + ty) * N + (blockIdx.x * blockDim.x + tx);

    if (blockIdx.x * blockDim.x + tx < N && blockIdx.y * blockDim.y + ty < N) {
        sdata[ty][tx] = input[idx];
        __syncthreads();
        output[idx] = sdata[ty][tx] * 2.0f;
    }
}

// ============================================================================
// 3. CONSTANT MEMORY - Explicit Usage Only
// ============================================================================

// 3.1 EXPLICIT: Constant memory declaration (must be at file scope)
__constant__ float const_coefficients[16];
__constant__ float const_scalar;

// 3.2 EXPLICIT: Using constant memory (efficient when all threads read same value)
__global__ void constant_explicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Efficiently broadcast to all threads
        float result = input[idx] * const_scalar;

        // Using array in constant memory
        for (int i = 0; i < 16; i++) {
            result += const_coefficients[i];
        }

        output[idx] = result;
    }
}

// ============================================================================
// 4. TEXTURE MEMORY - Explicit Usage Only
// ============================================================================

// 4.1 EXPLICIT: 1D texture memory using texture objects (modern API)
__global__ void texture_1d_explicit(cudaTextureObject_t texObj, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Explicit texture fetch with automatic caching
        float value = tex1Dfetch<float>(texObj, idx);
        output[idx] = value * 2.0f;
    }
}

// 4.2 EXPLICIT: 2D texture memory for spatial data
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

// 4.3 EXPLICIT: Texture with normalized coordinates
__global__ void texture_normalized(cudaTextureObject_t texObj, float* output,
                                   int width, int height) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x < width && y < height) {
        // Normalized coordinates [0.0, 1.0]
        float u = (float)x / (float)width;
        float v = (float)y / (float)height;
        float value = tex2D<float>(texObj, u, v);
        output[y * width + x] = value * 2.0f;
    }
}

// ============================================================================
// 5. GLOBAL MEMORY - Implicit and Explicit Usage
// ============================================================================

// 5.1 IMPLICIT: Global memory through function parameters (most common)
__global__ void global_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Pointers automatically point to global memory
        output[idx] = input[idx] * 2.0f;
    }
}

// 5.2 EXPLICIT: Global memory with __device__ variables
__device__ float global_device_var[1024];

__global__ void global_explicit_device() {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < 1024) {
        // Explicitly using global device variable
        global_device_var[idx] = idx * 2.0f;
    }
}

// 5.3 EXPLICIT: Coalesced global memory access
__global__ void global_coalesced(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // Consecutive threads access consecutive memory (coalesced)
        float value = input[idx];  // Coalesced load
        output[idx] = value * 2.0f;  // Coalesced store
    }
}

// 5.4 EXPLICIT: Strided global memory access (poor performance)
__global__ void global_strided(const float* input, float* output, int N, int stride) {
    int idx = (blockIdx.x * blockDim.x + threadIdx.x) * stride;
    if (idx < N) {
        // Strided access - poor coalescing, for demonstration
        output[idx] = input[idx] * 2.0f;
    }
}

// ============================================================================
// 6. L1 CACHE - Implicit Usage (Hardware Managed)
// ============================================================================

// 6.1 IMPLICIT: L1 cache automatically caches global/local memory
__global__ void l1_cache_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // L1 automatically caches these global memory accesses
        float value = input[idx];
        output[idx] = value * 2.0f;
    }
}

// 6.2 EXPLICIT: Control L1 cache preference via compilation flags or API
// Note: This function itself doesn't show explicit control, but can be configured via:
// - cudaDeviceSetCacheConfig(cudaFuncCachePreferL1) for more L1 cache
// - cudaDeviceSetCacheConfig(cudaFuncCachePreferShared) for less L1, more shared
__global__ void l1_cache_prefer_l1(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // With cudaFuncCachePreferL1, this benefits from larger L1 cache
        float value = input[idx];
        output[idx] = value * 2.0f;
    }
}

// ============================================================================
// 7. L2 CACHE - Implicit and Explicit Usage
// ============================================================================

// 7.1 IMPLICIT: L2 cache automatically caches all global memory
__global__ void l2_cache_implicit(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // L2 automatically caches these accesses across all SMs
        output[idx] = input[idx] * 2.0f;
    }
}

// 7.2 EXPLICIT: L2 persistent cache (Ampere+ architecture)
// This requires CUDA 11.0+ and Ampere or newer GPU
#if __CUDA_ARCH__ >= 800
__global__ void l2_cache_persistent(const float* input, float* output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        // With L2 persistence policy set via cudaDeviceSetLimit,
        // frequently accessed data stays in L2
        output[idx] = input[idx] * 2.0f;
    }
}
#endif

// ============================================================================
// Host-side helper functions for demonstrating explicit memory management
// ============================================================================

// Helper to set constant memory from host
void set_constant_memory_demo(float scalar, const float* coeffs, int coeff_size) {
    cudaMemcpyToSymbol(const_scalar, &scalar, sizeof(float));
    cudaMemcpyToSymbol(const_coefficients, coeffs, coeff_size * sizeof(float));
}

// Helper to create 1D texture object
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

// Helper to create 2D texture object
cudaTextureObject_t create_texture_2d(cudaArray_t array) {
    cudaResourceDesc resDesc;
    memset(&resDesc, 0, sizeof(resDesc));
    resDesc.resType = cudaResourceTypeArray;
    resDesc.res.array.array = array;

    cudaTextureDesc texDesc;
    memset(&texDesc, 0, sizeof(texDesc));
    texDesc.addressMode[0] = cudaAddressModeClamp;
    texDesc.addressMode[1] = cudaAddressModeClamp;
    texDesc.filterMode = cudaFilterModePoint;
    texDesc.readMode = cudaReadModeElementType;
    texDesc.normalizedCoords = 0;

    cudaTextureObject_t texObj = 0;
    cudaCreateTextureObject(&texObj, &resDesc, &texDesc, nullptr);
    return texObj;
}

// Helper to configure L1/shared memory partition
void configure_l1_cache(cudaFuncCache preference) {
    // Set device-wide cache preference
    cudaDeviceSetCacheConfig(preference);

    // Or per-kernel:
    // cudaFuncSetCacheConfig(kernel_name, cudaFuncCachePreferL1);
    // cudaFuncSetCacheConfig(kernel_name, cudaFuncCachePreferShared);
    // cudaFuncSetCacheConfig(kernel_name, cudaFuncCachePreferEqual);
}
