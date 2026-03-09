// ptx_atomics.cu - Atomic operations with PTX
// Demonstrates fine-grained control over atomic operations using inline PTX

#ifndef PTX_ATOMICS_CU
#define PTX_ATOMICS_CU

// ============================================================================
// Basic Atomic Operations
// ============================================================================

__device__ int atomic_add_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.global.add.s32 %0, [%1], %2;"
        : "=r"(old)
        : "l"(addr), "r"(val)
        : "memory"
    );
    return old;
}

__device__ int atomic_min_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.global.min.s32 %0, [%1], %2;"
        : "=r"(old)
        : "l"(addr), "r"(val)
        : "memory"
    );
    return old;
}

__device__ int atomic_max_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.global.max.s32 %0, [%1], %2;"
        : "=r"(old)
        : "l"(addr), "r"(val)
        : "memory"
    );
    return old;
}

// ============================================================================
// Compare-and-Swap (CAS)
// ============================================================================

__device__ int atomic_cas_ptx(int* addr, int compare, int val) {
    int old;
    asm volatile("atom.global.cas.b32 %0, [%1], %2, %3;"
        : "=r"(old)
        : "l"(addr), "r"(compare), "r"(val)
        : "memory"
    );
    return old;
}

// Lock-free increment using CAS
__device__ int atomic_inc_lock_free_ptx(int* addr, int limit) {
    int old, assumed;
    do {
        assumed = *addr;
        old = atomic_cas_ptx(addr, assumed, (assumed >= limit - 1) ? 0 : (assumed + 1));
    } while (assumed != old);
    return old;
}

// ============================================================================
// Shared Memory Atomics
// ============================================================================

__device__ int atomic_add_shared_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.shared.add.s32 %0, [%1], %2;"
        : "=r"(old)
        : "r"(addr), "r"(val)  // Note: "r" not "l" for shared memory
        : "memory"
    );
    return old;
}

// ============================================================================
// 64-bit Atomics
// ============================================================================

__device__ unsigned long long atomic_add_u64_ptx(unsigned long long* addr,
                                                  unsigned long long val) {
    unsigned long long old;
    asm volatile("atom.global.add.u64 %0, [%1], %2;"
        : "=l"(old)
        : "l"(addr), "l"(val)
        : "memory"
    );
    return old;
}

__device__ unsigned long long atomic_cas_u64_ptx(unsigned long long* addr,
                                                   unsigned long long compare,
                                                   unsigned long long val) {
    unsigned long long old;
    asm volatile("atom.global.cas.b64 %0, [%1], %2, %3;"
        : "=l"(old)
        : "l"(addr), "l"(compare), "l"(val)
        : "memory"
    );
    return old;
}

// ============================================================================
// Test Kernels
// ============================================================================

__global__ void atomic_add_kernel(int* counter, int val) {
    atomic_add_ptx(counter, val);
}

__global__ void atomic_min_kernel(int* global_min, int val) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    atomic_min_ptx(global_min, val + idx);
}

__global__ void atomic_max_kernel(int* global_max, int val) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    atomic_max_ptx(global_max, val + idx);
}

__global__ void atomic_cas_inc_kernel(int* value, int limit) {
    atomic_inc_lock_free_ptx(value, limit);
}

__global__ void atomic_add_shared_kernel(int* result) {
    __shared__ int shared_counter;

    if (threadIdx.x == 0) {
        shared_counter = 0;
    }
    __syncthreads();

    // Each thread atomically adds 1 to shared memory
    atomic_add_shared_ptx(&shared_counter, 1);
    __syncthreads();

    // Write result to global memory
    if (threadIdx.x == 0) {
        *result = shared_counter;
    }
}

__global__ void atomic_add_u64_kernel(unsigned long long* counter, unsigned long long val) {
    atomic_add_u64_ptx(counter, val);
}

// Histogram using atomics
__global__ void histogram_kernel(int* histogram, const int* data, int n, int num_bins) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int bin = data[idx] % num_bins;
        atomic_add_ptx(&histogram[bin], 1);
    }
}

#endif // PTX_ATOMICS_CU
