// inline_ptx.cu - Basic inline PTX operations
// Demonstrates inline PTX assembly for arithmetic, bit manipulation, and memory operations

#ifndef INLINE_PTX_CU
#define INLINE_PTX_CU

// ============================================================================
// Arithmetic Operations
// ============================================================================

__device__ int add_ptx(int a, int b) {
    int result;
    asm("add.s32 %0, %1, %2;"
        : "=r"(result)
        : "r"(a), "r"(b)
    );
    return result;
}

__device__ float fma_ptx(float a, float b, float c) {
    float result;
    // Fused multiply-add: result = a * b + c
    asm("fma.rn.f32 %0, %1, %2, %3;"
        : "=f"(result)
        : "f"(a), "f"(b), "f"(c)
    );
    return result;
}

__device__ int popc_ptx(unsigned int x) {
    int result;
    // Population count (count set bits)
    asm("popc.b32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}

__device__ int bfind_ptx(unsigned int x) {
    int result;
    // Find first set bit (most significant)
    asm("bfind.u32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}

// ============================================================================
// Bit Manipulation
// ============================================================================

__device__ int reverse_bits_ptx(int x) {
    int result;
    // Reverse all 32 bits
    asm("brev.b32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}

__device__ int byte_perm_ptx(int a, int b, int selector) {
    int result;
    // Arbitrary byte permutation
    asm("prmt.b32 %0, %1, %2, %3;"
        : "=r"(result)
        : "r"(a), "r"(b), "r"(selector)
    );
    return result;
}

__device__ unsigned int clz_ptx(unsigned int x) {
    unsigned int result;
    // Count leading zeros
    asm("clz.b32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}

// ============================================================================
// Memory Operations
// ============================================================================

__device__ void prefetch_l1_ptx(const void* ptr) {
    // Prefetch data into L1 cache
    asm volatile("prefetch.global.L1 [%0];"
        :
        : "l"(ptr)
    );
}

__device__ void prefetch_l2_ptx(const void* ptr) {
    // Prefetch data into L2 cache
    asm volatile("prefetch.global.L2 [%0];"
        :
        : "l"(ptr)
    );
}

__device__ float load_streaming_ptx(const float* src) {
    float val;
    // Load with streaming cache hint (cache at global level only)
    asm("ld.global.cs.f32 %0, [%1];"
        : "=f"(val)
        : "l"(src)
    );
    return val;
}

__device__ void store_streaming_ptx(float* dst, float val) {
    // Store with streaming cache hint
    asm volatile("st.global.cs.f32 [%0], %1;"
        :
        : "l"(dst), "f"(val)
    );
}

__device__ int load_volatile_ptx(const int* addr) {
    int result;
    // Volatile load ensures fresh read
    asm volatile("ld.global.volatile.s32 %0, [%1];"
        : "=r"(result)
        : "l"(addr)
    );
    return result;
}

__device__ void store_volatile_ptx(int* addr, int val) {
    // Volatile store ensures immediate write
    asm volatile("st.global.volatile.s32 [%0], %1;"
        :
        : "l"(addr), "r"(val)
    );
}

// ============================================================================
// Test Kernels (for unit testing)
// ============================================================================

__global__ void test_add_kernel(int* result, int a, int b) {
    *result = add_ptx(a, b);
}

__global__ void test_fma_kernel(float* result, float a, float b, float c) {
    *result = fma_ptx(a, b, c);
}

__global__ void test_popc_kernel(int* result, unsigned int val) {
    *result = popc_ptx(val);
}

__global__ void test_bfind_kernel(int* result, unsigned int val) {
    *result = bfind_ptx(val);
}

__global__ void test_reverse_bits_kernel(int* result, int val) {
    *result = reverse_bits_ptx(val);
}

__global__ void test_clz_kernel(unsigned int* result, unsigned int val) {
    *result = clz_ptx(val);
}

#endif // INLINE_PTX_CU
