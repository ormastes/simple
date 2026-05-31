/*
 * SIMD Dispatch — compilation unit for dispatch table support.
 * The text dispatch table (g_simd_text) and init are in runtime_simd_utf8.c.
 * The crypto dispatch table (g_simd_crypto) is defined here with scalar stubs.
 */
#include "runtime_simd_dispatch.h"
#include "runtime.h"

#if defined(__x86_64__) || defined(_M_X64)
#  include <immintrin.h>
#endif

#if !defined(_WIN32)
#  include <dlfcn.h>
#endif

typedef int (*rt_opencl_get_platform_ids_fn)(uint32_t, void*, uint32_t*);

static rt_opencl_get_platform_ids_fn rt_opencl_get_platform_ids_symbol(void) {
#if defined(_WIN32)
    return NULL;
#else
    static void* opencl_handle = NULL;
    static rt_opencl_get_platform_ids_fn symbol = NULL;
    static int attempted = 0;
    if (attempted) return symbol;
    attempted = 1;
    opencl_handle = dlopen("libOpenCL.so.1", RTLD_LAZY | RTLD_LOCAL);
    if (!opencl_handle) {
        opencl_handle = dlopen("libOpenCL.so", RTLD_LAZY | RTLD_LOCAL);
    }
    if (!opencl_handle) return NULL;
    symbol = (rt_opencl_get_platform_ids_fn)dlsym(opencl_handle, "clGetPlatformIDs");
    return symbol;
#endif
}

int64_t rt_opencl_platform_count(void) {
    rt_opencl_get_platform_ids_fn get_platform_ids = rt_opencl_get_platform_ids_symbol();
    if (!get_platform_ids) return 0;
    uint32_t count = 0;
    int status = get_platform_ids(0, NULL, &count);
    if (status != 0) return 0;
    return (int64_t)count;
}

bool rt_opencl_is_available(void) {
    return rt_opencl_platform_count() > 0;
}

int64_t rt_opencl_create_context(int64_t platform) {
    (void)platform;
    return 0;
}

int64_t rt_opencl_create_queue(int64_t context) {
    (void)context;
    return 0;
}

int64_t rt_opencl_create_program(int64_t context, const char* source) {
    (void)context;
    (void)source;
    return 0;
}

bool rt_opencl_build_program(int64_t program) {
    (void)program;
    return false;
}

int64_t rt_opencl_create_kernel(int64_t program, const char* name) {
    (void)program;
    (void)name;
    return 0;
}

bool rt_opencl_enqueue_ndrange(int64_t queue, int64_t kernel, int64_t gx, int64_t gy, int64_t gz, int64_t lx, int64_t ly, int64_t lz) {
    (void)queue;
    (void)kernel;
    (void)gx;
    (void)gy;
    (void)gz;
    (void)lx;
    (void)ly;
    (void)lz;
    return false;
}

bool rt_opencl_finish(int64_t queue) {
    (void)queue;
    return false;
}

static inline int64_t engine2d_numeric_arg(int64_t value) {
    uint64_t raw = (uint64_t)value;
    if ((raw & RT_VALUE_TAG_MASK_SIMD) == 0 && raw >= 8) {
        return (int64_t)(raw >> 3);
    }
    return value;
}

static int engine2d_span_bounds(SplArray* array, int64_t offset, int64_t count,
                                int64_t* out_offset, int64_t* out_count) {
    if (!array || !out_offset || !out_count) return 0;
    int64_t len = rt_array_len(array);
    offset = engine2d_numeric_arg(offset);
    count = engine2d_numeric_arg(count);
    if (offset < 0 || count <= 0 || offset >= len) return 0;
    if (count > len - offset) count = len - offset;
    *out_offset = offset;
    *out_count = count;
    return count > 0;
}

#if defined(__x86_64__) || defined(_M_X64)
__attribute__((target("avx2")))
static void engine2d_fill_u32_avx2(int64_t* data, int64_t count, int64_t color) {
    __m256i v = _mm256_set1_epi64x(color);
    int64_t i = 0;
    for (; i + 4 <= count; i += 4) {
        _mm256_storeu_si256((__m256i*)(void*)(data + i), v);
    }
    for (; i < count; i++) {
        data[i] = color;
    }
}

__attribute__((target("avx2")))
static void engine2d_copy_u32_avx2(int64_t* dst, const int64_t* src, int64_t count) {
    int64_t i = 0;
    for (; i + 4 <= count; i += 4) {
        __m256i v = _mm256_loadu_si256((const __m256i*)(const void*)(src + i));
        _mm256_storeu_si256((__m256i*)(void*)(dst + i), v);
    }
    for (; i < count; i++) {
        dst[i] = src[i];
    }
}
#endif

int64_t rt_engine2d_simd_fill_u32(SplArray* dst, int64_t offset, int64_t count, int64_t color) {
    int64_t off = 0;
    int64_t n = 0;
    if (!engine2d_span_bounds(dst, offset, count, &off, &n)) return 0;

    int64_t* data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    if (!data) return 0;
    int64_t color_word = engine2d_numeric_arg(color) & 0xffffffffLL;

#if defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        engine2d_fill_u32_avx2(data + off, n, color_word);
        return n;
    }
#endif

    for (int64_t i = 0; i < n; i++) {
        data[off + i] = color_word;
    }
    return n;
}

int64_t rt_engine2d_simd_copy_u32(SplArray* dst, int64_t dst_off, SplArray* src,
                                  int64_t src_off, int64_t count) {
    int64_t d_off = 0;
    int64_t n = 0;
    if (!engine2d_span_bounds(dst, dst_off, count, &d_off, &n)) return 0;

    int64_t s_off = 0;
    int64_t src_n = 0;
    if (!engine2d_span_bounds(src, src_off, n, &s_off, &src_n)) return 0;
    if (src_n < n) n = src_n;

    int64_t* dst_data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    const int64_t* src_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    if (!dst_data || !src_data || n <= 0) return 0;

#if defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        engine2d_copy_u32_avx2(dst_data + d_off, src_data + s_off, n);
        return n;
    }
#endif

    memmove(dst_data + d_off, src_data + s_off, (size_t)n * sizeof(int64_t));
    return n;
}

/* Scalar fallback stubs — no-op placeholders until pure Simple or
   hardware-accelerated implementations are wired in. */

static void scalar_aes_encrypt_block(const uint8_t* in, uint8_t* out,
                                     const uint8_t* round_keys, int rounds) {
    (void)in; (void)out; (void)round_keys; (void)rounds;
}

static void scalar_aes_decrypt_block(const uint8_t* in, uint8_t* out,
                                     const uint8_t* round_keys, int rounds) {
    (void)in; (void)out; (void)round_keys; (void)rounds;
}

static void scalar_sha256_compress(uint32_t state[8], const uint8_t* block) {
    (void)state; (void)block;
}

static void scalar_chacha20_block(uint32_t out[16], const uint32_t in[16]) {
    (void)out; (void)in;
}

static uint32_t scalar_crc32_update(uint32_t crc, const uint8_t* data, uint64_t len) {
    (void)data; (void)len;
    return crc;
}

static void scalar_ghash_multiply(uint8_t* result, const uint8_t* h, const uint8_t* x) {
    (void)result; (void)h; (void)x;
}

SimdCryptoDispatch g_simd_crypto = {
    .aes_encrypt_block = scalar_aes_encrypt_block,
    .aes_decrypt_block = scalar_aes_decrypt_block,
    .sha256_compress   = scalar_sha256_compress,
    .chacha20_block    = scalar_chacha20_block,
    .crc32_update      = scalar_crc32_update,
    .ghash_multiply    = scalar_ghash_multiply,
};

void simd_crypto_init(void) {
    /* Detect hardware crypto extensions and upgrade function pointers.
       AES-NI, SHA-NI, and PCLMULQDQ implementations will be added as
       separate TUs (runtime_simd_aesni.c, runtime_simd_shani.c, etc.)
       and wired in here when available. */
}
