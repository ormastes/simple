/*
 * SIMD Text Dispatch — shared header for runtime_simd_*.c files
 *
 * Provides:
 *   - CPU feature detection (cpuid for x86_64, getauxval for ARM)
 *   - SimdTextDispatch function-pointer table
 *   - Platform detection macros (SSE2/AVX2/NEON)
 *   - RtCoreString typedef + tag helpers (duplicated from runtime_native.c
 *     so each TU gets its own static-inline copy without symbol conflicts)
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. file.c
 */

#ifndef RUNTIME_SIMD_DISPATCH_H
#define RUNTIME_SIMD_DISPATCH_H

#include <stdint.h>
#include <stddef.h>
#include <string.h>

/* ================================================================
 * Platform Detection Macros
 * ================================================================ */

/* x86_64 SSE2 — guaranteed on all x86-64 */
#if defined(__x86_64__) || defined(_M_X64)
#  define SIMD_HAS_X86 1
#  define SIMD_HAS_SSE2 1
#else
#  define SIMD_HAS_X86 0
#  define SIMD_HAS_SSE2 0
#endif

/* x86_64 AVX2 — runtime-detected via cpuid */
#if defined(__x86_64__) || defined(_M_X64)
#  define SIMD_CAN_AVX2 1
#else
#  define SIMD_CAN_AVX2 0
#endif

/* ARM NEON — compile-time on aarch64, runtime on armv7 */
#if defined(__aarch64__) || defined(_M_ARM64)
#  define SIMD_HAS_NEON 1
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
#  define SIMD_HAS_NEON 1
#else
#  define SIMD_HAS_NEON 0
#endif

/* ================================================================
 * CPU Feature Detection
 * ================================================================ */

#if SIMD_HAS_X86
#  if defined(__GNUC__) || defined(__clang__)
#    include <cpuid.h>
#  elif defined(_MSC_VER)
#    include <intrin.h>
#  endif
#endif

#if defined(__linux__) && (defined(__arm__) || defined(__aarch64__))
#  include <sys/auxv.h>
#  ifndef HWCAP_NEON
#    define HWCAP_NEON (1 << 12)
#  endif
#endif

static inline int simd_detect_avx2(void) {
#if SIMD_CAN_AVX2
#  if defined(__GNUC__) || defined(__clang__)
    unsigned int eax, ebx, ecx, edx;
    /* Check OSXSAVE (cpuid leaf 1, ecx bit 27) */
    if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx)) return 0;
    if (!(ecx & (1U << 27))) return 0; /* OSXSAVE not set */
    /* Check AVX2 (cpuid leaf 7, sub-leaf 0, ebx bit 5) */
    if (!__get_cpuid_count(7, 0, &eax, &ebx, &ecx, &edx)) return 0;
    return (ebx & (1U << 5)) ? 1 : 0;
#  elif defined(_MSC_VER)
    int info[4];
    __cpuidex(info, 7, 0);
    return (info[1] & (1 << 5)) ? 1 : 0;
#  else
    return 0;
#  endif
#else
    return 0;
#endif
}

static inline int simd_detect_neon(void) {
#if defined(__aarch64__) || defined(_M_ARM64)
    return 1; /* NEON is mandatory on aarch64 */
#elif defined(__linux__) && defined(__arm__)
    unsigned long hwcap = getauxval(AT_HWCAP);
    return (hwcap & HWCAP_NEON) ? 1 : 0;
#else
    return 0;
#endif
}

/* ================================================================
 * RtCoreString — duplicated from runtime_native.c for TU isolation
 * ================================================================ */

#define RT_VALUE_TAG_MASK_SIMD       0x7ULL
#define RT_VALUE_TAG_HEAP_SIMD       0x1ULL
#define RT_VALUE_HEAP_STRING_SIMD    0x53545231U

typedef struct RtCoreStringSimd {
    uint32_t kind;
    uint32_t reserved;
    uint64_t len;
    char data[];
} RtCoreStringSimd;

static inline RtCoreStringSimd* simd_as_string(int64_t value) {
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK_SIMD) != RT_VALUE_TAG_HEAP_SIMD)
        return NULL;
    RtCoreStringSimd* s = (RtCoreStringSimd*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK_SIMD);
    if (!s || s->kind != RT_VALUE_HEAP_STRING_SIMD) return NULL;
    return s;
}

/* ================================================================
 * Reserved-Field Cache Bit Layout
 *
 *   Bits [31:30] = flags:
 *     00 = uncached
 *     01 = codepoint-count cached
 *     10 = is-ASCII flag set (value in bit 29)
 *     11 = both cached
 *   Bits [29:0]  = codepoint count (max ~1 billion)
 *
 * Bit 31 = "is-ASCII known" flag
 * Bit 30 = "cp-count known" flag
 * Bit 29 = ASCII value (1=all-ASCII, 0=not all-ASCII) when bit 31 set
 * Bits [28:0] = codepoint count when bit 30 set (max ~536 million)
 *
 * Revised layout (cleaner separation):
 *   Bit 31     = is-ASCII validity flag
 *   Bit 30     = cp-count validity flag
 *   Bit 29     = is-ASCII value (meaningful only when bit 31 = 1)
 *   Bits [28:0] = codepoint count (meaningful only when bit 30 = 1)
 * ================================================================ */

#define SIMD_CACHE_FLAG_ASCII_VALID   (1U << 31)
#define SIMD_CACHE_FLAG_CPCOUNT_VALID (1U << 30)
#define SIMD_CACHE_FLAG_ASCII_VALUE   (1U << 29)
#define SIMD_CACHE_CPCOUNT_MASK       0x1FFFFFFFU  /* bits [28:0] */

/* ================================================================
 * SimdTextDispatch — function-pointer table for text operations
 * ================================================================ */

typedef struct {
    int64_t (*utf8_count_codepoints)(const uint8_t*, uint64_t);
    int     (*utf8_validate)(const uint8_t*, uint64_t);
    int64_t (*utf8_find_invalid)(const uint8_t*, uint64_t);
    int64_t (*str_search)(const uint8_t*, uint64_t, const uint8_t*, uint64_t);
    int     (*is_ascii)(const uint8_t*, uint64_t);
    void    (*to_upper_ascii)(const uint8_t*, uint8_t*, uint64_t);
    void    (*to_lower_ascii)(const uint8_t*, uint8_t*, uint64_t);
    int     (*str_equal)(const uint8_t*, uint64_t, const uint8_t*, uint64_t);
} SimdTextDispatch;

extern SimdTextDispatch g_simd_text;

void simd_text_init(void);

#endif /* RUNTIME_SIMD_DISPATCH_H */
