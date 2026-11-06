/*
 * ASCII Case Operations — is_ascii, to_upper, to_lower
 *
 * Portable scalar baseline only. The SSE2/AVX2/NEON kernels moved to the
 * levelled vector provider (providers/vector/text_level_kernels.c, opcodes
 * SIMPLE_VECTOR_TEXT_ASCII_*); when runtime_simd_utf8.c admitted it, spans of
 * at least SIMD_TEXT_PROVIDER_MIN_BYTES route there, otherwise scalar.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_case.c
 */

#include "runtime_simd_dispatch.h"
#include "simple_vector_kernel_abi_v1.h"
#include <stdlib.h>
#include <stdatomic.h>

/* unused: MSVC does not warn about an unreferenced static, so there is nothing
 * to suppress; GCC/Clang keep the attribute. */
#if defined(__GNUC__) || defined(__clang__)
#define RT_SIMD_UNUSED __attribute__((unused))
#else
#define RT_SIMD_UNUSED
#endif

/* ================================================================
 * Reserved-Field ASCII Cache Helpers
 * ================================================================ */

RT_SIMD_UNUSED static inline void cache_ascii_flag(RtCoreStringSimd* s, int is_ascii) {
    if (!s) return;
    if (is_ascii)
        s->reserved |= SIMD_CACHE_FLAG_IS_ASCII;
    /* Non-ASCII: don't cache (positive-only flag per spec) */
}

RT_SIMD_UNUSED static inline int cached_ascii_flag(const RtCoreStringSimd* s) {
    if (!s) return -1;
    if (s->reserved & SIMD_CACHE_FLAG_IS_ASCII) return 1;
    return -1; /* unknown (could be ASCII or not) */
}

/* ================================================================
 * Scalar Kernels
 * ================================================================ */

static int scalar_is_ascii(const uint8_t* data, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

static void scalar_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'A' && c <= 'Z')
            dst[i] = c | 0x20;
        else
            dst[i] = c;
    }
}

static void scalar_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        uint8_t c = src[i];
        if (c >= 'a' && c <= 'z')
            dst[i] = c & 0xDF;
        else
            dst[i] = c;
    }
}

/* ================================================================
 * Provider-routed kernels (scalar for short spans or any refusal)
 * ================================================================ */

RT_SIMD_UNUSED static int routed_is_ascii(const uint8_t* data, uint64_t len) {
    int64_t r;
    if (len >= SIMD_TEXT_PROVIDER_MIN_BYTES &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_ASCII_CHECK, data, len, NULL, 0, NULL, &r))
        return r == 1;
    return scalar_is_ascii(data, len);
}

RT_SIMD_UNUSED static void routed_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    int64_t r;
    if (len >= SIMD_TEXT_PROVIDER_MIN_BYTES &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_ASCII_LOWER, src, len, NULL, 0, dst, &r))
        return;
    scalar_to_lower_ascii(src, dst, len);
}

RT_SIMD_UNUSED static void routed_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    int64_t r;
    if (len >= SIMD_TEXT_PROVIDER_MIN_BYTES &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_ASCII_UPPER, src, len, NULL, 0, dst, &r))
        return;
    scalar_to_upper_ascii(src, dst, len);
}

/* ================================================================
 * Dispatch Slot Upgrade — first use by the opt-in case provider only
 * ================================================================ */

RT_SIMD_UNUSED static void simd_case_init(void) {
    static atomic_int state = ATOMIC_VAR_INIT(0);
    if (atomic_load_explicit(&state, memory_order_acquire) == 2) return;
    int expected = 0;
    if (!atomic_compare_exchange_strong_explicit(&state, &expected, 1,
            memory_order_acquire, memory_order_acquire)) {
        while (atomic_load_explicit(&state, memory_order_acquire) != 2) {}
        return;
    }
    /* Ensure base dispatch table (and provider admission) is done first */
    simd_text_init();

    /* Our scalar kernels avoid the locale-dependent toupper/tolower from
     * <ctype.h> used in the dispatch-table defaults. */
    g_simd_text.is_ascii       = scalar_is_ascii;
    g_simd_text.to_lower_ascii = scalar_to_lower_ascii;
    g_simd_text.to_upper_ascii = scalar_to_upper_ascii;
    if (simd_text_provider_level() > 0) {
        g_simd_text.is_ascii       = routed_is_ascii;
        g_simd_text.to_lower_ascii = routed_to_lower_ascii;
        g_simd_text.to_upper_ascii = routed_to_upper_ascii;
    }
    atomic_store_explicit(&state, 2, memory_order_release);
}

/* ================================================================
 * rt_* Public API
 * ================================================================ */

/*
 * OPT-IN, DEFAULT OFF — resolves a hard duplicate-symbol conflict.
 *
 * runtime_native.c also defines rt_text_is_ascii / rt_text_to_upper_ascii /
 * rt_text_to_lower_ascii, so linking both put three duplicate definitions in
 * libsimple_runtime.a and the Stage-4 archive gate rejected it:
 *
 *   Build failed: Stage4 archive core defines `rt_text_is_ascii` 2 times
 *
 * The two implementations are NOT interchangeable, so this cannot be settled by
 * deleting whichever one is convenient:
 *
 *   - nil / non-string: runtime_native returns 0, this file returns 1
 *     ("vacuously ASCII").
 *   - runtime_native retries through rt_string_promote_raw_receiver(); this
 *     file has no promotion path at all.
 *   - the case converters here allocate RtCoreStringSimd and return a pointer
 *     tagged RT_VALUE_TAG_HEAP_SIMD, a different heap representation from
 *     runtime_native's RtCoreString.
 *
 * Every existing caller was built against runtime_native's semantics, so the
 * incumbent stays the default and this file's entry points are compiled only
 * when a build explicitly asks for them. The SIMD dispatch machinery above is
 * untouched and still available to whoever finishes wiring this lane up.
 *
 * To adopt: define SPL_SIMD_TEXT_CASE_PROVIDER and remove the three
 * definitions from runtime_native.c in the same change, after deciding the
 * nil, promotion, and heap-tag questions above.
 */
#if defined(SPL_SIMD_TEXT_CASE_PROVIDER)

/*
 * rt_text_is_ascii(tagged_string) -> int64_t (1=all ASCII, 0=has non-ASCII)
 *   Caches the result in the reserved field.
 */
int64_t rt_text_is_ascii(int64_t value) {
    simd_case_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 1; /* nil/non-string: vacuously ASCII */

    /* Check cache */
    int cached = cached_ascii_flag(s);
    if (cached >= 0) return (int64_t)cached;

    /* Compute via dispatch table */
    int result = g_simd_text.is_ascii(
        (const uint8_t*)s->data, s->len);

    /* Cache the result */
    cache_ascii_flag(s, result);
    return (int64_t)result;
}

/*
 * rt_text_to_upper_ascii(tagged_string) -> int64_t (new tagged string)
 *   Allocates a new string with ASCII chars uppercased.
 *   Non-ASCII bytes are copied unchanged.
 */
int64_t rt_text_to_upper_ascii(int64_t value) {
    simd_case_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s || s->len == 0) return value;

    /* Allocate new RtCoreStringSimd */
    size_t total = sizeof(RtCoreStringSimd) + (size_t)s->len + 1;
    RtCoreStringSimd* out = (RtCoreStringSimd*)malloc(total);
    if (!out) return value;

    out->kind = RT_VALUE_HEAP_STRING_SIMD;
    out->reserved = 0;
    out->len = s->len;

    g_simd_text.to_upper_ascii(
        (const uint8_t*)s->data, (uint8_t*)out->data, s->len);
    out->data[s->len] = '\0';

    /* Return tagged pointer */
    return (int64_t)(((uintptr_t)out) | RT_VALUE_TAG_HEAP_SIMD);
}

/*
 * rt_text_to_lower_ascii(tagged_string) -> int64_t (new tagged string)
 *   Allocates a new string with ASCII chars lowercased.
 *   Non-ASCII bytes are copied unchanged.
 */
int64_t rt_text_to_lower_ascii(int64_t value) {
    simd_case_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s || s->len == 0) return value;

    /* Allocate new RtCoreStringSimd */
    size_t total = sizeof(RtCoreStringSimd) + (size_t)s->len + 1;
    RtCoreStringSimd* out = (RtCoreStringSimd*)malloc(total);
    if (!out) return value;

    out->kind = RT_VALUE_HEAP_STRING_SIMD;
    out->reserved = 0;
    out->len = s->len;

    g_simd_text.to_lower_ascii(
        (const uint8_t*)s->data, (uint8_t*)out->data, s->len);
    out->data[s->len] = '\0';

    /* Return tagged pointer */
    return (int64_t)(((uintptr_t)out) | RT_VALUE_TAG_HEAP_SIMD);
}

#endif /* SPL_SIMD_TEXT_CASE_PROVIDER */
