/*
 * SIMD Text Dispatch Table — initialization and scalar fallbacks
 *
 * simd_text_init() probes CPU features and fills g_simd_text with
 * the best available implementation.  Wave 1 always uses scalar;
 * Wave 2 will add AVX2/NEON fast paths.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_simd_dispatch.c
 */

#include "runtime_simd_dispatch.h"
#include <ctype.h>

/* ================================================================
 * Scalar Fallbacks (declared here so other TUs can extern them too)
 * ================================================================ */

/* Count UTF-8 codepoints by scanning continuation bytes */
static int64_t scalar_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    int64_t count = 0;
    for (uint64_t i = 0; i < len; ) {
        uint8_t b = data[i];
        if (b < 0x80) {
            i += 1;
        } else if ((b & 0xE0) == 0xC0) {
            i += 2;
        } else if ((b & 0xF0) == 0xE0) {
            i += 3;
        } else if ((b & 0xF8) == 0xF0) {
            i += 4;
        } else {
            /* Invalid lead byte — skip one byte */
            i += 1;
        }
        count++;
    }
    return count;
}

/* Validate UTF-8.  Returns 1 if valid, 0 otherwise. */
static int scalar_utf8_validate(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    while (i < len) {
        uint8_t b = data[i];
        uint64_t need;
        uint32_t cp;
        if (b < 0x80) {
            i++;
            continue;
        } else if ((b & 0xE0) == 0xC0) {
            need = 2; cp = b & 0x1F;
            if (cp < 2) return 0; /* overlong */
        } else if ((b & 0xF0) == 0xE0) {
            need = 3; cp = b & 0x0F;
        } else if ((b & 0xF8) == 0xF0) {
            need = 4; cp = b & 0x07;
        } else {
            return 0; /* invalid lead */
        }
        if (i + need > len) return 0; /* truncated */
        for (uint64_t j = 1; j < need; j++) {
            if ((data[i + j] & 0xC0) != 0x80) return 0;
            cp = (cp << 6) | (data[i + j] & 0x3F);
        }
        /* Check overlong and surrogate */
        if (need == 3 && cp < 0x800) return 0;
        if (need == 4 && cp < 0x10000) return 0;
        if (cp >= 0xD800 && cp <= 0xDFFF) return 0;
        if (cp > 0x10FFFF) return 0;
        i += need;
    }
    return 1;
}

/* Find first invalid UTF-8 byte offset.  Returns -1 if all valid. */
static int64_t scalar_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    while (i < len) {
        uint8_t b = data[i];
        uint64_t need;
        uint32_t cp;
        if (b < 0x80) { i++; continue; }
        else if ((b & 0xE0) == 0xC0) { need = 2; cp = b & 0x1F; if (cp < 2) return (int64_t)i; }
        else if ((b & 0xF0) == 0xE0) { need = 3; cp = b & 0x0F; }
        else if ((b & 0xF8) == 0xF0) { need = 4; cp = b & 0x07; }
        else return (int64_t)i;

        if (i + need > len) return (int64_t)i;
        for (uint64_t j = 1; j < need; j++) {
            if ((data[i + j] & 0xC0) != 0x80) return (int64_t)i;
            cp = (cp << 6) | (data[i + j] & 0x3F);
        }
        if (need == 3 && cp < 0x800) return (int64_t)i;
        if (need == 4 && cp < 0x10000) return (int64_t)i;
        if (cp >= 0xD800 && cp <= 0xDFFF) return (int64_t)i;
        if (cp > 0x10FFFF) return (int64_t)i;
        i += need;
    }
    return -1;
}

/* Byte-offset search.  Returns offset or -1. */
static int64_t scalar_str_search(const uint8_t* haystack, uint64_t hlen,
                                 const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;
    const void* result = memmem(haystack, hlen, needle, nlen);
    if (!result) return -1;
    return (int64_t)((const uint8_t*)result - haystack);
}

/* Check if all bytes are ASCII (< 0x80) */
static int scalar_is_ascii(const uint8_t* data, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

/* ASCII upper-case (in-place to dst) */
static void scalar_to_upper_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        dst[i] = (uint8_t)toupper(src[i]);
    }
}

/* ASCII lower-case (in-place to dst) */
static void scalar_to_lower_ascii(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        dst[i] = (uint8_t)tolower(src[i]);
    }
}

/* Byte-exact equality */
static int scalar_str_equal(const uint8_t* a, uint64_t alen,
                            const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

/* ================================================================
 * Global Dispatch Table
 * ================================================================ */

SimdTextDispatch g_simd_text = {0};

/* ================================================================
 * Initialization
 * ================================================================ */

void simd_text_init(void) {
    static int initialized = 0;
    if (initialized) return;
    initialized = 1;

    /* Start with scalar defaults */
    g_simd_text.utf8_count_codepoints = scalar_utf8_count_codepoints;
    g_simd_text.utf8_validate         = scalar_utf8_validate;
    g_simd_text.utf8_find_invalid     = scalar_utf8_find_invalid;
    g_simd_text.str_search            = scalar_str_search;
    g_simd_text.is_ascii              = scalar_is_ascii;
    g_simd_text.to_upper_ascii        = scalar_to_upper_ascii;
    g_simd_text.to_lower_ascii        = scalar_to_lower_ascii;
    g_simd_text.str_equal             = scalar_str_equal;

    /* Probe CPU features — Wave 2 will upgrade slots here */
    (void)simd_detect_avx2();
    (void)simd_detect_neon();
}
