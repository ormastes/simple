/*
 * UTF-8 text operations — codepoint counting, validation, invalid-byte search
 * — plus the owner of the text dispatch table and of the levelled text
 * provider route.
 *
 * CPU-level specific SIMD does NOT live in this binary. The SSE2/AVX2/NEON
 * kernels that used to be here (and in runtime_simd_case.c /
 * runtime_simd_search.c) moved to the levelled vector provider DSO
 * (src/runtime/providers/vector/text_level_kernels.c, one object per level,
 * opcodes SIMPLE_VECTOR_TEXT_* in simple_vector_kernel_abi_v1.h). This file
 * keeps only portable scalar code compiled at the architecture baseline, and
 * at first use (lazy, once, atomic) tries to admit that provider:
 *
 *   path   SIMPLE_VECTOR_PROVIDER_PATH, else the build-time
 *          SIMPLE_VECTOR_PROVIDER_DEFAULT_PATH; same path policy as
 *          provider_artifact_path_allowed_v1 (src/os/smf/provider_loader.spl)
 *   pin    SIMPLE_VECTOR_PROVIDER_SHA256 (with the env path), else the
 *          build-time SIMPLE_VECTOR_PROVIDER_DEFAULT_SHA256; no pin => refused
 *   checks digest before open, digest re-read after open (unstable =>
 *          refused), exports present, interface + ABI digest + TEXT caps
 *          granted by simple_provider_query_v1, selected level > 0, and a
 *          known-answer self-test of every text opcode against scalar.
 *
 * Absent / refused / unsupported => scalar, never a crash, and a provider
 * call that returns any non-OK status falls back to scalar for that call, so
 * results are never silently wrong. simd_text_provider_level() and
 * simd_text_provider_status() report which route runs.
 */

#include "runtime_simd_dispatch.h"
#include "simple_vector_kernel_abi_v1.h"
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdatomic.h>
#if defined(_WIN32)
#  include <windows.h>
#  define SIMD_TEXT_DYNLOAD 1
#elif !defined(__simpleos__) && defined(__has_include)
#  if __has_include(<dlfcn.h>)
#    include <dlfcn.h>
#    define SIMD_TEXT_DYNLOAD 1
#  endif
#endif
#ifndef SIMD_TEXT_DYNLOAD
#  define SIMD_TEXT_DYNLOAD 0 /* no dynamic loader (SimpleOS sysroot): scalar only */
#endif

/* Site ids + prototypes for the UTF-8 slice-boundary audit defined at the
 * bottom of this file. Declared locally (not in runtime.h) so the legacy C
 * translation units that are NOT linked with this file can take a weak
 * reference without dragging in the SIMD dispatch header. */
#define RT_TEXT_SLICE_SITE_RT_SLICE_C      0
#define RT_TEXT_SLICE_SITE_SPL_STR_SLICE   1
#define RT_TEXT_SLICE_SITE_SPL_LEGACY      2
#define RT_TEXT_SLICE_SITE_RT_SLICE_SIMPLE 3
#define RT_TEXT_SLICE_SITE_SELF_TEST       4

/* ================================================================
 * Reserved-Field Cache Helpers
 * ================================================================ */

static inline void cache_cp_count(RtCoreStringSimd* s, int64_t count) {
    if (!s) return;
    if (count < 0 || (uint64_t)count > SIMD_CACHE_CPCOUNT_MASK) return;
    uint32_t r = s->reserved;
    r |= SIMD_CACHE_FLAG_CPCOUNT_VALID;
    r = (r & ~SIMD_CACHE_CPCOUNT_MASK) | ((uint32_t)count & SIMD_CACHE_CPCOUNT_MASK);
    s->reserved = r;
}

static inline int64_t cached_cp_count(const RtCoreStringSimd* s) {
    if (!s) return -1;
    if (!(s->reserved & SIMD_CACHE_FLAG_CPCOUNT_VALID)) return -1;
    return (int64_t)(s->reserved & SIMD_CACHE_CPCOUNT_MASK);
}

/* Check the reserved-field ASCII cache.
 * Returns 1 if the string is known all-ASCII, 0 otherwise (unknown or not ASCII).
 * Bit 31 (SIMD_CACHE_FLAG_IS_ASCII) is set when the string is confirmed all-ASCII. */
static inline int rt_str_is_ascii_cached(const RtCoreStringSimd* s) {
    if (!s) return 0;
    return (s->reserved & SIMD_CACHE_FLAG_IS_ASCII) ? 1 : 0;
}

/* ================================================================
 * Scalar baseline (portable C, architecture-baseline ISA only)
 * ================================================================ */

/* Sum of the 8 byte lanes of a word. */
static inline uint64_t scalar_lane_sum(uint64_t acc) {
    acc = (acc & UINT64_C(0x00FF00FF00FF00FF)) + ((acc >> 8) & UINT64_C(0x00FF00FF00FF00FF));
    return (acc * UINT64_C(0x0001000100010001)) >> 48;
}

/* Lead bytes = length - continuation bytes (10xxxxxx). Word-at-a-time: bit 7
 * of x & ~(x << 1) is "bit7 set and bit6 clear" per byte; per-byte counters
 * flush every 255 rounds. Measured 2026-11-06 on 1 MiB: 44 us, vs 480 us for
 * the byte loop (an `if (...) count++` into int64 does not vectorize). */
static int64_t scalar_utf8_count_codepoints(const uint8_t* data, uint64_t len) {
    const uint64_t high = UINT64_C(0x8080808080808080);
    uint64_t i = 0, cont = 0;
    while (len - i >= 16) {
        uint64_t a0 = 0, a1 = 0;
        for (unsigned round = 0; round < 255 && len - i >= 16; round++, i += 16) {
            uint64_t x, y;
            memcpy(&x, data + i, 8);
            memcpy(&y, data + i + 8, 8);
            a0 += (x & ~(x << 1) & high) >> 7;
            a1 += (y & ~(y << 1) & high) >> 7;
        }
        cont += scalar_lane_sum(a0) + scalar_lane_sum(a1);
    }
    if (len - i >= 8) {
        uint64_t x;
        memcpy(&x, data + i, 8);
        cont += scalar_lane_sum((x & ~(x << 1) & high) >> 7);
        i += 8;
    }
    int64_t count = (int64_t)(i - cont);
    for (; i < len; i++) count += (data[i] & 0xC0) != 0x80;
    return count;
}

/* Portable ASCII test of one 64-byte block: an OR reduction the compiler
 * vectorizes at the baseline ISA (no intrinsics, no CPU-level code). */
#define SCALAR_ASCII_BLOCK 64u
static inline int scalar_block_ascii(const uint8_t* p) {
    uint8_t acc = 0;
    for (unsigned j = 0; j < SCALAR_ASCII_BLOCK; j++) acc |= p[j];
    return acc < 0x80;
}

/* Walk complete sequences from a proven boundary through `end` (the last one
 * may cross it). Returns the first invalid offset, or -1 with *next set. */
static int64_t scalar_utf8_walk(const uint8_t* data, uint64_t len,
                                uint64_t pos, uint64_t end, uint64_t* next) {
    /* Unicode Table 3-7: the second byte's range encodes the overlong
     * (C0/C1 leads, E0, F0), surrogate (ED) and > U+10FFFF (F4, F5+) rules. */
    const uint64_t stop = end < len ? end : len;
    while (pos < stop) {
        uint8_t b = data[pos];
        if (b < 0x80) {
            pos++;
            /* ASCII run: skip whole words. */
            for (uint64_t w; stop - pos >= 8; pos += 8) {
                memcpy(&w, data + pos, 8);
                if (w & UINT64_C(0x8080808080808080)) break;
            }
            continue;
        }
        uint64_t need;
        uint8_t lo = 0x80, hi = 0xBF;
        if (b < 0xC2) return (int64_t)pos; /* continuation as lead, or overlong */
        else if (b < 0xE0) need = 2;
        else if (b < 0xF0) { need = 3; if (b == 0xE0) lo = 0xA0; else if (b == 0xED) hi = 0x9F; }
        else if (b < 0xF5) { need = 4; if (b == 0xF0) lo = 0x90; else if (b == 0xF4) hi = 0x8F; }
        else return (int64_t)pos;
        if (len - pos < need) return (int64_t)pos; /* Truncated sequence */
        if (data[pos + 1] < lo || data[pos + 1] > hi) return (int64_t)pos;
        if (need > 2 && (data[pos + 2] & 0xC0) != 0x80) return (int64_t)pos;
        if (need > 3 && (data[pos + 3] & 0xC0) != 0x80) return (int64_t)pos;
        pos += need;
    }
    *next = pos;
    return -1;
}

static int64_t scalar_utf8_find_invalid(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    while (len - i >= SCALAR_ASCII_BLOCK) {
        if (scalar_block_ascii(data + i)) { i += SCALAR_ASCII_BLOCK; continue; }
        int64_t bad = scalar_utf8_walk(data, len, i, i + SCALAR_ASCII_BLOCK, &i);
        if (bad >= 0) return bad;
    }
    return scalar_utf8_walk(data, len, i, len, &i);
}

static int scalar_utf8_validate(const uint8_t* data, uint64_t len) {
    return scalar_utf8_find_invalid(data, len) < 0;
}

/* ================================================================
 * Global Dispatch Table + Scalar Fallbacks for non-UTF8 operations
 *
 * These live here so runtime_simd_dispatch.h stays header-only.
 * ================================================================ */

SimdTextDispatch g_simd_text = {0};

static const void* scalar_memmem_portable(const void* haystack, size_t hlen,
                                          const void* needle, size_t nlen) {
    const uint8_t* h = (const uint8_t*)haystack;
    const uint8_t* n = (const uint8_t*)needle;
    if (nlen == 0) return haystack;
    if (nlen > hlen) return NULL;
    for (size_t i = 0; i <= hlen - nlen; i++) {
        if (h[i] == n[0] && memcmp(h + i, n, nlen) == 0) {
            return h + i;
        }
    }
    return NULL;
}

/* Scalar fallbacks for search/case (used as initial defaults) */
static int64_t scalar_str_search_default(const uint8_t* haystack, uint64_t hlen,
                                         const uint8_t* needle, uint64_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;
    const void* result = scalar_memmem_portable(haystack, (size_t)hlen, needle, (size_t)nlen);
    if (!result) return -1;
    return (int64_t)((const uint8_t*)result - haystack);
}

static int scalar_is_ascii_default(const uint8_t* data, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        if (data[i] >= 0x80) return 0;
    }
    return 1;
}

static void scalar_to_upper_default(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        dst[i] = (uint8_t)toupper(src[i]);
    }
}

static void scalar_to_lower_default(const uint8_t* src, uint8_t* dst, uint64_t len) {
    for (uint64_t i = 0; i < len; i++) {
        dst[i] = (uint8_t)tolower(src[i]);
    }
}

static int scalar_str_equal_default(const uint8_t* a, uint64_t alen,
                                    const uint8_t* b, uint64_t blen) {
    if (alen != blen) return 0;
    return memcmp(a, b, alen) == 0 ? 1 : 0;
}

/* ================================================================
 * Levelled text provider route
 * ================================================================ */

static simple_vector_apply_fn_v1 g_text_apply = NULL;
static int64_t g_text_handle = 0;
static int g_text_level = 0;
static int g_text_status = SIMD_TEXT_PROVIDER_NOT_CONFIGURED;

int simd_text_provider_call(uint32_t op, const uint8_t* a, uint64_t n,
                            const uint8_t* b, uint64_t bn, uint8_t* out,
                            int64_t* result) {
    simple_vector_apply_fn_v1 apply = g_text_apply;
    if (!apply) return 0;
    uint8_t q[SIMPLE_VECTOR_REQUEST_V1_SIZE], r[SIMPLE_VECTOR_RESPONSE_V1_SIZE];
    simple_vector_wr32(q, SIMPLE_VECTOR_REQUEST_V1_SIZE);
    simple_vector_wr32(q + 4, op);
    simple_vector_wr64(q + 8, n ? (uint64_t)(uintptr_t)a : 0);
    simple_vector_wr64(q + 16, n);
    simple_vector_wr64(q + 24, bn ? (uint64_t)(uintptr_t)b : 0);
    simple_vector_wr64(q + 32, bn);
    simple_vector_wr64(q + 40, (out && n) ? (uint64_t)(uintptr_t)out : 0);
    simple_vector_wr64(q + 48, out ? n : 0);
    simple_vector_wr64(q + 56, 0);
    if (apply(g_text_handle, (int64_t)(uintptr_t)q, (int64_t)(uintptr_t)r) != 0) return 0;
    if (simple_vector_rd32(r) != SIMPLE_VECTOR_RESPONSE_V1_SIZE ||
        simple_vector_rd32(r + 4) != SIMPLE_VECTOR_OK) return 0;
    if (out && simple_vector_rd64(r + 8) != n) return 0;
    *result = (int64_t)simple_vector_rd64(r + 16);
    return 1;
}

int64_t simd_text_provider_level(void) {
    simd_text_init();
    return g_text_level;
}

int64_t simd_text_provider_status(void) {
    simd_text_init();
    return g_text_status;
}

#if SIMD_TEXT_DYNLOAD
/* --- SHA-256 (artifact pin; cold path only) --- */
typedef struct { uint32_t h[8]; uint64_t bytes; uint8_t buf[64]; unsigned used; } TextSha256;
static uint32_t text_rotr(uint32_t v, unsigned s) { return (v >> s) | (v << (32 - s)); }
static void text_sha256_block(TextSha256* c, const uint8_t* p) {
    static const uint32_t k[64] = {
        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
    uint32_t w[64], s[8];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)p[4*i] << 24) | ((uint32_t)p[4*i+1] << 16) | ((uint32_t)p[4*i+2] << 8) | p[4*i+3];
    for (int i = 16; i < 64; i++)
        w[i] = w[i-16] + (text_rotr(w[i-15],7) ^ text_rotr(w[i-15],18) ^ (w[i-15] >> 3)) +
               w[i-7] + (text_rotr(w[i-2],17) ^ text_rotr(w[i-2],19) ^ (w[i-2] >> 10));
    memcpy(s, c->h, sizeof(s));
    for (int i = 0; i < 64; i++) {
        uint32_t t1 = s[7] + (text_rotr(s[4],6) ^ text_rotr(s[4],11) ^ text_rotr(s[4],25)) +
                      ((s[4] & s[5]) ^ (~s[4] & s[6])) + k[i] + w[i];
        uint32_t t2 = (text_rotr(s[0],2) ^ text_rotr(s[0],13) ^ text_rotr(s[0],22)) +
                      ((s[0] & s[1]) ^ (s[0] & s[2]) ^ (s[1] & s[2]));
        memmove(s + 1, s, 7 * sizeof(uint32_t));
        s[4] += t1; s[0] = t1 + t2;
    }
    for (int i = 0; i < 8; i++) c->h[i] += s[i];
}
static void text_sha256_init(TextSha256* c) {
    static const uint32_t iv[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
                                   0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    memcpy(c->h, iv, sizeof(iv)); c->bytes = 0; c->used = 0;
}
static void text_sha256_update(TextSha256* c, const uint8_t* p, size_t n) {
    c->bytes += n;
    while (n) {
        size_t take = 64 - c->used; if (take > n) take = n;
        memcpy(c->buf + c->used, p, take); c->used += (unsigned)take; p += take; n -= take;
        if (c->used == 64) { text_sha256_block(c, c->buf); c->used = 0; }
    }
}
static void text_sha256_hex(TextSha256* c, char hex[65]) {
    uint64_t bits = c->bytes * 8;
    uint8_t pad = 0x80, zero = 0, len[8];
    text_sha256_update(c, &pad, 1);
    while (c->used != 56) text_sha256_update(c, &zero, 1);
    for (int i = 0; i < 8; i++) len[i] = (uint8_t)(bits >> (56 - 8 * i));
    text_sha256_update(c, len, 8);
    for (int i = 0; i < 32; i++)
        snprintf(hex + 2 * i, 3, "%02x", (unsigned)((c->h[i / 4] >> (24 - 8 * (i % 4))) & 0xFF));
    hex[64] = 0;
}
/* Digest of the artifact's current bytes; 0 if unreadable (never "empty"). */
static int text_file_sha256(const char* path, char hex[65]) {
    FILE* f = fopen(path, "rb");
    if (!f) return 0;
    TextSha256 c; text_sha256_init(&c);
    uint8_t buf[16384]; size_t got;
    while ((got = fread(buf, 1, sizeof(buf), f)) > 0) text_sha256_update(&c, buf, got);
    int ok = !ferror(f);
    fclose(f);
    if (ok) text_sha256_hex(&c, hex);
    return ok;
}

/* Mirror of provider_artifact_path_allowed_v1(path, "native"). */
static int text_provider_path_allowed(const char* p) {
    if (!p || !*p || strstr(p, "..") || strstr(p, "//") || strchr(p, '\\')) return 0;
    static const char* roots[] = { "build/providers/", "/sys/providers/",
        "/usr/lib/simple/providers/", "/usr/local/lib/simple/providers/" };
    int rooted = 0;
    for (size_t i = 0; i < sizeof(roots) / sizeof(roots[0]); i++)
        if (!strncmp(p, roots[i], strlen(roots[i]))) rooted = 1;
    size_t n = strlen(p);
    return rooted && ((n > 3 && !strcmp(p + n - 3, ".so")) ||
        (n > 6 && !strcmp(p + n - 6, ".dylib")) || (n > 4 && !strcmp(p + n - 4, ".dll")));
}

static int text_pin_valid(const char* pin) {
    if (!pin || strlen(pin) != 64) return 0;
    for (int i = 0; i < 64; i++)
        if (!((pin[i] >= '0' && pin[i] <= '9') || (pin[i] >= 'a' && pin[i] <= 'f'))) return 0;
    return 1;
}

static void* text_lib_open(const char* path) {
#if defined(_WIN32)
    char native[MAX_PATH], full[MAX_PATH];
    size_t n = strlen(path);
    if (n >= sizeof(native)) return NULL;
    for (size_t i = 0; i <= n; i++) native[i] = path[i] == '/' ? '\\' : path[i];
    DWORD got = GetFullPathNameA(native, MAX_PATH, full, NULL);
    if (got == 0 || got >= MAX_PATH) return NULL;
    return (void*)LoadLibraryExA(full, NULL, LOAD_WITH_ALTERED_SEARCH_PATH);
#else
    return dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}
static void* text_lib_sym(void* lib, const char* name) {
#if defined(_WIN32)
    return (void*)GetProcAddress((HMODULE)lib, name);
#else
    return dlsym(lib, name);
#endif
}
static void text_lib_close(void* lib) {
#if defined(_WIN32)
    FreeLibrary((HMODULE)lib);
#else
    dlclose(lib);
#endif
}

/* Known-answer test of every text opcode through the admitted handle,
 * against the scalar baseline, before any caller is routed there. */
static int text_provider_self_test(void) {
    uint8_t buf[200], up[200], want[200];
    int64_t r;
    for (int i = 0; i < 200; i++) buf[i] = (uint8_t)("aZ-\xc3\xa9qQ"[i % 7]);
    memcpy(buf + 150, "needle", 6);
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_UTF8_VALIDATE, buf, 200, NULL, 0, NULL, &r) || r != 0)
        return 0; /* the 7-byte pattern splits a 2-byte sequence at 196..199 */
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_UTF8_FIND_INVALID, buf, 200, NULL, 0, NULL, &r) ||
        r != scalar_utf8_find_invalid(buf, 200)) return 0;
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_UTF8_COUNT, buf, 200, NULL, 0, NULL, &r) ||
        r != scalar_utf8_count_codepoints(buf, 200)) return 0;
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_ASCII_CHECK, buf, 200, NULL, 0, NULL, &r) || r != 0)
        return 0;
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_ASCII_UPPER, buf, 200, NULL, 0, up, &r)) return 0;
    for (int i = 0; i < 200; i++)
        want[i] = (uint8_t)((buf[i] >= 'a' && buf[i] <= 'z') ? (buf[i] & 0xDF) : buf[i]);
    if (memcmp(up, want, 200)) return 0;
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_ASCII_LOWER, buf, 200, NULL, 0, up, &r)) return 0;
    for (int i = 0; i < 200; i++)
        want[i] = (uint8_t)((buf[i] >= 'A' && buf[i] <= 'Z') ? (buf[i] | 0x20) : buf[i]);
    if (memcmp(up, want, 200)) return 0;
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_FIND, buf, 200, (const uint8_t*)"needle", 6, NULL, &r) ||
        r != 150) return 0;
    if (!simd_text_provider_call(SIMPLE_VECTOR_TEXT_FIND_LAST, buf, 200, (const uint8_t*)"aZ", 2, NULL, &r) ||
        r != 196) return 0;
    return 1;
}

/* Cold, once, from simd_text_init. Publishes g_text_* before the table. */
static void simd_text_provider_admit(void) {
    const char* path = getenv("SIMPLE_VECTOR_PROVIDER_PATH");
    const char* pin = getenv("SIMPLE_VECTOR_PROVIDER_SHA256");
    if (!path || !*path) {
#if defined(SIMPLE_VECTOR_PROVIDER_DEFAULT_PATH) && defined(SIMPLE_VECTOR_PROVIDER_DEFAULT_SHA256)
        path = SIMPLE_VECTOR_PROVIDER_DEFAULT_PATH;
        pin = SIMPLE_VECTOR_PROVIDER_DEFAULT_SHA256;
#else
        g_text_status = SIMD_TEXT_PROVIDER_NOT_CONFIGURED;
        return;
#endif
    }
    if (!strcmp(path, "off")) { g_text_status = SIMD_TEXT_PROVIDER_NOT_CONFIGURED; return; }
    if (!text_provider_path_allowed(path)) { g_text_status = SIMD_TEXT_PROVIDER_PATH_DENIED; return; }
    if (!text_pin_valid(pin)) { g_text_status = SIMD_TEXT_PROVIDER_PIN_INVALID; return; }
    char digest[65];
    if (!text_file_sha256(path, digest)) { g_text_status = SIMD_TEXT_PROVIDER_ARTIFACT_MISSING; return; }
    if (strcmp(digest, pin)) { g_text_status = SIMD_TEXT_PROVIDER_DIGEST_MISMATCH; return; }
    void* lib = text_lib_open(path);
    if (!lib) { g_text_status = SIMD_TEXT_PROVIDER_LOAD_FAILED; return; }
    char reread[65];
    if (!text_file_sha256(path, reread) || strcmp(reread, pin)) {
        text_lib_close(lib); g_text_status = SIMD_TEXT_PROVIDER_DIGEST_UNSTABLE; return;
    }
    simple_vector_query_fn_v1 query = (simple_vector_query_fn_v1)(uintptr_t)text_lib_sym(lib, "simple_provider_query_v1");
    simple_vector_apply_fn_v1 apply = (simple_vector_apply_fn_v1)(uintptr_t)text_lib_sym(lib, "simple_vector_apply_v1");
    int32_t (*level_fn)(void) = (int32_t (*)(void))(uintptr_t)text_lib_sym(lib, "simple_vector_selected_level_v1");
    if (!query || !apply || !level_fn) {
        text_lib_close(lib); g_text_status = SIMD_TEXT_PROVIDER_SYMBOL_MISSING; return;
    }
    uint8_t pq[44] = {0}, pr[84] = {0};
    static const uint8_t abi_digest[32] = SIMPLE_VECTOR_ABI_DIGEST_BYTES;
    simple_vector_wr32(pq, 44);
    simple_vector_wr64(pq + 4, SIMPLE_VECTOR_KERNELS_V1_INTERFACE);
    simple_vector_wr32(pq + 12, 1);
    simple_vector_wr64(pq + 20, 1);
    simple_vector_wr64(pq + 36, SIMPLE_VECTOR_TEXT_CAPS);
    if (query((uint64_t)(uintptr_t)pq, (uint64_t)(uintptr_t)pr) != 0 ||
        simple_vector_rd32(pr) != 0 || simple_vector_rd32(pr + 4) != 1 ||
        memcmp(pr + 48, abi_digest, 32) != 0 ||
        (simple_vector_rd64(pr + 16) & SIMPLE_VECTOR_TEXT_CAPS) != SIMPLE_VECTOR_TEXT_CAPS) {
        text_lib_close(lib); g_text_status = SIMD_TEXT_PROVIDER_QUERY_REFUSED; return;
    }
    int level = level_fn();
    if (level <= 0) { text_lib_close(lib); g_text_status = SIMD_TEXT_PROVIDER_NO_SIMD_LEVEL; return; }
    g_text_handle = (int64_t)simple_vector_rd64(pr + 16);
    g_text_apply = apply;
    if (!text_provider_self_test()) {
        g_text_apply = NULL; g_text_handle = 0;
        text_lib_close(lib); g_text_status = SIMD_TEXT_PROVIDER_SELF_TEST_FAILED; return;
    }
    /* Admitted: the library stays loaded for the process lifetime. */
    g_text_level = level;
    g_text_status = SIMD_TEXT_PROVIDER_ADMITTED;
}

#else
/* No dynamic loader on this target: the scalar baseline is the route. */
static void simd_text_provider_admit(void) {
    const char* path = getenv("SIMPLE_VECTOR_PROVIDER_PATH");
    g_text_status = (path && *path && strcmp(path, "off")) ? SIMD_TEXT_PROVIDER_LOAD_FAILED
                                                            : SIMD_TEXT_PROVIDER_NOT_CONFIGURED;
}
#endif /* SIMD_TEXT_DYNLOAD */

/* Provider-routed slots: tiny spans stay scalar (call overhead), and any
 * non-OK provider status falls back to scalar for that call. */
static int64_t routed_utf8_count(const uint8_t* d, uint64_t n) {
    int64_t r;
    if (n >= SIMD_TEXT_PROVIDER_MIN_BYTES &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_UTF8_COUNT, d, n, NULL, 0, NULL, &r)) return r;
    return scalar_utf8_count_codepoints(d, n);
}
static int routed_utf8_validate(const uint8_t* d, uint64_t n) {
    int64_t r;
    if (n >= SIMD_TEXT_PROVIDER_MIN_BYTES &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_UTF8_VALIDATE, d, n, NULL, 0, NULL, &r)) return r == 1;
    return scalar_utf8_validate(d, n);
}
static int64_t routed_utf8_find_invalid(const uint8_t* d, uint64_t n) {
    int64_t r;
    if (n >= SIMD_TEXT_PROVIDER_MIN_BYTES &&
        simd_text_provider_call(SIMPLE_VECTOR_TEXT_UTF8_FIND_INVALID, d, n, NULL, 0, NULL, &r)) return r;
    return scalar_utf8_find_invalid(d, n);
}

void simd_text_init(void) {
    /* Publish every slot together; concurrent first users must not observe
     * the partially initialized table. No constructor calls this owner. */
    static atomic_int state = ATOMIC_VAR_INIT(0);
    if (atomic_load_explicit(&state, memory_order_acquire) == 2) return;
    int expected = 0;
    if (!atomic_compare_exchange_strong_explicit(&state, &expected, 1,
            memory_order_acquire, memory_order_acquire)) {
        while (atomic_load_explicit(&state, memory_order_acquire) != 2) {}
        return;
    }

    /* Start with scalar defaults for all slots */
    g_simd_text.utf8_count_codepoints = scalar_utf8_count_codepoints;
    g_simd_text.utf8_validate         = scalar_utf8_validate;
    g_simd_text.utf8_find_invalid     = scalar_utf8_find_invalid;
    g_simd_text.str_search            = scalar_str_search_default;
    g_simd_text.is_ascii              = scalar_is_ascii_default;
    g_simd_text.to_upper_ascii        = scalar_to_upper_default;
    g_simd_text.to_lower_ascii        = scalar_to_lower_default;
    g_simd_text.str_equal             = scalar_str_equal_default;

    /* Vector kernels only through an admitted levelled provider. */
    simd_text_provider_admit();
    if (g_text_level > 0) {
        g_simd_text.utf8_count_codepoints = routed_utf8_count;
        g_simd_text.utf8_validate         = routed_utf8_validate;
        g_simd_text.utf8_find_invalid     = routed_utf8_find_invalid;
    }

    /* Search and the opt-in case APIs route through simd_text_provider_call
     * themselves after this publication. */
    atomic_store_explicit(&state, 2, memory_order_release);
}

static inline void simd_text_ensure_init(void) {
    simd_text_init();
}


/* ================================================================
 * rt_* Public API
 * ================================================================ */

/*
 * rt_text_count_codepoints_cached(tagged_string) -> int64_t
 *
 * Checks the reserved-field cache first; falls back to dispatch table.
 * Caches the result in reserved for subsequent calls.
 */
int64_t rt_text_count_codepoints_cached(int64_t value) {
    simd_text_ensure_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 0;

    /* Check cache */
    int64_t cached = cached_cp_count(s);
    if (cached >= 0) return cached;

    /* Dispatch to best available implementation */
    int64_t count = g_simd_text.utf8_count_codepoints(
        (const uint8_t*)s->data, s->len);

    /* Cache the result */
    cache_cp_count(s, count);
    return count;
}

int64_t rt_text_count_codepoints(int64_t value) {
    return rt_text_count_codepoints_cached(value);
}

/*
 * rt_text_validate_utf8(tagged_string) -> int64_t (1=valid, 0=invalid)
 *
 * Fast path: if ASCII cache says all-ASCII, return valid immediately.
 */
int64_t rt_text_validate_utf8(int64_t value) {
    simd_text_ensure_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return 1; /* nil/non-string: vacuously valid */

    /* Fast path: all-ASCII is always valid UTF-8 */
    if (rt_str_is_ascii_cached(s)) return 1;

    return (int64_t)g_simd_text.utf8_validate(
        (const uint8_t*)s->data, s->len);
}

/*
 * rt_text_find_invalid_utf8(tagged_string) -> int64_t
 *   Returns byte offset of first invalid byte, or -1 if valid.
 */
int64_t rt_text_find_invalid_utf8(int64_t value) {
    simd_text_ensure_init();
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return -1;

    /* Fast path: all-ASCII is always valid UTF-8 */
    if (rt_str_is_ascii_cached(s)) return -1;

    return g_simd_text.utf8_find_invalid(
        (const uint8_t*)s->data, s->len);
}

/*
 * rt_text_validate_utf8_bytes(data, len) -> int64_t (1=valid, 0=invalid)
 *
 * Raw-buffer entry point for the same validator `rt_text_validate_utf8` uses.
 * The tagged-value form cannot be applied to a slice RANGE of a string that
 * has not been materialised yet, which is exactly what the slice audit below
 * needs to check.
 */
int64_t rt_text_validate_utf8_bytes(const uint8_t* data, uint64_t len) {
    if (!data || len == 0) return 1;
    simd_text_ensure_init();
    return (int64_t)g_simd_text.utf8_validate(data, len);
}

/* ================================================================
 * UTF-8 slice-boundary audit — COUNTING MODE (stage 1)
 *
 * Bug: text slicing splits UTF-8 mid-codepoint and stores the invalid bytes
 * with no validation. Several independent slice implementations disagree
 * about what happens (raw / lossy / clamped) and stdout's sanitizer renders
 * every one of them identically, so the defect is invisible in printed
 * output -- only the bytes show it.
 *
 * Every C slice implementation reports the range it is about to return here.
 * NOTHING FAILS: this records and (level-gated) logs. The hard error is
 * stage 4 and is enabled only once the measured blast radius over a real
 * workload is zero or a justified residual.
 *
 * Gate -- DEFAULT OFF -- environment `SIMPLE_UTF8_SLICE_AUDIT`:
 *   unset / "0"  disabled; one relaxed load per slice, no validation
 *   "1"          count violations, log the FIRST occurrence per site
 *   "2"          count violations, log EVERY occurrence
 *
 * A violation is recorded only when the SOURCE bytes were valid UTF-8 and
 * the returned bytes are not, so the count measures what slicing causes
 * rather than inheriting unrelated corruption.
 * ================================================================ */

static int g_slice_audit_level = -1; /* -1 = not yet read from environment */
static int64_t g_slice_audit_violations = 0;
static int g_slice_audit_seen[8];

int64_t rt_text_slice_audit_level(void) {
    if (g_slice_audit_level < 0) {
        const char* raw = getenv("SIMPLE_UTF8_SLICE_AUDIT");
        if (raw && raw[0] == '1' && raw[1] == '\0') g_slice_audit_level = 1;
        else if (raw && raw[0] == '2' && raw[1] == '\0') g_slice_audit_level = 2;
        else g_slice_audit_level = 0;
    }
    return g_slice_audit_level;
}

int64_t rt_text_slice_audit_violations(void) {
    return g_slice_audit_violations;
}

/*
 * Returns 1 when this slice created invalid UTF-8. Callers MUST NOT change
 * behaviour on the result while the rollout is in counting mode -- the return
 * value exists so stage 4 can flip to an error at exactly these call sites.
 */
int64_t rt_text_slice_audit_note(int site_id,
                                 const char* site_name,
                                 int64_t start,
                                 int64_t end,
                                 const uint8_t* src,
                                 uint64_t src_len,
                                 const uint8_t* out,
                                 uint64_t out_len) {
    if (rt_text_slice_audit_level() == 0) return 0;
    if (rt_text_validate_utf8_bytes(out, out_len)) return 0;
    if (!rt_text_validate_utf8_bytes(src, src_len)) return 0;

    g_slice_audit_violations++;

    int idx = site_id & 7;
    int first_for_site = (g_slice_audit_seen[idx] == 0);
    g_slice_audit_seen[idx] = 1;
    if (g_slice_audit_level >= 2 || first_for_site) {
        fprintf(stderr,
                "SIMPLE_UTF8_SLICE_AUDIT site=%s start=%lld end=%lld srclen=%llu outlen=%llu\n",
                site_name ? site_name : "unknown",
                (long long)start, (long long)end,
                (unsigned long long)src_len, (unsigned long long)out_len);
    }
    return 1;
}

/*
 * rt_text_slice_audit_note_range(src, src_len, begin, finish)
 *
 * Range form for callers that have not materialised the output string yet --
 * notably the pure-Simple `rt_slice` in src/runtime/simple_core/core_string.spl,
 * which cannot build a C site-name pointer from its baremetal tier. When this
 * object is not linked in, the Simple side's extern resolves to a stub that
 * returns 0 and the audit is simply inactive (fail-closed OFF).
 */
int64_t rt_text_slice_audit_note_range(int64_t src, int64_t src_len,
                                       int64_t begin, int64_t finish) {
    if (rt_text_slice_audit_level() == 0) return 0;
    if (src == 0 || begin < 0 || finish < begin || finish > src_len) return 0;
    const uint8_t* data = (const uint8_t*)(uintptr_t)src;
    return rt_text_slice_audit_note(RT_TEXT_SLICE_SITE_RT_SLICE_SIMPLE, "rt_slice_simple",
                                    begin, finish,
                                    data, (uint64_t)src_len,
                                    data + begin, (uint64_t)(finish - begin));
}

/*
 * Force a synthetic violation. Used to prove the counter is LIVE in the same
 * process as a measurement run: a count of zero from an inert check is
 * indistinguishable from a real zero. Honours the gate like any other site.
 */
int64_t rt_text_slice_audit_self_test(void) {
    static const uint8_t src[2] = { 0xC3, 0xA9 }; /* "é" */
    return rt_text_slice_audit_note(RT_TEXT_SLICE_SITE_SELF_TEST, "self_test",
                                    0, 1, src, 2, src, 1);
}
