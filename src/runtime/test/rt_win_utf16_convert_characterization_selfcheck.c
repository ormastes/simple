/*
 * Characterization selfcheck for the hand-rolled UTF-8 <-> UTF-16 converters
 * in the Windows C runtime (narrow/wide de-duplication, work/dedup-utf16).
 *
 * The ORACLE_* functions below are verbatim copies of the converter bodies
 * that existed before the de-duplication. Only the allocator and free calls
 * are routed through the test hook (t_alloc/t_free), so that allocation
 * failure can be injected:
 *   fwd_z_strict   native_env_widen, runtime_dynload_open_utf8,
 *                  simple_load_library_utf8, spl_widen_long_path (prefix),
 *                  rt_file_list_dir pattern, win_capture_command_wide,
 *                  runtime_dynload.c open, core_snapshot_windows_raw_target
 *   fwd_z_lenient  owned_win_widen                  (flags 0)
 *   fwd_n_strict   rt_http_win_wide                 (length-delimited)
 *   rev_z_lenient  core_exp_wide_to_utf8            (flags 0)
 *   rev_n_lenient  rt_http_win_narrow               (flags 0)
 *   rev_n_strict   native_host_text_from_wide       (WC_ERR_INVALID_CHARS)
 *
 * The transcript printed on stdout is the behavioural contract. It was
 * recorded against the pre-refactor code in
 * rt_win_utf16_convert_characterization.golden.txt and must stay byte-identical.
 *
 * Build and run (Windows, llvm-mingw clang, from the repo root):
 *   clang -std=c11 -Wall -Wextra -Werror -I src/runtime \
 *     src/runtime/test/rt_win_utf16_convert_characterization_selfcheck.c \
 *     -o build/rt_char/rt_win_utf16_convert.exe
 *   build/rt_char/rt_win_utf16_convert.exe > build/rt_char/utf16.txt
 *   diff build/rt_char/utf16.txt \
 *     src/runtime/test/rt_win_utf16_convert_characterization.golden.txt
 * On a non-Windows host the check prints SKIP and exits 0.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef _WIN32
int main(void) {
    printf("SKIP rt_win_utf16_convert_characterization: windows-only\n");
    return 0;
}
#else
#include <windows.h>
#include <limits.h>
#include <wchar.h>

/* ---- allocation test hook ---- */
static int g_fail_at = -1;  /* 1-based allocation index that fails, -1 = never */
static int g_alloc_calls;
static int g_live;
static void* t_alloc(size_t n) {
    g_alloc_calls++;
    if (g_fail_at >= 0 && g_alloc_calls == g_fail_at) return NULL;
    void* p = malloc(n);
    if (p) g_live++;
    return p;
}
static void t_free(void* p) {
    if (p) g_live--;
    free(p);
}
static void hook_reset(int fail_at) {
    g_fail_at = fail_at;
    g_alloc_calls = 0;
}

/* ================= ORACLES (verbatim pre-refactor bodies) ================= */

static wchar_t* oracle_fwd_z_strict(const char* value) {
    int count = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, value, -1, NULL, 0);
    if (count <= 0) return NULL;
    wchar_t* wide = (wchar_t*)t_alloc((size_t)count * sizeof(wchar_t));
    if (!wide) return NULL;
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, value, -1, wide, count)) {
        t_free(wide);
        return NULL;
    }
    return wide;
}

static wchar_t* oracle_fwd_z_lenient(const char* s) {
    int n = MultiByteToWideChar(CP_UTF8, 0, s, -1, NULL, 0);
    if (n <= 0) return NULL;
    wchar_t* w = (wchar_t*)t_alloc((size_t)n * sizeof(wchar_t));
    if (!w) return NULL;
    if (MultiByteToWideChar(CP_UTF8, 0, s, -1, w, n) <= 0) {
        t_free(w);
        return NULL;
    }
    return w;
}

static wchar_t* oracle_fwd_n_strict(const char* text, size_t len) {
    if (len > (size_t)INT_MAX) return NULL;
    int need = len ? MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, text, (int)len, NULL, 0) : 0;
    if (len && need <= 0) return NULL;
    wchar_t* out = (wchar_t*)t_alloc(((size_t)need + 1) * sizeof(wchar_t));
    if (!out) return NULL;
    if (need) MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, text, (int)len, out, need);
    out[need] = L'\0';
    return out;
}

static char* oracle_rev_z_lenient(const wchar_t* wide) {
    int len = WideCharToMultiByte(CP_UTF8, 0, wide, -1, NULL, 0, NULL, NULL);
    if (len <= 0) return NULL;
    char* utf8 = (char*)t_alloc((size_t)len);
    if (!utf8) return NULL;
    if (WideCharToMultiByte(CP_UTF8, 0, wide, -1, utf8, len, NULL, NULL) <= 0) {
        t_free(utf8);
        return NULL;
    }
    return utf8;
}

static uint8_t* oracle_rev_n_lenient(const wchar_t* text, size_t len, size_t* out_len) {
    *out_len = 0;
    if (len > (size_t)INT_MAX) return NULL;
    int need = len ? WideCharToMultiByte(CP_UTF8, 0, text, (int)len, NULL, 0, NULL, NULL) : 0;
    if (len && need <= 0) return NULL;
    uint8_t* out = (uint8_t*)t_alloc((size_t)need + 1);
    if (!out) return NULL;
    if (need) WideCharToMultiByte(CP_UTF8, 0, text, (int)len, (char*)out, need, NULL, NULL);
    out[need] = '\0';
    *out_len = (size_t)need;
    return out;
}

/* native_host_text_from_wide minus the rt_string_new wrapping: returns a
 * malloc'd copy of the bytes the rt_string would have held (NULL = nil). */
static uint8_t* oracle_rev_n_strict(const wchar_t* wide, DWORD length, size_t* out_len) {
    *out_len = 0;
    if (length == 0) return (uint8_t*)calloc(1, 1);
    if (length > INT_MAX) return NULL;
    int bytes = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, wide, (int)length, NULL, 0, NULL, NULL);
    if (bytes <= 0) return NULL;
    uint8_t* utf8 = (uint8_t*)t_alloc((size_t)bytes);
    if (!utf8) return NULL;
    int converted = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, wide, (int)length, (char*)utf8, bytes, NULL, NULL);
    uint8_t* result = NULL;
    if (converted == bytes) {
        result = (uint8_t*)malloc((size_t)bytes);
        memcpy(result, utf8, (size_t)bytes);
        *out_len = (size_t)bytes;
    }
    t_free(utf8);
    return result;
}

/* ================ HELPERS (post-refactor shared header) ================ */
/* Each wraps platform/spl_win_utf16_private.h exactly the way the migrated
 * call site does, so the helper pass must reproduce the oracle transcript. */
#include "platform/spl_win_utf16_private.h"

static wchar_t* helper_fwd_z_strict(const char* s) {
    return spl_win_utf8_to_wide(s, -1, MB_ERR_INVALID_CHARS, t_alloc, t_free, NULL);
}
static wchar_t* helper_fwd_z_lenient(const char* s) {
    return spl_win_utf8_to_wide(s, -1, 0, t_alloc, t_free, NULL);
}
static wchar_t* helper_fwd_n_strict(const char* text, size_t len) {
    if (len > (size_t)INT_MAX) return NULL;
    return spl_win_utf8_to_wide(text, (ptrdiff_t)len, MB_ERR_INVALID_CHARS, t_alloc, t_free, NULL);
}
static char* helper_rev_z_lenient(const wchar_t* w) {
    return spl_win_wide_to_utf8(w, -1, 0, t_alloc, t_free, NULL);
}
static uint8_t* helper_rev_n_lenient(const wchar_t* text, size_t len, size_t* out_len) {
    *out_len = 0;
    if (len > (size_t)INT_MAX) return NULL;
    return (uint8_t*)spl_win_wide_to_utf8(text, (ptrdiff_t)len, 0, t_alloc, t_free, out_len);
}
static uint8_t* helper_rev_n_strict(const wchar_t* wide, DWORD length, size_t* out_len) {
    *out_len = 0;
    if (length == 0) return (uint8_t*)calloc(1, 1);
    if (length > INT_MAX) return NULL;
    size_t bytes = 0;
    char* utf8 = spl_win_wide_to_utf8(wide, (ptrdiff_t)length, WC_ERR_INVALID_CHARS, t_alloc, t_free, &bytes);
    if (!utf8) return NULL;
    uint8_t* result = (uint8_t*)malloc(bytes ? bytes : 1);
    memcpy(result, utf8, bytes);
    *out_len = bytes;
    t_free(utf8);
    return result;
}

/* pass 0 runs the oracles, pass 1 the helpers; transcripts must match */
static int g_use_helper;
static FILE* g_out;
static wchar_t* conv_fwd_z_strict(const char* s) { return g_use_helper ? helper_fwd_z_strict(s) : oracle_fwd_z_strict(s); }
static wchar_t* conv_fwd_z_lenient(const char* s) { return g_use_helper ? helper_fwd_z_lenient(s) : oracle_fwd_z_lenient(s); }
static wchar_t* conv_fwd_n_strict(const char* s, size_t n) { return g_use_helper ? helper_fwd_n_strict(s, n) : oracle_fwd_n_strict(s, n); }
static char* conv_rev_z_lenient(const wchar_t* w) { return g_use_helper ? helper_rev_z_lenient(w) : oracle_rev_z_lenient(w); }
static uint8_t* conv_rev_n_lenient(const wchar_t* w, size_t n, size_t* o) { return g_use_helper ? helper_rev_n_lenient(w, n, o) : oracle_rev_n_lenient(w, n, o); }
static uint8_t* conv_rev_n_strict(const wchar_t* w, DWORD n, size_t* o) { return g_use_helper ? helper_rev_n_strict(w, n, o) : oracle_rev_n_strict(w, n, o); }

/* ============================ transcript ============================ */

static int g_failures;

static uint32_t fnv(const void* data, size_t n, uint32_t h) {
    const unsigned char* p = (const unsigned char*)data;
    for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 16777619u; }
    return h;
}

static void emit(const char* oracle, const char* id, const void* out, size_t bytes, int alloc_calls) {
    if (!out) {
        fprintf(g_out, "%-14s %-24s -> NULL allocs=%d live=%d\n", oracle, id, alloc_calls, g_live);
    } else {
        fprintf(g_out, "%-14s %-24s -> len=%zu fnv=%08x head=", oracle, id, bytes, fnv(out, bytes, 2166136261u));
        const unsigned char* p = (const unsigned char*)out;
        for (size_t i = 0; i < bytes && i < 16; i++) fprintf(g_out, "%02x", p[i]);
        fprintf(g_out, " allocs=%d\n", alloc_calls);
    }
}

static void check_live(const char* oracle, const char* id, int expected) {
    if (g_live != expected) {
        fprintf(g_out, "FAIL leak %s %s live=%d expected=%d\n", oracle, id, g_live, expected);
        g_failures++;
    }
}

/* ---- forward cases (UTF-8 in) ---- */
typedef struct { const char* id; const char* bytes; size_t len; } U8Case;

static void run_fwd(const U8Case* c, int fail_at) {
    char idbuf[64];
    snprintf(idbuf, sizeof(idbuf), fail_at >= 0 ? "%s@fail%d" : "%s", c->id, fail_at);
    int nul_free = memchr(c->bytes, 0, c->len) == NULL;
    if (nul_free) {
        char* z = (char*)malloc(c->len + 1);
        memcpy(z, c->bytes, c->len);
        z[c->len] = 0;
        hook_reset(fail_at);
        wchar_t* w = conv_fwd_z_strict(z);
        emit("fwd_z_strict", idbuf, w, w ? wcslen(w) * sizeof(wchar_t) : 0, g_alloc_calls);
        t_free(w);
        check_live("fwd_z_strict", idbuf, 0);
        hook_reset(fail_at);
        w = conv_fwd_z_lenient(z);
        emit("fwd_z_lenient", idbuf, w, w ? wcslen(w) * sizeof(wchar_t) : 0, g_alloc_calls);
        t_free(w);
        check_live("fwd_z_lenient", idbuf, 0);
        free(z);
    }
    hook_reset(fail_at);
    wchar_t* w = conv_fwd_n_strict(c->bytes, c->len);
    /* the length-delimited result may carry embedded NULs: count to the
     * terminator the oracle wrote, which is at index need. */
    size_t wl = 0;
    if (w) {
        int need = c->len ? MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, c->bytes, (int)c->len, NULL, 0) : 0;
        wl = (size_t)need;
    }
    emit("fwd_n_strict", idbuf, w, wl * sizeof(wchar_t), g_alloc_calls);
    t_free(w);
    check_live("fwd_n_strict", idbuf, 0);
}

/* ---- reverse cases (UTF-16 in) ---- */
typedef struct { const char* id; const wchar_t* w; size_t len; } U16Case;

static void run_rev(const U16Case* c, int fail_at) {
    char idbuf[64];
    snprintf(idbuf, sizeof(idbuf), fail_at >= 0 ? "%s@fail%d" : "%s", c->id, fail_at);
    int nul_free = wmemchr(c->w, 0, c->len) == NULL;
    if (nul_free) {
        wchar_t* z = (wchar_t*)malloc((c->len + 1) * sizeof(wchar_t));
        wmemcpy(z, c->w, c->len);
        z[c->len] = 0;
        hook_reset(fail_at);
        char* s = conv_rev_z_lenient(z);
        emit("rev_z_lenient", idbuf, s, s ? strlen(s) : 0, g_alloc_calls);
        t_free(s);
        check_live("rev_z_lenient", idbuf, 0);
        free(z);
    }
    size_t n = 0;
    hook_reset(fail_at);
    uint8_t* b = conv_rev_n_lenient(c->w, c->len, &n);
    emit("rev_n_lenient", idbuf, b, n, g_alloc_calls);
    t_free(b);
    check_live("rev_n_lenient", idbuf, 0);
    hook_reset(fail_at);
    b = conv_rev_n_strict(c->w, (DWORD)c->len, &n);
    emit("rev_n_strict", idbuf, b, n, g_alloc_calls);
    free(b); /* result copy is not hooked */
    check_live("rev_n_strict", idbuf, 0);
}

static char* repeat_bytes(const char* unit, size_t unit_len, size_t count, size_t* out_len) {
    char* buf = (char*)malloc(unit_len * count + 1);
    for (size_t i = 0; i < count; i++) memcpy(buf + i * unit_len, unit, unit_len);
    buf[unit_len * count] = 0;
    *out_len = unit_len * count;
    return buf;
}

static wchar_t* repeat_wide(const wchar_t* unit, size_t unit_len, size_t count, size_t* out_len) {
    wchar_t* buf = (wchar_t*)malloc((unit_len * count + 1) * sizeof(wchar_t));
    for (size_t i = 0; i < count; i++) wmemcpy(buf + i * unit_len, unit, unit_len);
    buf[unit_len * count] = 0;
    *out_len = unit_len * count;
    return buf;
}

#define U8(id, lit) { id, lit, sizeof(lit) - 1 }

static void suite(void) {
    static const U8Case u8[] = {
        U8("empty", ""),
        U8("ascii1", "a"),
        U8("ascii", "hello world"),
        U8("path_ascii", "C:\\Users\\x\\file.txt"),
        U8("latin_e_acute", "\xC3\xA9"),
        U8("hangul", "\xED\x95\x9C\xEA\xB8\x80"),
        U8("emoji_4byte", "\xF0\x9F\x98\x80"),
        U8("mixed", "a\xC3\xA9\xED\x95\x9C\xF0\x9F\x98\x80z"),
        U8("max_scalar", "\xF4\x8F\xBF\xBF"),
        U8("bom", "\xEF\xBB\xBF" "x"),
        U8("inv_lone_cont", "\x80"),
        U8("inv_trunc2", "\xC3"),
        U8("inv_trunc3", "\xE2\x82"),
        U8("inv_trunc4", "\xF0\x9F\x98"),
        U8("inv_overlong_slash", "\xC0\xAF"),
        U8("inv_overlong_nul", "\xC0\x80"),
        U8("inv_surrogate_hi", "\xED\xA0\x80"),
        U8("inv_surrogate_lo", "\xED\xBF\xBF"),
        U8("inv_cesu_pair", "\xED\xA0\xBD\xED\xB8\x80"),
        U8("inv_above_max", "\xF4\x90\x80\x80"),
        U8("inv_ff", "\xFF"),
        U8("inv_fe", "\xFE"),
        U8("inv_mid", "a\x80" "b"),
        U8("inv_tail", "abc\xC3"),
        U8("embedded_nul", "a\0b"),
        U8("only_nul", "\0"),
        U8("nul_then_inv", "\0\x80"),
    };
    size_t nu8 = sizeof(u8) / sizeof(u8[0]);
    for (size_t i = 0; i < nu8; i++) run_fwd(&u8[i], -1);

    /* buffer / path-length boundaries, incl. > 32K (long-path territory) */
    static const size_t lens[] = { 1, 2, 3, 247, 248, 259, 260, 261, 1023, 1024,
                                   32766, 32767, 32768, 32769, 40000, 70000 };
    for (size_t i = 0; i < sizeof(lens) / sizeof(lens[0]); i++) {
        size_t n;
        char id[64];
        char* a = repeat_bytes("a", 1, lens[i], &n);
        snprintf(id, sizeof(id), "long_ascii_%zu", lens[i]);
        U8Case c = { id, a, n };
        run_fwd(&c, -1);
        free(a);
        a = repeat_bytes("\xC3\xA9", 2, lens[i], &n);
        snprintf(id, sizeof(id), "long_2byte_%zu", lens[i]);
        U8Case c2 = { id, a, n };
        run_fwd(&c2, -1);
        free(a);
        a = repeat_bytes("\xF0\x9F\x98\x80", 4, lens[i], &n);
        snprintf(id, sizeof(id), "long_4byte_%zu", lens[i]);
        U8Case c4 = { id, a, n };
        run_fwd(&c4, -1);
        /* invalid byte at the very end of a long run */
        a[n - 1] = (char)0x80;
        snprintf(id, sizeof(id), "long_4byte_badtail_%zu", lens[i]);
        U8Case c5 = { id, a, n };
        run_fwd(&c5, -1);
        free(a);
    }
    /* long Windows-style path: \\?\C:\ + 300 segments of "dir\xC3\xA9\" */
    {
        size_t n;
        char* seg = repeat_bytes("dir\xC3\xA9\\", 6, 6000, &n);
        char* path = (char*)malloc(n + 16);
        memcpy(path, "\\\\?\\C:\\", 7);
        memcpy(path + 7, seg, n + 1);
        U8Case c = { "long_unc_path_36k", path, n + 7 };
        run_fwd(&c, -1);
        free(seg);
        free(path);
    }

    /* allocation failure on the first (only) allocation */
    for (size_t i = 0; i < nu8; i++) run_fwd(&u8[i], 1);

    /* ---- reverse ---- */
    static const wchar_t w_e[] = { 0x00E9 };
    static const wchar_t w_emoji[] = { 0xD83D, 0xDE00 };
    static const wchar_t w_hi[] = { 0xD83D };
    static const wchar_t w_lo[] = { 0xDE00 };
    static const wchar_t w_hi_end[] = { L'a', 0xD83D };
    static const wchar_t w_rev_pair[] = { 0xDE00, 0xD83D };
    static const wchar_t w_hi_hi[] = { 0xD83D, 0xD83D, 0xDE00 };
    static const wchar_t w_mixed[] = { L'a', 0x00E9, 0xD55C, 0xD83D, 0xDE00, L'z' };
    static const wchar_t w_emb[] = { L'a', 0, L'b' };
    static const wchar_t w_fffd[] = { 0xFFFD };
    static const wchar_t w_ffff[] = { 0xFFFF };
    static const U16Case u16[] = {
        { "empty", L"", 0 },
        { "ascii", L"hello", 5 },
        { "latin_e_acute", w_e, 1 },
        { "emoji_pair", w_emoji, 2 },
        { "mixed", w_mixed, 6 },
        { "lone_high", w_hi, 1 },
        { "lone_low", w_lo, 1 },
        { "high_at_end", w_hi_end, 2 },
        { "reversed_pair", w_rev_pair, 2 },
        { "high_high_low", w_hi_hi, 3 },
        { "embedded_nul", w_emb, 3 },
        { "fffd", w_fffd, 1 },
        { "ffff_nonchar", w_ffff, 1 },
    };
    size_t nu16 = sizeof(u16) / sizeof(u16[0]);
    for (size_t i = 0; i < nu16; i++) run_rev(&u16[i], -1);
    for (size_t i = 0; i < sizeof(lens) / sizeof(lens[0]); i++) {
        size_t n;
        char id[64];
        wchar_t* a = repeat_wide(w_emoji, 2, lens[i], &n);
        snprintf(id, sizeof(id), "long_pairs_%zu", lens[i]);
        U16Case c = { id, a, n };
        run_rev(&c, -1);
        a[n - 1] = 0xD83D; /* break the final pair: high,high */
        snprintf(id, sizeof(id), "long_pairs_badtail_%zu", lens[i]);
        U16Case c2 = { id, a, n };
        run_rev(&c2, -1);
        free(a);
    }
    for (size_t i = 0; i < nu16; i++) run_rev(&u16[i], 1);

    /* ---- round trips: strict forward then strict reverse ---- */
    for (size_t i = 0; i < nu8; i++) {
        hook_reset(-1);
        wchar_t* w = conv_fwd_n_strict(u8[i].bytes, u8[i].len);
        if (!w) { fprintf(g_out, "roundtrip %-24s -> fwd NULL\n", u8[i].id); continue; }
        int need = u8[i].len ? MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, u8[i].bytes, (int)u8[i].len, NULL, 0) : 0;
        size_t n = 0;
        uint8_t* back = conv_rev_n_strict(w, (DWORD)need, &n);
        int same = back && n == u8[i].len && memcmp(back, u8[i].bytes, n) == 0;
        fprintf(g_out, "roundtrip %-24s -> %s\n", u8[i].id, same ? "identical" : "DIFFERENT");
        free(back);
        t_free(w);
    }

    /* ---- seeded fuzz: aggregate fingerprint per oracle ---- */
    {
        uint32_t seed = 0x5EED1234u;
        uint32_t h_zs = 2166136261u, h_zl = 2166136261u, h_ns = 2166136261u;
        uint32_t h_rz = 2166136261u, h_rl = 2166136261u, h_rs = 2166136261u;
        int null_zs = 0, null_zl = 0, null_ns = 0, null_rz = 0, null_rl = 0, null_rs = 0;
        for (int iter = 0; iter < 20000; iter++) {
            unsigned char buf[40];
            wchar_t wbuf[20];
            seed = seed * 1103515245u + 12345u;
            size_t len = (seed >> 16) % 39;
            for (size_t k = 0; k < len; k++) {
                seed = seed * 1103515245u + 12345u;
                unsigned v = (seed >> 16) & 0xFF;
                /* bias toward UTF-8 lead/continuation bytes */
                buf[k] = (unsigned char)((v & 1) ? (0x80 | (v & 0x3F)) : (v | 1));
            }
            buf[len] = 0;
            size_t wlen = len / 2;
            for (size_t k = 0; k < wlen; k++) {
                seed = seed * 1103515245u + 12345u;
                unsigned v = seed >> 16;
                wbuf[k] = (wchar_t)((v & 3) == 0 ? (0xD800 | (v & 0x7FF)) : ((v & 0xFFFF) | 1));
            }
            wbuf[wlen] = 0;
            hook_reset(-1);
            wchar_t* w = conv_fwd_z_strict((const char*)buf);
            if (w) h_zs = fnv(w, wcslen(w) * 2, h_zs); else null_zs++;
            t_free(w);
            w = conv_fwd_z_lenient((const char*)buf);
            if (w) h_zl = fnv(w, wcslen(w) * 2, h_zl); else null_zl++;
            t_free(w);
            w = conv_fwd_n_strict((const char*)buf, len);
            if (w) h_ns = fnv(w, wcslen(w) * 2, h_ns); else null_ns++;
            t_free(w);
            char* s = conv_rev_z_lenient(wbuf);
            if (s) h_rz = fnv(s, strlen(s), h_rz); else null_rz++;
            t_free(s);
            size_t n = 0;
            uint8_t* b = conv_rev_n_lenient(wbuf, wlen, &n);
            if (b) h_rl = fnv(b, n, h_rl); else null_rl++;
            t_free(b);
            b = conv_rev_n_strict(wbuf, (DWORD)wlen, &n);
            if (b) h_rs = fnv(b, n, h_rs); else null_rs++;
            free(b);
        }
        fprintf(g_out, "fuzz fwd_z_strict  fnv=%08x nulls=%d\n", h_zs, null_zs);
        fprintf(g_out, "fuzz fwd_z_lenient fnv=%08x nulls=%d\n", h_zl, null_zl);
        fprintf(g_out, "fuzz fwd_n_strict  fnv=%08x nulls=%d\n", h_ns, null_ns);
        fprintf(g_out, "fuzz rev_z_lenient fnv=%08x nulls=%d\n", h_rz, null_rz);
        fprintf(g_out, "fuzz rev_n_lenient fnv=%08x nulls=%d\n", h_rl, null_rl);
        fprintf(g_out, "fuzz rev_n_strict  fnv=%08x nulls=%d\n", h_rs, null_rs);
        check_live("fuzz", "all", 0);
    }
}

static char* slurp(FILE* f, long* len) {
    fflush(f);
    *len = ftell(f);
    char* buf = (char*)malloc((size_t)*len + 1);
    rewind(f);
    *len = (long)fread(buf, 1, (size_t)*len, f);
    return buf;
}

int main(void) {
    FILE* passes[2];
    for (int p = 0; p < 2; p++) {
        passes[p] = tmpfile();
        if (!passes[p]) { fprintf(stderr, "tmpfile failed\n"); return 2; }
        g_use_helper = p;
        g_out = passes[p];
        suite();
    }
    long n0, n1;
    char* t0 = slurp(passes[0], &n0);
    char* t1 = slurp(passes[1], &n1);
    fwrite(t0, 1, (size_t)n0, stdout); /* oracle transcript == golden */
    if (n0 != n1 || memcmp(t0, t1, (size_t)n0) != 0) {
        long i = 0;
        while (i < n0 && i < n1 && t0[i] == t1[i]) i++;
        fprintf(stderr, "FAIL helper transcript differs from oracle at byte %ld\n", i);
        g_failures++;
    }
    if (g_failures) {
        fprintf(stderr, "rt_win_utf16_convert_characterization: %d failure(s)\n", g_failures);
        return 1;
    }
    fprintf(stderr, "rt_win_utf16_convert_characterization: PASS (oracle == helper)\n");
    return 0;
}
#endif
