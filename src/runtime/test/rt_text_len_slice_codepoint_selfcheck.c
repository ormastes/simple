/* C twin of the Rust runtime text length/slice unit (ADR-005 item 5, bug
 * text_len_bytes_vs_codepoint_index_bound_disagree_2026_11_03): the user-facing
 * length (rt_len / rt_string_char_count), rt_slice on text, rt_string_index_of
 * and rt_string_rfind count CODE POINTS, while rt_string_len stays the BYTE
 * primitive (byte_len(), the (data, len) text extern ABI, internal callers).
 * Rust twin: collections.rs `text_len_slice_codepoint_tests`.
 * Standalone build (unused runtime TUs are dropped by section GC; the local
 * spl_panic stands in for runtime.c, so never link runtime.c with this):
 *   clang -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1
 *     -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -Isrc/runtime -Isrc/runtime/platform <this file>
 *     Linux: -Wl,--gc-sections -lm -lpthread
 *     Windows (lld-link): -Wl,/OPT:REF -Wl,/FORCE:UNRESOLVED */
#include "../runtime_native.c"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void spl_panic(const char* msg) { fprintf(stderr, "PANIC: %s\n", msg ? msg : ""); exit(101); }
/* rt_slice's UTF-8 slice audit hook lives in runtime_simd_utf8.c, which this
 * standalone link does not pull in (an unresolved call under /FORCE would jump
 * to address 0). Audit off. */
int64_t rt_text_slice_audit_level(void) { return 0; }

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

static int64_t T(const char* s) { return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s)); }

static int text_is(int64_t v, const char* want) {
    int64_t n = rt_string_len(v);
    const uint8_t* d = rt_string_data(v);
    return d && n == (int64_t)strlen(want) && memcmp(d, want, (size_t)n) == 0;
}

#ifdef _WIN32
#include <windows.h>
#include <process.h>
#else
#include <pthread.h>
#endif

static int64_t g_ascii, g_utf, g_needle;
static volatile int g_fail;

static void stress_body(void) {
    for (int64_t i = 0; i < 20000 && !g_fail; i++) {
        if (rt_string_char_count(g_ascii) != 257 || rt_len(g_ascii) != 257) { g_fail = 1; return; }
        if (rt_string_char_count(g_utf) != 480 || rt_len(g_utf) != 480 || rt_string_len(g_utf) != 560) { g_fail = 2; return; }
        int64_t k = i % 400;
        int64_t want = (k + 3 < 257 ? k + 3 : 257) - (k < 257 ? k : 257);
        if (rt_string_len(rt_slice(g_ascii, k, k + 3, 1)) != want) { g_fail = 3; return; }
        if (!text_is(rt_slice(g_utf, 12 * (i % 40), 12 * (i % 40) + 2, 1), "h\xC3\xA9")) { g_fail = 4; return; }
        if (rt_string_find(g_utf, g_needle) != 6) { g_fail = 5; return; }
    }
}

#ifdef _WIN32
static unsigned __stdcall stress_thread(void* arg) { (void)arg; stress_body(); return 0; }
#else
static void* stress_thread(void* arg) { (void)arg; stress_body(); return NULL; }
#endif

static int stress_two_threads(void) {
    char ascii[258]; memset(ascii, 'x', 257); ascii[257] = 0;
    char utf[561]; utf[0] = 0;
    for (int i = 0; i < 40; i++) strcat(utf, "h\xC3\xA9llo w\xC3\xB6rld "); /* 12 cps, 14 bytes each */
    g_ascii = T(ascii); g_utf = T(utf); g_needle = T("w\xC3\xB6");
    if (rt_string_len(g_utf) != 560) return 1;
#ifdef _WIN32
    HANDLE th[2];
    for (int t = 0; t < 2; t++) th[t] = (HANDLE)_beginthreadex(NULL, 0, stress_thread, NULL, 0, NULL);
    WaitForMultipleObjects(2, th, TRUE, INFINITE);
    for (int t = 0; t < 2; t++) CloseHandle(th[t]);
#else
    pthread_t th[2];
    for (int t = 0; t < 2; t++) pthread_create(&th[t], NULL, stress_thread, NULL);
    for (int t = 0; t < 2; t++) pthread_join(th[t], NULL);
#endif
    if (g_fail) { fprintf(stderr, "stress fail code=%d\n", g_fail); return 1; }
    /* memo bit set exactly on the ASCII string, never on the UTF-8 one */
    RtCoreString* a = rt_core_as_string(g_ascii);
    RtCoreString* u = rt_core_as_string(g_utf);
    if (!a || !u) return 1;
    if (!(__atomic_load_n(&a->reserved, __ATOMIC_RELAXED) & RT_CORE_STRING_FLAG_ASCII)) return 1;
    if (__atomic_load_n(&u->reserved, __ATOMIC_RELAXED) & RT_CORE_STRING_FLAG_ASCII) return 1;
    return 0;
}

int main(void) {
    int64_t s = T("h\xC3\xA9llo");          /* "h-e-acute-llo": 5 code points, 6 bytes */
    int64_t e = T("a\xF0\x9F\x98\x80" "b"); /* "a<U+1F600>b": 3 code points, 6 bytes */

    /* length unit */
    CHECK(rt_string_char_count(s) == 5);
    CHECK(rt_len(s) == 5);
    CHECK(rt_string_len(s) == 6);            /* byte primitive unchanged */
    CHECK(rt_string_char_count(e) == 3);
    CHECK(rt_len(e) == 3);
    CHECK(rt_string_len(e) == 6);
    CHECK(rt_string_char_count(T("")) == 0);
    CHECK(rt_string_char_count(rt_core_nil()) == -1);
    /* raw literal receiver (bare .rodata pointer, what rt_string_len accepts) */
    CHECK(rt_string_char_count((int64_t)(uintptr_t)"h\xC3\xA9llo") == 5);
    CHECK(rt_string_char_count((int64_t)(uintptr_t)"abc") == 3);

    /* ASCII fast path, around the 8-byte word boundary */
    {
        char buf[40];
        size_t ns[] = {7, 8, 9, 16, 17, 31, 32, 33};
        for (size_t k = 0; k < sizeof ns / sizeof ns[0]; k++) {
            size_t n = ns[k];
            memset(buf, 'x', n); buf[n] = 0;
            CHECK(rt_string_char_count(T(buf)) == (int64_t)n);
            CHECK(rt_len(T(buf)) == (int64_t)n);
            memset(buf, 'x', n - 1); buf[n - 1] = '\xC3'; buf[n] = '\xA9'; buf[n + 1] = 0;
            CHECK(rt_string_char_count(T(buf)) == (int64_t)n);
        }
    }

    /* slice by code point */
    CHECK(text_is(rt_slice(s, 1, 3, 1), "\xC3\xA9l"));
    CHECK(text_is(rt_slice(s, 2, 5, 1), "llo"));
    CHECK(text_is(rt_slice(s, 0, 2, 1), "h\xC3\xA9"));
    CHECK(text_is(rt_slice(s, -2, 5, 1), "lo"));
    CHECK(text_is(rt_slice(s, 3, 99, 1), "lo"));
    CHECK(text_is(rt_slice(s, 9, 12, 1), ""));
    CHECK(text_is(rt_slice(T("a\xF0\x9F\x98\x80" "bc"), 1, 3, 1), "\xF0\x9F\x98\x80" "b"));
    CHECK(text_is(rt_slice(T("hello"), 1, 3, 1), "el"));
    CHECK(text_is(rt_slice(T("hello"), 3, 5, 1), "lo"));
    CHECK(text_is(rt_slice(s, 0, 5, 2), "hlo"));  /* stride walks code points */

    /* index_of / rfind in code points */
    CHECK(rt_string_index_of(s, T("l")) == 2);
    CHECK(rt_string_index_of(s, T("o")) == 4);
    CHECK(rt_string_index_of(s, T("\xC3\xA9")) == 1);
    CHECK(rt_string_index_of(s, T("z")) == -1);
    CHECK(rt_string_index_of(s, T("")) == 0);
    CHECK(rt_string_rfind(s, T("l")) == 3);
    CHECK(rt_string_rfind(s, T("")) == 5);
    CHECK(rt_string_rfind(s, T("z")) == -1);
    CHECK(text_is(rt_slice(s, rt_string_index_of(s, T("l")), rt_len(s), 1), "llo"));
    CHECK(rt_string_index_of(T("hello"), T("lo")) == 3);
    CHECK(rt_string_rfind(T("hello"), T("l")) == 3);

    /* Two threads hammering len()/slice/find on ONE shared ASCII and ONE shared
     * non-ASCII string: the memoized ASCII flag is set with an atomic RMW, so
     * no thread may observe a wrong answer or a lost bit (concurrency is P0;
     * Opus review of PR #7892). */
    if (stress_two_threads() != 0) { fprintf(stderr, "FAIL concurrent len/slice/find\n"); return 1; }
    checks += 4;

    printf("PASS rt_text_len_slice_codepoint_selfcheck %u checks\n", checks);
    return 0;
}
