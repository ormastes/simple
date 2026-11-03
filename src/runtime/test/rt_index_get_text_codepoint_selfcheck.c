/* C twin of the Rust rt_index_get text policy (ADR-005, PR #6380):
 * s[i] indexes by code point, negative i counts from the end, and an
 * out-of-range index panics with "error: string index N out of bounds".
 * Run with no argument for the in-range checks; run with "oob" (or "neg")
 * and the process must die with that message on stderr.
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

/* spl_panic lives in runtime.c, which this standalone link does not pull in. */
void spl_panic(const char* msg) { fprintf(stderr, "PANIC: %s\n", msg ? msg : ""); exit(101); }

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

static int text_is(int64_t v, const char* want) {
    int64_t n = rt_string_len(v);
    const uint8_t* d = rt_string_data(v);
    return d && n == (int64_t)strlen(want) && memcmp(d, want, (size_t)n) == 0;
}

int main(int argc, char** argv) {
    const char* src = "72\xC3\xA9";           /* "72é": 3 code points, 4 bytes */
    int64_t s = rt_string_new((const uint8_t*)src, 4);
    if (argc > 1 && strcmp(argv[1], "oob") == 0) { rt_index_get(s, rt_value_int(3)); return 0; }
    if (argc > 1 && strcmp(argv[1], "neg") == 0) { rt_index_get(s, rt_value_int(-4)); return 0; }
    CHECK(text_is(rt_index_get(s, rt_value_int(0)), "7"));
    CHECK(text_is(rt_index_get(s, rt_value_int(2)), "\xC3\xA9"));
    CHECK(text_is(rt_index_get(s, rt_value_int(-1)), "\xC3\xA9"));
    CHECK(text_is(rt_index_get(s, rt_value_int(-3)), "7"));
    printf("PASS rt_index_get_text_codepoint_selfcheck %u checks\n", checks);
    return 0;
}
