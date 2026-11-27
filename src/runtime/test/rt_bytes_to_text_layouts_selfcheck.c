/* rt_bytes_to_text / rt_char_from_code: the canonical runtime entries the
 * native backend lowers `text.from_bytes` / `text.from_char_code` onto
 * (core_codegen.spl translate_call, 2026-09-25).
 *
 * The regression this pins: a `[u8]` is either byte-packed
 * (RT_CORE_ARRAY_FLAG_BYTES) or a generic array of tagged-int slots. The old
 * rt_bytes_to_text copied array->data verbatim, so a slot array produced 8
 * tagged bytes per element instead of the byte values.
 *
 * Build (Windows, clang-cl; POSIX: clang -c -std=gnu11 -ffunction-sections,
 * link with -Wl,--gc-sections -lpthread -lm -ldl):
 *   clang-cl /nologo /c /std:c11 -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -DSIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c
 *   clang-cl /nologo src/runtime/test/rt_bytes_to_text_layouts_selfcheck.c \
 *      runtime_native.obj /link /FORCE:UNRESOLVED
 * (/FORCE:UNRESOLVED for this test binary only: lld-link resolves before
 * /OPT:REF and runtime_native.obj alone references runtime.c helpers that no
 * path exercised here calls.)
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct SplArray SplArray;

extern int64_t rt_bytes_to_text(int64_t bytes_value);
extern int64_t rt_tls_wire_from_bytes(int64_t bytes_value);
extern int64_t rt_char_from_code(int64_t code);
extern SplArray* rt_array_new(int64_t capacity);
extern int64_t rt_array_push(SplArray* array, int64_t value);
extern int64_t rt_value_int(int64_t value);
extern int64_t rt_bytes_from_raw(int64_t addr, int64_t length);
extern int64_t rt_string_len(int64_t string);
extern const uint8_t* rt_string_data(int64_t string);

static int failures = 0;

static void expect_text(int64_t value, const char* want, size_t want_len, const char* what) {
    int64_t len = rt_string_len(value);
    const uint8_t* data = rt_string_data(value);
    int ok = len == (int64_t)want_len && (want_len == 0 || (data && memcmp(data, want, want_len) == 0));
    printf("%s %s (len=%lld)\n", ok ? "ok  " : "FAIL", what, (long long)len);
    if (!ok) failures++;
}

static void expect_nil(int64_t value, const char* what) {
    int ok = value == 3; /* RT_NIL: TAG_SPECIAL payload 0 == RuntimeValue::NIL */
    printf("%s %s (value=%lld)\n", ok ? "ok  " : "FAIL", what, (long long)value);
    if (!ok) failures++;
}

int main(void) {
    const uint8_t raw[] = {0x68, 0x69, 0xC3, 0xA9}; /* "hi" + U+00E9 */

    int64_t packed = rt_bytes_from_raw((int64_t)(uintptr_t)raw, (int64_t)sizeof(raw));
    expect_text(rt_bytes_to_text(packed), "hi\xC3\xA9", 4, "byte-packed [u8] copied verbatim");

    SplArray* slots = rt_array_new(4);
    for (size_t i = 0; i < sizeof(raw); i++) rt_array_push(slots, rt_value_int(raw[i]));
    expect_text(rt_bytes_to_text((int64_t)(uintptr_t)slots), "hi\xC3\xA9", 4,
                "tagged-int slot [u8] narrowed per element");

    {
        uint8_t all[256];
        for (size_t i = 0; i < sizeof(all); i++) all[i] = (uint8_t)i;
        expect_text(rt_tls_wire_from_bytes(
                        rt_bytes_from_raw((int64_t)(uintptr_t)all, (int64_t)sizeof(all))),
                    (const char*)all, sizeof(all),
                    "TLS wire packed [u8] preserves all 256 bytes and NUL");
        SplArray* all_slots = rt_array_new(256);
        for (size_t i = 0; i < sizeof(all); i++)
            rt_array_push(all_slots, rt_value_int(all[i]));
        expect_text(rt_tls_wire_from_bytes((int64_t)(uintptr_t)all_slots),
                    (const char*)all, sizeof(all),
                    "TLS wire boxed [u8] preserves all 256 bytes and NUL");
    }
    {
        const uint8_t mixed[] = {0xC2, 0x80, 0x00, 0xE2, 0x82, 0xAC, 0xFF};
        expect_text(rt_tls_wire_from_bytes(
                        rt_bytes_from_raw((int64_t)(uintptr_t)mixed, (int64_t)sizeof(mixed))),
                    (const char*)mixed, sizeof(mixed),
                    "TLS wire preserves UTF-8-shaped bytes, NUL, and FF");
    }

    SplArray* bad = rt_array_new(1);
    rt_array_push(bad, rt_value_int(300));
    expect_nil(rt_bytes_to_text((int64_t)(uintptr_t)bad), "out-of-range slot rejected -> NIL");

    /* Malformed UTF-8 is REJECTED (owner decision 2026-11-23): the result is
     * NIL (RT_NIL == 3), matching the Rust runtime. Never repaired, never a
     * raw-byte carrier -- use rt_tls_wire_from_bytes for exact bytes. */
    {
        struct { const uint8_t b[4]; int64_t n; const char* what; } cases[] = {
            {{0xC0, 0xAF}, 2, "overlong 2-byte '/' rejected"},
            {{0xE0, 0x80, 0xAF}, 3, "overlong 3-byte rejected"},
            {{0xF0, 0x80, 0x80, 0xAF}, 4, "overlong 4-byte rejected"},
            {{0x80}, 1, "lone continuation rejected"},
            {{0x61, 0xBF, 0x62}, 3, "continuation between ASCII rejected"},
            {{0xED, 0xA0, 0x80}, 3, "encoded high surrogate rejected"},
            {{0xED, 0xBF, 0xBF}, 3, "encoded low surrogate rejected"},
            {{0x61, 0xE2, 0x82}, 3, "truncated 3-byte rejected"},
            {{0xF0, 0x9F, 0x98}, 3, "truncated 4-byte rejected"},
            {{0xE2, 0x82, 0x41}, 3, "bad continuation rejected"},
            {{0x61, 0xFF, 0x62}, 3, "invalid lead 0xFF rejected"},
            {{0xF4, 0x90, 0x80, 0x80}, 4, "above U+10FFFF rejected"},
        };
        for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
            int64_t packed_bad = rt_bytes_from_raw((int64_t)(uintptr_t)cases[i].b, cases[i].n);
            expect_nil(rt_bytes_to_text(packed_bad), cases[i].what);
            SplArray* slot_bad = rt_array_new(cases[i].n);
            for (int64_t k = 0; k < cases[i].n; k++) rt_array_push(slot_bad, rt_value_int(cases[i].b[k]));
            expect_nil(rt_bytes_to_text((int64_t)(uintptr_t)slot_bad), cases[i].what);
        }
        const uint8_t good[] = {0xF0, 0x9F, 0x98, 0x80};
        expect_text(rt_bytes_to_text(rt_bytes_from_raw((int64_t)(uintptr_t)good, 4)), "\xF0\x9F\x98\x80", 4, "valid 4-byte preserved");
        const uint8_t edge[] = {0xF4, 0x8F, 0xBF, 0xBF};
        expect_text(rt_bytes_to_text(rt_bytes_from_raw((int64_t)(uintptr_t)edge, 4)), "\xF4\x8F\xBF\xBF", 4, "U+10FFFF accepted");
    }

    expect_text(rt_char_from_code(65), "A", 1, "rt_char_from_code ASCII");
    expect_text(rt_char_from_code(0xE9), "\xC3\xA9", 2, "rt_char_from_code 2-byte UTF-8");
    expect_text(rt_char_from_code(0x1F600), "\xF0\x9F\x98\x80", 4, "rt_char_from_code 4-byte UTF-8");
    expect_text(rt_char_from_code(0xD800), "", 0, "rt_char_from_code surrogate -> \"\"");

    if (failures) {
        printf("FAIL - %d check(s) failed\n", failures);
        return 1;
    }
    printf("PASS - text.from_bytes / text.from_char_code runtime entries\n");
    return 0;
}
