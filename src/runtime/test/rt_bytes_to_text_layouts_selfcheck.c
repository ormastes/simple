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

int main(void) {
    const uint8_t raw[] = {0x68, 0x69, 0xC3, 0xA9}; /* "hi" + U+00E9 */

    int64_t packed = rt_bytes_from_raw((int64_t)(uintptr_t)raw, (int64_t)sizeof(raw));
    expect_text(rt_bytes_to_text(packed), "hi\xC3\xA9", 4, "byte-packed [u8] copied verbatim");

    SplArray* slots = rt_array_new(4);
    for (size_t i = 0; i < sizeof(raw); i++) rt_array_push(slots, rt_value_int(raw[i]));
    expect_text(rt_bytes_to_text((int64_t)(uintptr_t)slots), "hi\xC3\xA9", 4,
                "tagged-int slot [u8] narrowed per element");

    SplArray* bad = rt_array_new(1);
    rt_array_push(bad, rt_value_int(300));
    expect_text(rt_bytes_to_text((int64_t)(uintptr_t)bad), "", 0, "out-of-range slot rejected -> \"\"");

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
