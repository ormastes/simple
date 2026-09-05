/* Regression for rt_to_string confusing a boxed integer with an array pointer.
 *
 * Build + run:
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/rt-to-string \
 *     src/runtime/test/rt_to_string_registry_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3 && /tmp/rt-to-string
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct SplArray SplArray;

extern int64_t rt_to_string(int64_t value);
extern const uint8_t* rt_string_data(int64_t string);
extern int64_t rt_string_len(int64_t string);
extern SplArray* rt_array_new(int64_t cap);
extern int8_t rt_array_push(SplArray* array, int64_t value);

static int text_is(int64_t value, const char* expected) {
    int64_t actual_len = rt_string_len(value);
    size_t expected_len = strlen(expected);
    return actual_len == (int64_t)expected_len &&
           memcmp(rt_string_data(value), expected, expected_len) == 0;
}

int main(void) {
    SplArray* array = rt_array_new(1);
    if (!array) {
        fputs("FAIL: registered array creation\n", stderr);
        return 1;
    }

    int64_t year = rt_to_string(2026LL << 3);
    if (!text_is(year, "2026")) {
        fputs("FAIL: boxed integer formatting with a live array\n", stderr);
        return 1;
    }

    if (!rt_array_push(array, 7LL << 3) ||
        !text_is(rt_to_string((int64_t)(uintptr_t)array), "[7]")) {
        fputs("FAIL: registered array formatting\n", stderr);
        return 1;
    }

    puts("RT_TO_STRING_REGISTRY_SELFCHECK: PASS");
    return 0;
}
