#include "runtime.h"
#include <stdio.h>
#include <string.h>
#include <time.h>

static int checks, failures;
#define CHECK(value) do { ++checks; if (!(value)) { ++failures; fprintf(stderr, "FAIL POSIX bytes line %d\n", __LINE__); } } while (0)
static int64_t run(const char* script, int64_t timeout, int64_t cap) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, rt_string_new((const uint8_t*)"-c", 2));
    rt_array_push(args, rt_string_new((const uint8_t*)script, strlen(script)));
    int64_t result = rt_process_run_bounded_bytes("/bin/sh", 7, args, timeout, cap);
    rt_array_free(args);
    return result;
}
static int equal(int64_t array, const unsigned char* expected, size_t count) {
    SplArray* bytes = (SplArray*)(uintptr_t)array;
    if ((uint64_t)rt_array_len(bytes) != count) return 0;
    for (size_t i = 0; i < count; ++i) if (rt_value_as_int(rt_array_get(bytes, i)) != expected[i]) return 0;
    return 1;
}
int main(void) {
    int64_t result = run("printf 'A\\000\\377\\342\\202'; exit 9", 1000, 1024);
    const unsigned char expected[] = {'A', 0, 255, 0xe2, 0x82};
    CHECK(rt_value_as_int(rt_tuple_get(result, 2)) == 9);
    CHECK(equal(rt_tuple_get(result, 0), expected, sizeof(expected)));
    CHECK(equal(rt_tuple_get(result, 1), NULL, 0));
    result = run("printf abcdefghijklmnopqrstuvwxyz; exit 7", 1000, 3);
    CHECK(rt_value_as_int(rt_tuple_get(result, 2)) == 7);
    CHECK(equal(rt_tuple_get(result, 0), (const unsigned char*)"abc", 3));
    struct timespec before, after;
    clock_gettime(CLOCK_MONOTONIC, &before);
    result = run("sleep 5", 50, 0);
    clock_gettime(CLOCK_MONOTONIC, &after);
    CHECK(rt_value_as_int(rt_tuple_get(result, 2)) == -1);
    CHECK(equal(rt_tuple_get(result, 0), NULL, 0));
    CHECK(equal(rt_tuple_get(result, 1), NULL, 0));
    CHECK((after.tv_sec - before.tv_sec) * 1000 + (after.tv_nsec - before.tv_nsec) / 1000000 < 2000);
    printf("POSIX production runtime bytes: %d checks, %d failures\n", checks, failures);
    return failures;
}
