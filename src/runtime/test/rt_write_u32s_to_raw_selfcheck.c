/* Self-check for the C-lane twins of rt_write_u32s_to_raw and
 * rt_write_fill_u32s_to_raw_checksum (runtime_native.c; Rust originals in
 * compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs).
 *
 * Build + run (Windows MSVC lane, pinned clang-cl; core-C objects built with
 * the native_project/tools.rs core-C flags):
 *   clang-cl -std:c11 -experimental:c11atomics -DSIMPLE_CORE_C_STANDALONE=1 \
 *     -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -Isrc/runtime -Isrc/runtime/platform \
 *     src/runtime/test/rt_write_u32s_to_raw_selfcheck.c <core-C objects> \
 *     -Fe:rtw32.exe && ./rtw32.exe
 * Linux/macOS: same TU list with the host cc (see rt_array_free_deep_selfcheck.c).
 */
#include <stdio.h>
#include <stdint.h>

typedef struct SplArray SplArray;

extern SplArray* rt_array_new(int64_t cap);
extern SplArray* rt_byte_array_new_len(uint64_t len);
extern int8_t rt_array_push(SplArray* array, int64_t value);
extern int8_t rt_array_set(SplArray* array, int64_t idx, int64_t value);
extern int64_t rt_value_int(int64_t value);
extern int64_t rt_write_u32s_to_raw(int64_t ptr, int64_t values);
extern int64_t rt_write_fill_u32s_to_raw_checksum(int64_t ptr, int64_t values, int64_t count, int64_t expected);

static int failures = 0;
#define CHECK(cond, msg) do { if (!(cond)) { printf("FAIL: %s\n", msg); failures++; } } while (0)

int main(void) {
    uint32_t out[4] = {0, 0, 0, 0};
    int64_t dst = (int64_t)(intptr_t)out;

    /* 1. tagged ints copy as u32 words, count returned; high bits truncate. */
    SplArray* words = rt_array_new(3);
    rt_array_push(words, rt_value_int(7));
    rt_array_push(words, rt_value_int(0xFFFFFFFFLL));
    rt_array_push(words, rt_value_int(0x100000002LL));
    CHECK(rt_write_u32s_to_raw(dst, (int64_t)(intptr_t)words) == 3, "write returns len 3");
    CHECK(out[0] == 7u && out[1] == 0xFFFFFFFFu && out[2] == 2u, "words copied (u32 truncation)");
    CHECK(out[3] == 0u, "no write past len");

    /* 2. null ptr, empty array and non-array all write nothing and return 0. */
    CHECK(rt_write_u32s_to_raw(0, (int64_t)(intptr_t)words) == 0, "null ptr -> 0");
    CHECK(rt_write_u32s_to_raw(dst, (int64_t)(intptr_t)rt_array_new(0)) == 0, "empty -> 0");
    CHECK(rt_write_u32s_to_raw(dst, rt_value_int(5)) == 0, "non-array -> 0");

    /* 3. BYTES arrays hand back raw slots: each byte becomes one word. */
    SplArray* bytes = rt_byte_array_new_len(2);
    rt_array_set(bytes, 0, rt_value_int(200));
    rt_array_set(bytes, 1, rt_value_int(9));
    CHECK(rt_write_u32s_to_raw(dst, (int64_t)(intptr_t)bytes) == 2, "bytes write returns 2");
    CHECK(out[0] == 200u && out[1] == 9u, "bytes copied raw");

    /* 4. exact fill: checksum = sum(w & 0x7fffffff) mod (2^31-1). */
    SplArray* fill = rt_array_new(3);
    for (int i = 0; i < 3; i++) rt_array_push(fill, rt_value_int(5));
    CHECK(rt_write_fill_u32s_to_raw_checksum(dst, (int64_t)(intptr_t)fill, 3, 5) == 15, "fill checksum 15");
    CHECK(out[0] == 5u && out[1] == 5u && out[2] == 5u, "fill words written");

    /* 5. mismatch -> -1 (after writing), zero checksum -> 1, bad args -> 0. */
    CHECK(rt_write_fill_u32s_to_raw_checksum(dst, (int64_t)(intptr_t)fill, 3, 6) == -1, "mismatch -> -1");
    SplArray* zeros = rt_array_new(2);
    rt_array_push(zeros, rt_value_int(0));
    rt_array_push(zeros, rt_value_int(0));
    CHECK(rt_write_fill_u32s_to_raw_checksum(dst, (int64_t)(intptr_t)zeros, 2, 0) == 1, "zero checksum -> 1");
    CHECK(rt_write_fill_u32s_to_raw_checksum(dst, (int64_t)(intptr_t)fill, 2, 5) == 0, "count != len -> 0");
    CHECK(rt_write_fill_u32s_to_raw_checksum(dst, (int64_t)(intptr_t)fill, 3, -1) == 0, "negative expected -> 0");
    CHECK(rt_write_fill_u32s_to_raw_checksum(0, (int64_t)(intptr_t)fill, 3, 5) == 0, "null ptr -> 0");

    if (failures) { printf("rt_write_u32s_to_raw_selfcheck: %d failure(s)\n", failures); return 1; }
    printf("rt_write_u32s_to_raw_selfcheck: PASS\n");
    return 0;
}
