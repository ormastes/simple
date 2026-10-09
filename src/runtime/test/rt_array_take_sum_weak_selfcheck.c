/* Self-check for the C-lane twins of rt_array_take, rt_array_sum,
 * rt_shared_downgrade and rt_weak_upgrade (runtime_native.c; Rust originals in
 * compiler_rust/runtime/src/value/collections.rs and objects.rs).
 *
 * The case that bites: take on a BYTES array. rt_array_get returns the RAW
 * byte for a BYTES array, so a take that allocated a plain tagged array and
 * pushed those raw slots would hand back untagged 0..255 values that decode as
 * something else. take must keep the source representation.
 *
 * Build + run (Windows MSVC lane, pinned clang-cl; core-C objects built with
 * the native_project/tools.rs core-C flags):
 *   clang-cl -std:c11 -experimental:c11atomics -DSIMPLE_CORE_C_STANDALONE=1 \
 *     -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -Isrc/runtime -Isrc/runtime/platform \
 *     src/runtime/test/rt_array_take_sum_weak_selfcheck.c <core-C objects> \
 *     -Fe:rtats.exe && ./rtats.exe
 * Linux/macOS: same TU list with the host cc (see rt_array_free_deep_selfcheck.c).
 */
#include <stdio.h>
#include <stdint.h>

typedef struct SplArray SplArray;

extern SplArray* rt_array_new(int64_t cap);
extern SplArray* rt_byte_array_new_len(uint64_t len);
extern int8_t rt_array_push(SplArray* array, int64_t value);
extern int8_t rt_array_set(SplArray* array, int64_t idx, int64_t value);
extern int64_t rt_array_get(SplArray* array, int64_t idx);
extern int64_t rt_array_len(SplArray* array);
extern int64_t rt_array_take(int64_t array, int64_t n);
extern int64_t rt_array_sum(int64_t array);
extern int64_t rt_value_int(int64_t value);
extern int64_t rt_value_float(double value);
extern double rt_value_as_float(int64_t value);
extern int8_t rt_value_is_float(int64_t value);
extern int64_t rt_shared_new(int64_t value);
extern int64_t rt_shared_get(int64_t shared);
extern int64_t rt_shared_downgrade(int64_t shared);
extern int64_t rt_weak_upgrade(int64_t weak);

#define NIL ((int64_t)3)

static int failures = 0;
#define CHECK(cond, msg) do { if (!(cond)) { printf("FAIL: %s\n", msg); failures++; } } while (0)

int main(void) {
    /* 1. take on a BYTES array keeps raw bytes and the BYTES representation. */
    SplArray* bytes = rt_byte_array_new_len(6);
    for (int64_t i = 0; i < 6; i++) rt_array_set(bytes, i, rt_value_int(250 + i));
    int64_t source_slot0 = rt_array_get(bytes, 0);
    SplArray* t = (SplArray*)(intptr_t)rt_array_take((int64_t)(intptr_t)bytes, 4);
    CHECK(t != NULL, "take(bytes, 4) returned non-null");
    CHECK(rt_array_len(t) == 4, "take(bytes, 4) has length 4");
    for (int64_t i = 0; i < 4; i++)
        CHECK(rt_array_get(t, i) == rt_array_get(bytes, i), "take(bytes) slot equals source slot");
    CHECK(rt_array_get(t, 0) == source_slot0, "take(bytes) slot 0 is the raw source byte");
    /* A BYTES result truncates a pushed value to 8 bits; a tagged one would not. */
    rt_array_push(t, rt_value_int(0x1FF));
    CHECK(rt_array_get(t, 4) == 0xFF, "take(bytes) result is still a BYTES array");

    /* 2. take on a tagged array: clamp, values preserved, negative -> empty. */
    SplArray* ints = rt_array_new(4);
    for (int64_t i = 1; i <= 3; i++) rt_array_push(ints, rt_value_int(i * 10));
    SplArray* t2 = (SplArray*)(intptr_t)rt_array_take((int64_t)(intptr_t)ints, 10);
    CHECK(rt_array_len(t2) == 3, "take(ints, 10) clamps to len");
    CHECK(rt_array_get(t2, 2) == rt_value_int(30), "take(ints) keeps tagged values");
    SplArray* t3 = (SplArray*)(intptr_t)rt_array_take((int64_t)(intptr_t)ints, -1);
    CHECK(rt_array_len(t3) == 0, "take(ints, -1) is empty");
    CHECK(rt_array_take(rt_value_int(5), 1) == NIL, "take(non-array) is nil");

    /* 3. sum: ints, raw bytes, float promotion, empty, non-array. */
    CHECK(rt_array_sum((int64_t)(intptr_t)ints) == rt_value_int(60), "sum(ints) == 60");
    int64_t byte_sum = 0;
    for (int64_t i = 0; i < 6; i++) byte_sum += rt_array_get(bytes, i);
    CHECK(rt_array_sum((int64_t)(intptr_t)bytes) == rt_value_int(byte_sum), "sum(bytes) sums raw bytes");
    SplArray* mixed = rt_array_new(4);
    rt_array_push(mixed, rt_value_int(1));
    rt_array_push(mixed, rt_value_float(2.5));
    int64_t ms = rt_array_sum((int64_t)(intptr_t)mixed);
    CHECK(rt_value_is_float(ms) && rt_value_as_float(ms) == 3.5, "sum(1, 2.5) == 3.5 float");
    CHECK(rt_array_sum((int64_t)(intptr_t)rt_array_new(0)) == rt_value_int(0), "sum([]) == 0");
    CHECK(rt_array_sum(rt_value_int(5)) == NIL, "sum(non-array) is nil");

    /* 4. weak round trip on a live shared value. */
    int64_t shared = rt_shared_new(rt_value_int(42));
    CHECK(rt_shared_get(rt_weak_upgrade(rt_shared_downgrade(shared))) == rt_value_int(42),
          "get(upgrade(downgrade(shared(42)))) == 42");

    if (failures) { printf("rt_array_take_sum_weak_selfcheck: %d failure(s)\n", failures); return 1; }
    printf("rt_array_take_sum_weak_selfcheck: PASS\n");
    return 0;
}
