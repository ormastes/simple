/* C-lane contract mirrored by value/array_i64.rs tests. */
#include "runtime.h"
#include <assert.h>
#include <stdio.h>

static int64_t handle(SplArray *array) { return (int64_t)(uintptr_t)array; }
static int64_t boxed(int64_t value) { return (int64_t)((uint64_t)value << 3); }

int main(void) {
    SplArray *array = rt_array_new(3);
    int64_t values[] = {-(INT64_C(1) << 60), -1, (INT64_C(1) << 60) - 1};
    int64_t out[] = {99, 99, 99, 99};
    for (int i = 0; i < 3; i++) assert(rt_array_push(array, boxed(values[i])));
    assert(rt_array_i64_validate(handle(array)) == 3);
    for (int64_t capacity = -1; capacity < 3; capacity++) {
        assert(rt_array_i64_copy_checked(handle(array), out, capacity) == -22);
        for (int i = 0; i < 4; i++) assert(out[i] == 99);
    }
    assert(rt_array_i64_copy_checked(handle(array), NULL, 3) == -22);
    assert(rt_array_i64_copy_checked(handle(array), out, 4) == 3);
    for (int i = 0; i < 3; i++) assert(out[i] == values[i]);
    assert(out[3] == 99);
    rt_array_set(array, 2, 3); /* nil, after two valid integer elements */
    assert(rt_array_i64_validate(handle(array)) == -22);
    out[0] = 77;
    assert(rt_array_i64_copy_checked(handle(array), out, 4) == -22);
    assert(out[0] == 77 && out[1] == values[1] && out[2] == values[2] && out[3] == 99);
    rt_array_free(array);
    assert(rt_array_i64_validate(handle(array)) == -22);

    array = rt_array_new(0);
    assert(rt_array_i64_validate(handle(array)) == 0);
    assert(rt_array_i64_copy_checked(handle(array), NULL, 0) == 0);
    assert(rt_array_i64_copy_checked(handle(array), NULL, -1) == -22);
    rt_array_free(array);
    array = rt_byte_array_new_len(2);
    assert(rt_array_i64_validate(handle(array)) == -22);
    rt_array_free(array);
    array = rt_array_new_with_cap_u64(2);
    assert(rt_array_i64_validate(handle(array)) == -22);
    rt_array_free(array);
    int64_t invalid[] = {0, 3, 0x10001, -1};
    for (int i = 0; i < 4; i++) {
        assert(rt_array_i64_validate(invalid[i]) == -22);
        assert(rt_array_i64_copy_checked(invalid[i], NULL, 0) == -22);
    }
    puts("checked i64 array C contract: PASS");
    return 0;
}
