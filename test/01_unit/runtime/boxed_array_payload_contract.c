#include "src/runtime/runtime_native.c"
#include <assert.h>
int main(void) {
    assert(!rt_array_value_is_boxed_array(0));
    assert(!rt_array_value_is_boxed_array(9));
    assert(!rt_array_value_is_boxed_array(-7));
    assert(!rt_array_value_is_boxed_array(0x100000000LL));
    RtCoreArray fake = {0};
    assert(!rt_array_value_is_boxed_array((int64_t)(uintptr_t)&fake));
    SplArray *value = rt_array_new(2);
    assert(value);
    int64_t bits = (int64_t)(uintptr_t)value;
    assert(rt_array_value_is_boxed_array(bits));
    assert(rt_array_push(value, rt_value_int(42)));
    assert(rt_array_value_is_boxed_array(bits));
    RtCoreArray *registered = rt_core_as_registered_array(bits);
    assert(registered);
    for (unsigned mask = 0; mask < 8; mask++) {
        registered->flags = (mask & 1 ? RT_CORE_ARRAY_FLAG_TUPLE : 0) |
            (mask & 2 ? RT_CORE_ARRAY_FLAG_BYTES : 0) |
            (mask & 4 ? RT_CORE_ARRAY_FLAG_U64_PACKED : 0);
        assert(rt_array_value_is_boxed_array(bits) == (mask == 0));
    }
    registered->flags = 0;
    rt_array_free(value);
    assert(!rt_array_value_is_boxed_array(bits));
    int64_t tuple = rt_tuple_new(2);
    assert(!rt_array_value_is_boxed_array(tuple));
    assert(rt_tuple_set(tuple, 0, rt_value_int(7)));
    assert(rt_tuple_get(tuple, 0) == rt_value_int(7));
    rt_array_free((SplArray *)(uintptr_t)tuple);
    puts("actual C boxed-array registry and flags PASS");
    return 0;
}
