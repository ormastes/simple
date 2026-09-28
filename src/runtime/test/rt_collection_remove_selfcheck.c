/* Absolute-oracle regression for the erased array/dict remove dispatcher.
 * Build with runtime_native.c, SIMPLE_CORE_C_STANDALONE=1 and section GC. */
#include <stdint.h>
#include <stdio.h>
#include "runtime.h"

static int checks;
static int failures;
static void expect(const char* label, int64_t actual, int64_t wanted) {
    checks++;
    if (actual != wanted) {
        failures++;
        printf("FAIL %s: expected %lld, got %lld\n", label,
               (long long)wanted, (long long)actual);
    }
}

static void check_packed_integer_remove(void) {
    const int64_t values[] = {
        INT64_C(1) << 62, INT64_MAX, INT64_MIN,
        -(INT64_C(1) << 60) - 1, -(INT64_C(1) << 60),
        (INT64_C(1) << 60) - 1, INT64_C(1) << 60, -1, 0
    };
    const int64_t count = (int64_t)(sizeof(values) / sizeof(values[0]));
    for (int dispatch = 0; dispatch < 2; dispatch++) {
        SplArray* packed = rt_array_new_with_cap_u64(count);
        for (int64_t i = 0; i < count; i++) rt_array_push(packed, values[i]);
        int64_t receiver = (int64_t)(uintptr_t)packed;
        for (int64_t i = 0; i < count; i++) {
            int64_t removed = dispatch
                ? rt_collection_remove(receiver, rt_value_int(0))
                : rt_array_remove(receiver, 0);
            /* Decode the return: heap boxes need not have equal addresses. */
            expect(dispatch ? "packed dispatcher decoded value" : "packed direct decoded value",
                   rt_value_as_int(removed), values[i]);
            expect("packed length shrank", rt_array_len(packed), count - i - 1);
            if (i + 1 < count) {
                expect("packed tail shifted without truncation", rt_array_get(packed, 0), values[i + 1]);
            }
        }
        rt_array_free(packed);
    }
}

int main(void) {
    check_packed_integer_remove();
    const int64_t nil = 3;
    const int64_t first = rt_string_new((const uint8_t*)"first", 5);
    const int64_t middle = rt_string_new((const uint8_t*)"middle", 6);
    const int64_t last = rt_string_new((const uint8_t*)"last", 4);
    SplArray* array = rt_array_new(3);
    rt_array_push(array, first);
    rt_array_push(array, middle);
    rt_array_push(array, last);
    int64_t receiver = (int64_t)(uintptr_t)array;
    expect("tagged index one returns pointer unchanged",
           rt_collection_remove(receiver, rt_value_int(1)), middle);
    expect("tail shifted", rt_array_get(array, 1), last);
    expect("length shrank", rt_array_len(array), 2);
    expect("negative index", rt_collection_remove(receiver, rt_value_int(-1)), nil);
    expect("past end", rt_collection_remove(receiver, rt_value_int(2)), nil);
    expect("noninteger index", rt_collection_remove(receiver, first), nil);
    expect("refusals preserve length", rt_array_len(array), 2);
    expect("first pointer", rt_collection_remove(receiver, rt_value_int(0)), first);
    expect("last pointer", rt_collection_remove(receiver, rt_value_int(0)), last);
    expect("empty array", rt_collection_remove(receiver, rt_value_int(0)), nil);

    int64_t dict = rt_dict_new(0);
    rt_dict_set(dict, rt_value_int(7), middle);
    rt_dict_set(dict, first, rt_value_int(91));
    expect("dict integer key returns value", rt_collection_remove(dict, rt_value_int(7)), middle);
    expect("dict deletion visible", rt_dict_get(dict, rt_value_int(7)), nil);
    expect("dict text key returns tagged value", rt_collection_remove(dict, first), rt_value_int(91));
    expect("dict missing key", rt_collection_remove(dict, first), nil);
    expect("dict nil key", rt_collection_remove(dict, nil), nil);
    expect("nil receiver", rt_collection_remove(nil, rt_value_int(0)), nil);
    expect("text receiver", rt_collection_remove(first, rt_value_int(0)), nil);
    expect("integer receiver", rt_collection_remove(rt_value_int(9), rt_value_int(0)), nil);
    printf("%s: %d checks, %d failures\n", failures ? "FAIL" : "PASS", checks, failures);
    return failures ? 1 : 0;
}
