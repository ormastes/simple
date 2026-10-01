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

    expect("raw array remove rejects text", rt_array_remove(first, 0), nil);
    expect("raw array remove rejects nil", rt_array_remove(nil, 0), nil);

    SplArray* bytes = rt_byte_array_new(4);
    rt_array_push(bytes, rt_value_int(0));
    rt_array_push(bytes, rt_value_int(128));
    rt_array_push(bytes, rt_value_int(255));
    rt_array_push(bytes, rt_value_int(42));
    int64_t byte_receiver = (int64_t)(uintptr_t)bytes;
    expect("byte layout", rt_array_bytes_basis_len(bytes), 4);
    expect("byte remove tagged middle", rt_collection_remove(byte_receiver, rt_value_int(1)), rt_value_int(128));
    expect("byte shifted first tail", rt_array_get(bytes, 1), 255);
    expect("byte shifted last tail", rt_array_get(bytes, 2), 42);
    expect("byte length", rt_array_len(bytes), 3);
    expect("byte raw remove last", rt_array_remove(byte_receiver, 2), rt_value_int(42));
    expect("byte raw remove first", rt_array_remove(byte_receiver, 0), rt_value_int(0));
    expect("byte raw remove remaining", rt_array_remove(byte_receiver, 0), rt_value_int(255));
    expect("byte empty", rt_collection_remove(byte_receiver, rt_value_int(0)), nil);

    SplArray* packed = rt_array_new_with_cap_u64(4);
    const int64_t large = INT64_C(1) << 59;
    rt_array_push_i64_raw(packed, 17);
    rt_array_push_i64_raw(packed, large);
    rt_array_push_i64_raw(packed, 123456789);
    rt_array_push_i64_raw(packed, 0);
    int64_t packed_receiver = (int64_t)(uintptr_t)packed;
    expect("packed remove tagged middle", rt_collection_remove(packed_receiver, rt_value_int(1)), rt_value_int(large));
    expect("packed shifted first tail", rt_array_get_i64_raw(packed, 1), 123456789);
    expect("packed shifted last tail", rt_array_get_i64_raw(packed, 2), 0);
    expect("packed length", rt_array_len(packed), 3);
    expect("packed raw remove last", rt_array_remove(packed_receiver, 2), rt_value_int(0));
    expect("packed raw remove first", rt_array_remove(packed_receiver, 0), rt_value_int(17));
    expect("packed raw remove remaining", rt_array_remove(packed_receiver, 0), rt_value_int(123456789));
    expect("packed empty", rt_collection_remove(packed_receiver, rt_value_int(0)), nil);

    /* Wide results are boxed independently; compare decoded values, not handles. */
    rt_array_push_i64_raw(packed, INT64_C(1) << 60);
    rt_array_push_i64_raw(packed, INT64_C(1) << 62);
    rt_array_push_i64_raw(packed, INT64_MAX);
    rt_array_push_i64_raw(packed, INT64_MIN);
    expect("packed positive tag boundary", rt_value_as_int(rt_collection_remove(packed_receiver, rt_value_int(0))), INT64_C(1) << 60);
    expect("packed wide high bits", rt_value_as_int(rt_collection_remove(packed_receiver, rt_value_int(0))), INT64_C(1) << 62);
    expect("packed signed maximum", rt_value_as_int(rt_array_remove(packed_receiver, 0)), INT64_MAX);
    expect("packed signed minimum", rt_value_as_int(rt_array_remove(packed_receiver, 0)), INT64_MIN);
    expect("packed wide removals empty", rt_array_len(packed), 0);

    int64_t dict = rt_dict_new(0);
    rt_dict_set(dict, rt_value_int(7), middle);
    rt_dict_set(dict, first, rt_value_int(91));
    expect("dict integer key returns value", rt_collection_remove(dict, rt_value_int(7)), middle);
    expect("dict deletion visible", rt_dict_get(dict, rt_value_int(7)), nil);
    expect("dict text key returns tagged value", rt_collection_remove(dict, first), rt_value_int(91));
    expect("dict missing key", rt_collection_remove(dict, first), nil);
    expect("dict nil key", rt_collection_remove(dict, nil), nil);
    rt_dict_set(dict, first, nil);
    expect("dict nil value removed", rt_collection_remove(dict, first), nil);
    expect("dict nil value deletion visible", rt_dict_contains(dict, first), 0);
    rt_dict_set(dict, first, middle);
    expect("legacy dict remove returns boolean", rt_dict_remove(dict, first), 1);
    expect("legacy deletion visible", rt_dict_get(dict, first), nil);
    expect("legacy missing returns false", rt_dict_remove(dict, first), 0);
    expect("legacy invalid receiver", rt_dict_remove(nil, first), 0);
    expect("nil receiver", rt_collection_remove(nil, rt_value_int(0)), nil);
    expect("text receiver", rt_collection_remove(first, rt_value_int(0)), nil);
    expect("integer receiver", rt_collection_remove(rt_value_int(9), rt_value_int(0)), nil);
    printf("%s: %d checks, %d failures\n", failures ? "FAIL" : "PASS", checks, failures);
    return failures ? 1 : 0;
}
