/* Native core owners must preserve byte extents and detect failing assertions. */
#include "runtime.h"
#include <stdio.h>
#include <string.h>
extern int64_t rt_text_to_bytes(int64_t text);
extern int64_t rt_bytes_to_text(int64_t bytes);

static int text_matches(int64_t value, const uint8_t *bytes, size_t length) {
    return rt_string_len(value) == (int64_t)length &&
        (length == 0 || memcmp(rt_string_data(value), bytes, length) == 0);
}

int main(int argc, char **argv) {
    int negative_only = argc == 2 && strcmp(argv[1], "--negative") == 0;
    rt_bdd_clear_state();
    rt_bdd_describe_start_rv(rt_string_new((const uint8_t*)"owner regression", 16));
    rt_bdd_it_start_rv(rt_string_new((const uint8_t*)"intentional unequal assertion", 29));
    rt_bdd_expect_eq_rv(rt_value_int(1), rt_value_int(2));
    if (rt_bdd_has_failure() != 1) return 10;
    rt_bdd_it_end(1);
    if (negative_only) {
        int64_t failures = rt_bdd_format_results();
        return failures == 1 ? 1 : 11;
    }
    rt_bdd_it_start_rv(rt_string_new((const uint8_t*)"equal assertion", 15));
    rt_bdd_expect_eq_rv(rt_value_int(7), rt_value_int(7));
    if (rt_bdd_has_failure() != 0) return 12;
    rt_bdd_it_end(1);
    if (rt_bdd_format_results() != 1) return 13;

    const uint8_t expected[] = {'A', 0, 0xed, 0x95, 0x9c, 0xea, 0xb8, 0x80};
    int64_t text = rt_string_new(expected, sizeof(expected));
    int64_t packed = rt_text_to_bytes(text);
    if (rt_array_len((SplArray*)(uintptr_t)packed) != sizeof(expected)) return 20;
    if (!text_matches(rt_bytes_to_text(packed), expected, sizeof(expected))) return 21;
    SplArray *slots = rt_array_new(0);
    for (size_t index = 0; index < sizeof(expected); index++) {
        if (!rt_array_push(slots, rt_value_int(expected[index]))) return 22;
    }
    if (!text_matches(rt_bytes_to_text((int64_t)(uintptr_t)slots), expected, sizeof(expected))) return 23;
    int64_t empty = rt_text_to_bytes(rt_string_new(NULL, 0));
    if (!text_matches(rt_bytes_to_text(empty), expected, 0)) return 24;
    puts("CORE_WINDOWS_BYTES_BDD_OWNER_PASS bdd_negative=detected bdd_positive=passed byte_layouts=2 utf8_and_nul=preserved");
    return 0;
}
