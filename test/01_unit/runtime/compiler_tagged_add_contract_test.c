/* Link against the real core-C runtime, not a mocked tag implementation.
 * Negative modes must terminate through the runtime's error convention. */
#include <stdint.h>
#include <string.h>
#include "runtime.h"

int main(int argc, char** argv) {
    if (argc > 1) {
        if (strcmp(argv[1], "nil") == 0)
            (void)rt_tagged_add(rt_value_nil(), rt_value_int(1));
        else if (strcmp(argv[1], "uint") == 0)
            (void)rt_tagged_add(rt_value_u64(-1), rt_value_int(1));
        else if (strcmp(argv[1], "unregistered") == 0)
            /* runtime_native.c: TAG_INT=0, TAG_HEAP=1; 4096 is aligned. */
            (void)rt_tagged_add(INT64_C(4096) | INT64_C(1), rt_value_int(1));
        else return 30;
        return 31; /* A negative mode returning is a failed rejection. */
    }
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(5), rt_value_int(3))) != 8) return 1;
    if (rt_value_as_float(rt_tagged_add(rt_value_float(2.5), rt_value_float(0.5))) != 3.0) return 2;
    if (rt_value_as_float(rt_tagged_add(rt_value_float(2.5), rt_value_int(3))) != 5.5) return 3;
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(INT64_C(1152921504606846975)), rt_value_int(1))) != INT64_C(1152921504606846976)) return 4;
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(INT64_MAX), rt_value_int(1))) != INT64_MIN) return 5;
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(INT64_MIN), rt_value_int(-1))) != INT64_MAX) return 6;
    if (rt_any_add(5, 3) != 8) return 7; /* Existing raw ABI stays intact. */
    int64_t prefix = rt_string_new((const uint8_t*)"n=", 2);
    if (strcmp(rt_interp_cstr(rt_tagged_add(prefix, rt_value_int(INT64_C(1152921504606846976)))), "n=1152921504606846976") != 0) return 8;
    if (strcmp(rt_interp_cstr(rt_tagged_add(prefix, rt_value_u64(-1))), "n=18446744073709551615") != 0) return 9;
    /* Existing text+nil coercion renders nil as the empty string. */
    if (strcmp(rt_interp_cstr(rt_tagged_add(prefix, rt_value_nil())), "n=") != 0) return 10;
    return 0;
}
