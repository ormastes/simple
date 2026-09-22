#include <stdint.h>

int64_t simple_dynlib_return42(void) {
    return INT64_C(42);
}

int64_t simple_dynlib_return0(void) {
    return INT64_C(0);
}

int64_t simple_dynlib_return_neg7(void) {
    return INT64_C(-7);
}
