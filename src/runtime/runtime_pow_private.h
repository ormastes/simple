/* Private integer power implementation shared by selected runtime providers. */
#ifndef SIMPLE_RUNTIME_POW_PRIVATE_H
#define SIMPLE_RUNTIME_POW_PRIVATE_H

#include <stdint.h>

static inline int64_t spl_runtime_integer_pow_v1(int64_t base, int64_t exp) {
    if (exp < 0) return 0;
    int64_t result = 1;
    while (exp > 0) {
        if (exp & 1) result *= base;
        exp >>= 1;
        /* The terminal square is unused and can overflow even when base^exp fits. */
        if (exp > 0) base *= base;
    }
    return result;
}

#endif
