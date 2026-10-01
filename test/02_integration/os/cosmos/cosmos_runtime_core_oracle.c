/*
 * Independent host C oracle for the pure-Simple Cosmos runtime core.
 *
 * This file deliberately does not include or call the migrated implementation.
 * Nonzero division uses the host C operators; explicit guards avoid signed C
 * overflow at INT32_MIN / -1 and define the retained ARM divide-by-zero policy.
 */

#include "cosmos_runtime_core_oracle.h"

#include <limits.h>
#include <stddef.h>

void *cosmos_runtime_oracle_copy(void *dst, const void *src, uint32_t size) {
    unsigned char *output = (unsigned char *)dst;
    const unsigned char *input = (const unsigned char *)src;
    uint32_t index;

    if (dst == NULL || src == NULL) {
        return dst;
    }
    for (index = 0U; index < size; ++index) {
        output[index] = input[index];
    }
    return dst;
}

void *cosmos_runtime_oracle_fill(void *dst, int value, uint32_t size) {
    unsigned char *output = (unsigned char *)dst;
    uint32_t index;

    if (dst == NULL) {
        return dst;
    }
    for (index = 0U; index < size; ++index) {
        output[index] = (unsigned char)value;
    }
    return dst;
}

struct cosmos_runtime_oracle_division cosmos_runtime_oracle_udivmod(
    uint32_t numerator, uint32_t denominator) {
    struct cosmos_runtime_oracle_division result;

    if (denominator == 0U) {
        result.quotient = 0U;
        result.remainder = 0U;
        result.success = 0;
        return result;
    }
    result.quotient = numerator / denominator;
    result.remainder = numerator % denominator;
    result.success = 1;
    return result;
}

uint32_t cosmos_runtime_oracle_unsigned_div0_value(uint32_t numerator) {
    return numerator == 0U ? 0U : UINT32_MAX;
}

int32_t cosmos_runtime_oracle_signed_div0_value(int32_t numerator) {
    if (numerator > 0) {
        return INT32_MAX;
    }
    if (numerator < 0) {
        return INT32_MIN;
    }
    return 0;
}

uint64_t cosmos_runtime_oracle_uidivmod(uint32_t numerator,
                                       uint32_t denominator) {
    const struct cosmos_runtime_oracle_division division =
        cosmos_runtime_oracle_udivmod(numerator, denominator);
    uint32_t quotient;
    uint32_t remainder;

    if (division.success != 0) {
        quotient = division.quotient;
        remainder = division.remainder;
    } else {
        quotient = cosmos_runtime_oracle_unsigned_div0_value(numerator);
        remainder = numerator;
    }
    return ((uint64_t)remainder << 32U) | quotient;
}

int32_t cosmos_runtime_oracle_idiv(int32_t numerator, int32_t denominator) {
    if (denominator == 0) {
        return cosmos_runtime_oracle_signed_div0_value(numerator);
    }
    if (numerator == INT32_MIN && denominator == -1) {
        return INT32_MIN;
    }
    return numerator / denominator;
}

uint64_t cosmos_runtime_oracle_idivmod(int32_t numerator,
                                      int32_t denominator) {
    int32_t quotient;
    int32_t remainder;

    if (denominator == 0) {
        quotient = cosmos_runtime_oracle_signed_div0_value(numerator);
        remainder = numerator;
    } else if (numerator == INT32_MIN && denominator == -1) {
        quotient = INT32_MIN;
        remainder = 0;
    } else {
        quotient = numerator / denominator;
        remainder = numerator % denominator;
    }
    return ((uint64_t)(uint32_t)remainder << 32U) | (uint32_t)quotient;
}
