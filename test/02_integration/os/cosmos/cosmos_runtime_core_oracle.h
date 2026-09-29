#ifndef SIMPLE_TEST_COSMOS_RUNTIME_CORE_ORACLE_H
#define SIMPLE_TEST_COSMOS_RUNTIME_CORE_ORACLE_H

#include <stdint.h>

struct cosmos_runtime_oracle_division {
    uint32_t quotient;
    uint32_t remainder;
    int success;
};

void *cosmos_runtime_oracle_copy(void *dst, const void *src, uint32_t size);
void *cosmos_runtime_oracle_fill(void *dst, int value, uint32_t size);
struct cosmos_runtime_oracle_division cosmos_runtime_oracle_udivmod(
    uint32_t numerator, uint32_t denominator);
uint32_t cosmos_runtime_oracle_unsigned_div0_value(uint32_t numerator);
int32_t cosmos_runtime_oracle_signed_div0_value(int32_t numerator);
uint64_t cosmos_runtime_oracle_uidivmod(uint32_t numerator,
                                       uint32_t denominator);
int32_t cosmos_runtime_oracle_idiv(int32_t numerator, int32_t denominator);
uint64_t cosmos_runtime_oracle_idivmod(int32_t numerator,
                                      int32_t denominator);

#endif
