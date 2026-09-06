#ifndef SIMPLE_OS_COSMOS_RUNTIME_CORE_H
#define SIMPLE_OS_COSMOS_RUNTIME_CORE_H

/* Pure-Simple runtime-core exports consumed only by cosmos_runtime.c/tests. */
void *cosmos_runtime_core_copy(void *dst, const void *src, unsigned int size);
void *cosmos_runtime_core_fill(void *dst, int value, unsigned int size);
int cosmos_runtime_core_udivmod(unsigned int numerator,
                                unsigned int denominator,
                                unsigned int *quotient,
                                unsigned int *remainder);
unsigned int cosmos_runtime_core_unsigned_div0_value(unsigned int numerator);
int cosmos_runtime_core_signed_div0_value(int numerator);

/* Actual-execution decision instrumentation owned by the Simple core. */
void cosmos_runtime_core_coverage_reset(void);
unsigned long long cosmos_runtime_core_coverage_mask(void);
unsigned long long cosmos_runtime_core_coverage_required(void);
unsigned long long cosmos_runtime_core_coverage_decisions(void);

#endif
