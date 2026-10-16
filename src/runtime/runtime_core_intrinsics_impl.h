/* Private implementation of the intrinsic runtime ABI.
 * Include in exactly one selected C provider per runtime composition. */
#ifndef SIMPLE_RUNTIME_CORE_INTRINSICS_IMPL_H
#define SIMPLE_RUNTIME_CORE_INTRINSICS_IMPL_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int64_t __simple_pow(int64_t base, int64_t exp) {
    if (exp < 0) return 0;
    int64_t result = 1;
    while (exp > 0) {
        if (exp & 1) result *= base;
        base *= base;
        exp >>= 1;
    }
    return result;
}

int64_t __simple_intrinsic_unreachable(void) {
    fprintf(stderr, "PANIC: reached unreachable intrinsic\n");
    exit(1);
    return 0;
}

/* IEEE-754 bit-cast helpers. Several Simple modules declare
 * `extern fn f32_from_bits(u32) -> f32` (nogc_sync_mut/ptr/raw.spl,
 * torch/dyn_sffi_tensor_ops.spl, nogc_sync_mut/gpu/memory.spl); the
 * entry-closure symbol registry binds those pub extern declarations over
 * lib/common/binary_io.spl's own local definition, so binary_io's internal
 * calls are emitted against the bare extern name and the stage2 link fails
 * with an undefined symbol (SIMPLE_NO_STUB_FALLBACK=1 lane). The pure-Simple
 * reconstruction in binary_io cannot preserve NaN payload/sign; a real
 * union bit-cast is exact and no consumer depends on the lossy behavior. */
float f32_from_bits(uint32_t bits) {
    union { uint32_t u; float f; } c;
    c.u = bits;
    return c.f;
}

double f64_from_bits(uint64_t bits) {
    union { uint64_t u; double d; } c;
    c.u = bits;
    return c.d;
}

int64_t __simple_intrinsic_trap(void) {
    fprintf(stderr, "PANIC: trap intrinsic\n");
    exit(1);
    return 0;
}

int64_t __simple_intrinsic_assume(int64_t cond) {
    (void)cond;
    return 0;
}

int64_t __simple_intrinsic_likely(int64_t cond) {
    return cond;
}

int64_t __simple_intrinsic_unlikely(int64_t cond) {
    return cond;
}

int64_t __simple_intrinsic_bounds_check(int64_t index, int64_t len) {
    if (index < 0 || index >= len) {
        fprintf(stderr, "PANIC: bounds_check intrinsic index=%lld len=%lld\n",
                (long long)index, (long long)len);
        exit(1);
    }
    return 0;
}

int64_t __simple_intrinsic_prefetch(void* ptr) {
    (void)ptr;
    return 0;
}

int64_t __simple_intrinsic_memcpy(void* dst, const void* src, int64_t n) {
    memcpy(dst, src, (size_t)n);
    return 0;
}

int64_t __simple_intrinsic_memset(void* dst, int64_t val, int64_t n) {
    memset(dst, (int)val, (size_t)n);
    return 0;
}

#endif /* SIMPLE_RUNTIME_CORE_INTRINSICS_IMPL_H */
