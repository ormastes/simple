/*
 * Cosmos+ ARMv7 freestanding runtime primitives.
 *
 * This is the small C ABI used before the full Simple runtime is handed off.
 * It owns only deterministic memory, string, and compiler support.  Allocation
 * belongs to the Simple runtime and is intentionally not provided here.
 */

#include "cosmos_hal.h"
#include "cosmos_runtime_core.h"
#include "cosmos_runtime_residual.h"

typedef unsigned int cosmos_u32;
typedef int cosmos_i32;
typedef unsigned long long cosmos_u64;
typedef unsigned int cosmos_size_t;

#define COSMOS_RUNTIME_SCAN_LIMIT COSMOS_POLL_LIMIT

static volatile cosmos_u32 cosmos_runtime_ready;

static void *cosmos_copy(void *dst, const void *src, cosmos_size_t n) {
    return cosmos_runtime_core_copy(dst, src, n);
}

static void *cosmos_fill(void *dst, int value, cosmos_size_t n) {
    return cosmos_runtime_core_fill(dst, value, n);
}

void *memcpy(void *dst, const void *src, cosmos_size_t n) {
    return cosmos_copy(dst, src, n);
}

void *memmove(void *dst, const void *src, cosmos_size_t n) {
    return cosmos_runtime_residual_memmove(dst, src, n);
}

void *memset(void *dst, int value, cosmos_size_t n) {
    return cosmos_fill(dst, value, n);
}

int memcmp(const void *left, const void *right, cosmos_size_t n) {
    return cosmos_runtime_residual_memcmp(left, right, n);
}

cosmos_size_t strlen(const char *text) {
    return cosmos_runtime_residual_strlen(text);
}

int strcmp(const char *left, const char *right) {
    return cosmos_runtime_residual_strcmp(left, right);
}

int strncmp(const char *left, const char *right, cosmos_size_t n) {
    return cosmos_runtime_residual_strncmp(left, right, n);
}

char *strncpy(char *dst, const char *src, cosmos_size_t n) {
    return cosmos_runtime_residual_strncpy(dst, src, n);
}

void *rt_memcpy(void *dst, const void *src, cosmos_size_t n) {
    return cosmos_copy(dst, src, n);
}

void *rt_memmove(void *dst, const void *src, cosmos_size_t n) {
    return memmove(dst, src, n);
}

void *rt_memset(void *dst, int value, cosmos_size_t n) {
    return cosmos_fill(dst, value, n);
}

int rt_memcmp(const void *left, const void *right, cosmos_size_t n) {
    return memcmp(left, right, n);
}

cosmos_size_t rt_strlen(const char *text) {
    return strlen(text);
}

int rt_strcmp(const char *left, const char *right) {
    return strcmp(left, right);
}

int rt_strncmp(const char *left, const char *right, cosmos_size_t n) {
    return strncmp(left, right, n);
}

void __aeabi_memcpy(void *dst, const void *src, cosmos_size_t n) {
    cosmos_copy(dst, src, n);
}

void __aeabi_memcpy4(void *dst, const void *src, cosmos_size_t n) {
    cosmos_copy(dst, src, n);
}

void __aeabi_memcpy8(void *dst, const void *src, cosmos_size_t n) {
    cosmos_copy(dst, src, n);
}

void __aeabi_memmove(void *dst, const void *src, cosmos_size_t n) {
    memmove(dst, src, n);
}

void __aeabi_memmove4(void *dst, const void *src, cosmos_size_t n) {
    memmove(dst, src, n);
}

void __aeabi_memmove8(void *dst, const void *src, cosmos_size_t n) {
    memmove(dst, src, n);
}

void __aeabi_memclr(void *dst, cosmos_size_t n) {
    cosmos_fill(dst, 0, n);
}

void __aeabi_memclr4(void *dst, cosmos_size_t n) {
    cosmos_fill(dst, 0, n);
}

void __aeabi_memclr8(void *dst, cosmos_size_t n) {
    cosmos_fill(dst, 0, n);
}

void __aeabi_memset(void *dst, cosmos_size_t n, int value) {
    cosmos_fill(dst, value, n);
}

void __aeabi_memset4(void *dst, cosmos_size_t n, int value) {
    cosmos_fill(dst, value, n);
}

void __aeabi_memset8(void *dst, cosmos_size_t n, int value) {
    cosmos_fill(dst, value, n);
}

static int cosmos_udivmod(cosmos_u32 numerator, cosmos_u32 denominator,
                          cosmos_u32 *quotient, cosmos_u32 *remainder) {
    return cosmos_runtime_core_udivmod(numerator, denominator,
                                       quotient, remainder);
}

__attribute__((weak)) int __aeabi_idiv0(int return_value) {
    return return_value;
}

static cosmos_u32 cosmos_unsigned_div0_value(cosmos_u32 numerator) {
    return cosmos_runtime_core_unsigned_div0_value(numerator);
}

static cosmos_i32 cosmos_signed_div0_value(cosmos_i32 numerator) {
    return cosmos_runtime_core_signed_div0_value(numerator);
}

unsigned int __aeabi_uidiv(unsigned int numerator, unsigned int denominator) {
    cosmos_u32 quotient;
    cosmos_u32 remainder;
    if (!cosmos_udivmod(numerator, denominator, &quotient, &remainder)) {
        return (unsigned int)__aeabi_idiv0(
            (int)cosmos_unsigned_div0_value(numerator));
    }
    return quotient;
}

cosmos_u64 __aeabi_uidivmod(unsigned int numerator, unsigned int denominator) {
    cosmos_u32 quotient;
    cosmos_u32 remainder;
    if (!cosmos_udivmod(numerator, denominator, &quotient, &remainder)) {
        quotient = (cosmos_u32)__aeabi_idiv0(
            (int)cosmos_unsigned_div0_value(numerator));
        remainder = numerator;
    }
    return ((cosmos_u64)remainder << 32) | quotient;
}

int __aeabi_idiv(int numerator, int denominator) {
    cosmos_u32 un;
    cosmos_u32 ud;
    cosmos_u32 uq;
    cosmos_u32 ur;
    cosmos_u32 negative;
    if (denominator == 0) {
        return __aeabi_idiv0(cosmos_signed_div0_value(numerator));
    }
    negative = ((numerator < 0) ^ (denominator < 0)) ? 1U : 0U;
    un = numerator < 0 ? 0U - (cosmos_u32)numerator : (cosmos_u32)numerator;
    ud = denominator < 0 ? 0U - (cosmos_u32)denominator : (cosmos_u32)denominator;
    (void)cosmos_udivmod(un, ud, &uq, &ur);
    return (int)(negative != 0U ? 0U - uq : uq);
}

cosmos_u64 __aeabi_idivmod(int numerator, int denominator) {
    cosmos_u32 un;
    cosmos_u32 ud;
    cosmos_u32 quotient;
    cosmos_u32 remainder;
    if (denominator == 0) {
        quotient = (cosmos_u32)__aeabi_idiv0(
            cosmos_signed_div0_value(numerator));
        remainder = (cosmos_u32)numerator;
        return ((cosmos_u64)remainder << 32) | quotient;
    }
    un = numerator < 0 ? 0U - (cosmos_u32)numerator : (cosmos_u32)numerator;
    ud = denominator < 0 ? 0U - (cosmos_u32)denominator : (cosmos_u32)denominator;
    (void)cosmos_udivmod(un, ud, &quotient, &remainder);
    if ((numerator < 0) ^ (denominator < 0)) {
        quotient = 0U - quotient;
    }
    if (numerator < 0) {
        remainder = 0U - remainder;
    }
    return ((cosmos_u64)remainder << 32) | quotient;
}

void __aeabi_unwind_cpp_pr0(void) {
    __builtin_trap();
}

void __aeabi_unwind_cpp_pr1(void) {
    __builtin_trap();
}

void cosmos_runtime_init(void) {
    cosmos_runtime_ready = 0U;
    cosmos_data_sync_barrier();
    cosmos_runtime_ready = 1U;
    cosmos_data_sync_barrier();
    cosmos_instruction_sync_barrier();
}

int cosmos_runtime_selftest(void) {
    unsigned char source[32] = "cosmos-runtime";
    unsigned char copy[32];
    unsigned char overlap[32];
    unsigned char text[32];
    volatile cosmos_u32 unsigned_max = ~0U;
    volatile cosmos_i32 signed_min = (cosmos_i32)(1U << 31);
    volatile cosmos_i32 signed_max = (cosmos_i32)~(1U << 31);
    cosmos_u32 quotient;
    cosmos_u32 remainder;
    cosmos_u64 result;
    cosmos_runtime_init();
    if (cosmos_runtime_ready != 1U) {
        return COSMOS_INVALID;
    }
    memset(copy, 0xA5, sizeof(copy));
    rt_memcpy(copy, source, sizeof(source));
    if (memcmp(copy, source, sizeof(source)) != 0) {
        return COSMOS_HW_ERROR;
    }
    memset(overlap, 0, sizeof(overlap));
    rt_memcpy(overlap, "0123456789", 11U);
    memmove(overlap + 2, overlap, 8U);
    if (strncmp((const char *)overlap, "0101234567", 10U) != 0) {
        return COSMOS_HW_ERROR;
    }
    strncpy((char *)text, "handoff", sizeof(text));
    if (strlen((const char *)text) != 7U ||
        strcmp((const char *)text, "handoff") != 0 ||
        rt_strcmp((const char *)text, "handoff") != 0) {
        return COSMOS_INVALID;
    }
    result = __aeabi_uidivmod(unsigned_max, unsigned_max);
    if ((cosmos_u32)result != 1U || (cosmos_u32)(result >> 32) != 0U ||
        __aeabi_uidiv(unsigned_max, 2U) != 0x7FFFFFFFU) {
        return COSMOS_INVALID;
    }
    result = __aeabi_idivmod(signed_min, signed_max);
    if ((cosmos_u32)result != ~0U ||
        (cosmos_u32)(result >> 32) != ~0U ||
        __aeabi_idiv(signed_min, -1) != signed_min ||
        __aeabi_idiv(signed_max, -1) != -signed_max) {
        return COSMOS_INVALID;
    }
    quotient = 0xA5A5A5A5U;
    remainder = 0x5A5A5A5AU;
    if (cosmos_udivmod(1U, 0U, &quotient, &remainder) != 0 ||
        quotient != 0xA5A5A5A5U || remainder != 0x5A5A5A5AU ||
        __aeabi_idiv0(123) != 123 ||
        __aeabi_uidiv(1U, 0U) != ~0U ||
        __aeabi_uidiv(0U, 0U) != 0U ||
        __aeabi_idiv(1, 0) != (cosmos_i32)0x7FFFFFFFU ||
        __aeabi_idiv(-1, 0) != (cosmos_i32)0x80000000U ||
        __aeabi_idiv(0, 0) != 0) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}
