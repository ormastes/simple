#include <limits.h>
#include <stdint.h>
#include <stdio.h>

#include "cosmos_runtime_core.h"
#include "cosmos_runtime_core_oracle.h"

typedef unsigned int cosmos_size_t;

void *memcpy(void *dst, const void *src, cosmos_size_t n);
void *memmove(void *dst, const void *src, cosmos_size_t n);
void *memset(void *dst, int value, cosmos_size_t n);
int memcmp(const void *left, const void *right, cosmos_size_t n);
cosmos_size_t strlen(const char *text);
int strcmp(const char *left, const char *right);
int strncmp(const char *left, const char *right, cosmos_size_t n);
char *strncpy(char *dst, const char *src, cosmos_size_t n);

void *rt_memcpy(void *dst, const void *src, cosmos_size_t n);
void *rt_memmove(void *dst, const void *src, cosmos_size_t n);
void *rt_memset(void *dst, int value, cosmos_size_t n);
int rt_memcmp(const void *left, const void *right, cosmos_size_t n);
cosmos_size_t rt_strlen(const char *text);
int rt_strcmp(const char *left, const char *right);
int rt_strncmp(const char *left, const char *right, cosmos_size_t n);

void __aeabi_memcpy(void *dst, const void *src, cosmos_size_t n);
void __aeabi_memcpy4(void *dst, const void *src, cosmos_size_t n);
void __aeabi_memcpy8(void *dst, const void *src, cosmos_size_t n);
void __aeabi_memmove(void *dst, const void *src, cosmos_size_t n);
void __aeabi_memmove4(void *dst, const void *src, cosmos_size_t n);
void __aeabi_memmove8(void *dst, const void *src, cosmos_size_t n);
void __aeabi_memclr(void *dst, cosmos_size_t n);
void __aeabi_memclr4(void *dst, cosmos_size_t n);
void __aeabi_memclr8(void *dst, cosmos_size_t n);
void __aeabi_memset(void *dst, cosmos_size_t n, int value);
void __aeabi_memset4(void *dst, cosmos_size_t n, int value);
void __aeabi_memset8(void *dst, cosmos_size_t n, int value);
unsigned int __aeabi_uidiv(unsigned int numerator, unsigned int denominator);
unsigned long long __aeabi_uidivmod(unsigned int numerator,
                                    unsigned int denominator);
int __aeabi_idiv(int numerator, int denominator);
unsigned long long __aeabi_idivmod(int numerator, int denominator);

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                  \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

static unsigned int idiv0_calls;
static int idiv0_argument;
static unsigned int oracle_cases;

int __aeabi_idiv0(int return_value) {
    idiv0_calls++;
    idiv0_argument = return_value;
    return return_value;
}

static void reset_idiv0(void) {
    idiv0_calls = 0U;
    idiv0_argument = 0;
}

static int bytes_equal(const unsigned char *actual,
                       const unsigned char *expected, unsigned int size) {
    unsigned int index;

    for (index = 0U; index < size; index++) {
        if (actual[index] != expected[index]) {
            return 0;
        }
    }
    return 1;
}

static void initialize_bytes(unsigned char *bytes, unsigned int size,
                             unsigned int salt) {
    unsigned int index;

    for (index = 0U; index < size; ++index) {
        bytes[index] = (unsigned char)((index * 37U + salt) & 0xFFU);
    }
}

static uint32_t oracle_next_u32(uint32_t *state) {
    *state = *state * UINT32_C(1664525) + UINT32_C(1013904223);
    return *state;
}

static int test_memory_and_aliases(void) {
    static const unsigned char source[8] = { 0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U };
    static const unsigned char copied[8] = { 0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U };
    static const unsigned char forward[10] =
        { 0U, 1U, 0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U };
    static const unsigned char backward[10] =
        { 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 8U, 9U };
    unsigned char actual[10];
    unsigned int index;

    for (index = 0U; index < 8U; index++) {
        actual[index] = 0xA5U;
    }
    CHECK(memcpy(actual, source, 8U) == actual);
    CHECK(bytes_equal(actual, copied, 8U));
    CHECK(rt_memcpy(actual, source, 8U) == actual);
    CHECK(bytes_equal(actual, copied, 8U));
    __aeabi_memcpy(actual, source, 8U);
    CHECK(bytes_equal(actual, copied, 8U));
    __aeabi_memcpy4(actual, source, 8U);
    CHECK(bytes_equal(actual, copied, 8U));
    __aeabi_memcpy8(actual, source, 8U);
    CHECK(bytes_equal(actual, copied, 8U));

    for (index = 0U; index < 10U; index++) {
        actual[index] = (unsigned char)index;
    }
    CHECK(memmove(actual + 2U, actual, 8U) == actual + 2U);
    CHECK(bytes_equal(actual, forward, 10U));
    for (index = 0U; index < 10U; index++) {
        actual[index] = (unsigned char)index;
    }
    CHECK(rt_memmove(actual, actual + 2U, 8U) == actual);
    CHECK(bytes_equal(actual, backward, 10U));
    for (index = 0U; index < 10U; index++) {
        actual[index] = (unsigned char)index;
    }
    __aeabi_memmove4(actual + 2U, actual, 8U);
    CHECK(bytes_equal(actual, forward, 10U));
    for (index = 0U; index < 10U; index++) {
        actual[index] = (unsigned char)index;
    }
    __aeabi_memmove8(actual, actual + 2U, 8U);
    CHECK(bytes_equal(actual, backward, 10U));
    for (index = 0U; index < 10U; index++) {
        actual[index] = (unsigned char)index;
    }
    __aeabi_memmove(actual + 2U, actual, 8U);
    CHECK(bytes_equal(actual, forward, 10U));

    CHECK(memset(actual, 0x5A, 10U) == actual);
    for (index = 0U; index < 10U; index++) {
        CHECK(actual[index] == 0x5AU);
    }
    CHECK(rt_memset(actual, 0x33, 10U) == actual);
    __aeabi_memset(actual, 10U, 0x11);
    __aeabi_memset4(actual, 10U, 0x22);
    __aeabi_memset8(actual, 10U, 0x44);
    for (index = 0U; index < 10U; index++) {
        CHECK(actual[index] == 0x44U);
    }
    __aeabi_memclr(actual, 10U);
    __aeabi_memclr4(actual, 10U);
    __aeabi_memclr8(actual, 10U);
    for (index = 0U; index < 10U; index++) {
        CHECK(actual[index] == 0U);
    }
    CHECK(memcmp(source, copied, 8U) == 0);
    CHECK(rt_memcmp(source, copied, 8U) == 0);
    CHECK(memcmp(source, forward, 3U) > 0);
    return 0;
}

static int test_strings(void) {
    char destination[8];

    CHECK(strlen("cosmos") == 6U);
    CHECK(rt_strlen("cosmos") == 6U);
    CHECK(strcmp("cosmos", "cosmos") == 0);
    CHECK(rt_strcmp("cosmos", "cosmos") == 0);
    CHECK(strcmp("cosmos", "cosmot") < 0);
    CHECK(strncmp("cosmos", "cosmot", 5U) == 0);
    CHECK(rt_strncmp("cosmos", "cosmot", 6U) < 0);
    CHECK(strncpy(destination, "hi", 8U) == destination);
    CHECK(destination[0] == 'h' && destination[1] == 'i');
    CHECK(destination[2] == '\0' && destination[7] == '\0');
    return 0;
}

static int test_division(void) {
    unsigned long long result;

    CHECK(__aeabi_uidiv(37U, 5U) == 7U);
    result = __aeabi_uidivmod(37U, 5U);
    CHECK((unsigned int)result == 7U);
    CHECK((unsigned int)(result >> 32) == 2U);
    CHECK(__aeabi_idiv(-37, 5) == -7);
    result = __aeabi_idivmod(-37, 5);
    CHECK((int)(unsigned int)result == -7);
    CHECK((int)(unsigned int)(result >> 32) == -2);
    CHECK(__aeabi_idiv(INT_MIN, -1) == INT_MIN);

    reset_idiv0();
    CHECK(__aeabi_uidiv(0U, 0U) == 0U);
    CHECK(idiv0_calls == 1U && idiv0_argument == 0);
    reset_idiv0();
    CHECK(__aeabi_uidiv(1U, 0U) == UINT_MAX);
    CHECK(idiv0_calls == 1U && (unsigned int)idiv0_argument == UINT_MAX);
    reset_idiv0();
    result = __aeabi_uidivmod(UINT_MAX, 0U);
    CHECK((unsigned int)result == UINT_MAX);
    CHECK((unsigned int)(result >> 32) == UINT_MAX);
    CHECK(idiv0_calls == 1U && (unsigned int)idiv0_argument == UINT_MAX);
    reset_idiv0();
    CHECK(__aeabi_idiv(1, 0) == INT_MAX);
    CHECK(idiv0_calls == 1U && idiv0_argument == INT_MAX);
    reset_idiv0();
    CHECK(__aeabi_idiv(-1, 0) == INT_MIN);
    CHECK(idiv0_calls == 1U && idiv0_argument == INT_MIN);
    reset_idiv0();
    CHECK(__aeabi_idiv(0, 0) == 0);
    CHECK(idiv0_calls == 1U && idiv0_argument == 0);
    reset_idiv0();
    result = __aeabi_idivmod(-1, 0);
    CHECK((int)(unsigned int)result == INT_MIN);
    CHECK((int)(unsigned int)(result >> 32) == -1);
    CHECK(idiv0_calls == 1U && idiv0_argument == INT_MIN);
    return 0;
}

static int check_unsigned_oracle_case(uint32_t numerator,
                                      uint32_t denominator) {
    const struct cosmos_runtime_oracle_division expected =
        cosmos_runtime_oracle_udivmod(numerator, denominator);
    uint32_t quotient = UINT32_C(0xA5A5A5A5);
    uint32_t remainder = UINT32_C(0x5A5A5A5A);
    uint64_t packed;
    uint32_t scalar;

    reset_idiv0();
    scalar = __aeabi_uidiv(numerator, denominator);
    CHECK(scalar == (expected.success != 0
                         ? expected.quotient
                         : cosmos_runtime_oracle_unsigned_div0_value(
                               numerator)));
    CHECK(idiv0_calls == (denominator == 0U ? 1U : 0U));
    if (denominator == 0U) {
        CHECK((uint32_t)idiv0_argument ==
              cosmos_runtime_oracle_unsigned_div0_value(numerator));
    }

    reset_idiv0();
    packed = __aeabi_uidivmod(numerator, denominator);
    CHECK(packed == cosmos_runtime_oracle_uidivmod(numerator, denominator));
    CHECK(idiv0_calls == (denominator == 0U ? 1U : 0U));
    if (denominator == 0U) {
        CHECK((uint32_t)idiv0_argument ==
              cosmos_runtime_oracle_unsigned_div0_value(numerator));
    }

    CHECK(cosmos_runtime_core_udivmod(numerator, denominator,
                                      &quotient, &remainder) ==
          expected.success);
    if (expected.success != 0) {
        CHECK(quotient == expected.quotient);
        CHECK(remainder == expected.remainder);
    } else {
        CHECK(quotient == UINT32_C(0xA5A5A5A5));
        CHECK(remainder == UINT32_C(0x5A5A5A5A));
    }
    ++oracle_cases;
    return 0;
}

static int check_signed_oracle_case(int32_t numerator, int32_t denominator) {
    uint64_t packed;
    int32_t scalar;

    reset_idiv0();
    scalar = __aeabi_idiv(numerator, denominator);
    CHECK(scalar == cosmos_runtime_oracle_idiv(numerator, denominator));
    CHECK(idiv0_calls == (denominator == 0 ? 1U : 0U));
    if (denominator == 0) {
        CHECK(idiv0_argument ==
              cosmos_runtime_oracle_signed_div0_value(numerator));
    }

    reset_idiv0();
    packed = __aeabi_idivmod(numerator, denominator);
    CHECK(packed == cosmos_runtime_oracle_idivmod(numerator, denominator));
    CHECK(idiv0_calls == (denominator == 0 ? 1U : 0U));
    if (denominator == 0) {
        CHECK(idiv0_argument ==
              cosmos_runtime_oracle_signed_div0_value(numerator));
    }
    ++oracle_cases;
    return 0;
}

static int test_memory_oracle_parity(void) {
    unsigned char source[96];
    unsigned char actual[96];
    unsigned char expected[96];
    unsigned int size;

    initialize_bytes(source, 96U, 11U);
    for (size = 0U; size <= 64U; ++size) {
        initialize_bytes(actual, 96U, 29U);
        initialize_bytes(expected, 96U, 29U);
        CHECK(cosmos_runtime_oracle_copy(expected, source, size) == expected);
        CHECK(memcpy(actual, source, size) == actual);
        CHECK(bytes_equal(actual, expected, 96U));
        ++oracle_cases;

        initialize_bytes(actual, 96U, 47U);
        initialize_bytes(expected, 96U, 47U);
        CHECK(cosmos_runtime_oracle_fill(expected, (int)(0x120U + size),
                                         size) == expected);
        CHECK(memset(actual, (int)(0x120U + size), size) == actual);
        CHECK(bytes_equal(actual, expected, 96U));
        ++oracle_cases;
    }

    initialize_bytes(actual, 96U, 61U);
    initialize_bytes(expected, 96U, 61U);
    CHECK(memcpy(NULL, source, 4U) == NULL);
    ++oracle_cases;
    CHECK(memcpy(actual, NULL, 4U) == actual);
    CHECK(bytes_equal(actual, expected, 96U));
    ++oracle_cases;
    CHECK(memcpy(actual, source, 0U) == actual);
    CHECK(bytes_equal(actual, expected, 96U));
    ++oracle_cases;
    CHECK(memset(NULL, 0xA5, 4U) == NULL);
    ++oracle_cases;
    CHECK(memset(actual, 0xA5, (0U)) == actual);
    CHECK(bytes_equal(actual, expected, 96U));
    ++oracle_cases;
    return 0;
}

static int test_division_oracle_parity(void) {
    static const uint32_t unsigned_values[] = {
        0U, 1U, 2U, 3U, 4U, 5U, 7U, 8U,
        15U, 16U, 31U, 37U, UINT32_C(0x7FFFFFFF),
        UINT32_C(0x80000000), UINT32_C(0xFFFFFFFE), UINT32_MAX
    };
    static const int32_t signed_values[] = {
        INT32_MIN, INT32_MIN + 1, -65537, -37, -5, -2, -1, 0,
        1, 2, 5, 37, 65537, INT32_MAX - 1, INT32_MAX
    };
    uint32_t state = UINT32_C(0xC05A05F1);
    unsigned int left;
    unsigned int right;
    unsigned int iteration;
    uint32_t remainder = 0U;

    for (left = 0U; left < sizeof(unsigned_values) / sizeof(unsigned_values[0]);
         ++left) {
        for (right = 0U;
             right < sizeof(unsigned_values) / sizeof(unsigned_values[0]);
             ++right) {
            CHECK(check_unsigned_oracle_case(unsigned_values[left],
                                              unsigned_values[right]) == 0);
        }
    }
    for (left = 0U; left < sizeof(signed_values) / sizeof(signed_values[0]);
         ++left) {
        for (right = 0U;
             right < sizeof(signed_values) / sizeof(signed_values[0]);
             ++right) {
            CHECK(check_signed_oracle_case(signed_values[left],
                                            signed_values[right]) == 0);
        }
    }

    for (iteration = 0U; iteration < 4096U; ++iteration) {
        const uint32_t unsigned_numerator = oracle_next_u32(&state);
        const uint32_t unsigned_denominator = oracle_next_u32(&state);
        const int32_t signed_numerator = (int32_t)oracle_next_u32(&state);
        const int32_t signed_denominator = (int32_t)oracle_next_u32(&state);

        CHECK(check_unsigned_oracle_case(unsigned_numerator,
                                          unsigned_denominator) == 0);
        CHECK(check_signed_oracle_case(signed_numerator,
                                       signed_denominator) == 0);
    }

    CHECK(cosmos_runtime_core_udivmod(1U, 1U, NULL, &remainder) == 0);
    ++oracle_cases;
    CHECK(cosmos_runtime_core_udivmod(1U, 1U, &remainder, NULL) == 0);
    ++oracle_cases;

    CHECK(cosmos_runtime_core_unsigned_div0_value(0U) ==
          cosmos_runtime_oracle_unsigned_div0_value(0U));
    ++oracle_cases;
    CHECK(cosmos_runtime_core_unsigned_div0_value(1U) ==
          cosmos_runtime_oracle_unsigned_div0_value(1U));
    ++oracle_cases;
    CHECK(cosmos_runtime_core_unsigned_div0_value(UINT32_MAX) ==
          cosmos_runtime_oracle_unsigned_div0_value(UINT32_MAX));
    ++oracle_cases;
    CHECK(cosmos_runtime_core_signed_div0_value(-1) ==
          cosmos_runtime_oracle_signed_div0_value(-1));
    ++oracle_cases;
    CHECK(cosmos_runtime_core_signed_div0_value(0) ==
          cosmos_runtime_oracle_signed_div0_value(0));
    ++oracle_cases;
    CHECK(cosmos_runtime_core_signed_div0_value(1) ==
          cosmos_runtime_oracle_signed_div0_value(1));
    ++oracle_cases;
    return 0;
}

static unsigned int count_outcomes(uint64_t mask) {
    unsigned int count = 0U;

    while (mask != 0U) {
        count += (unsigned int)(mask & UINT64_C(1));
        mask >>= 1U;
    }
    return count;
}

static int test_runtime_core_decision_manifest(void) {
    const uint64_t mask = cosmos_runtime_core_coverage_mask();
    const uint64_t required = cosmos_runtime_core_coverage_required();
    const uint64_t decisions = cosmos_runtime_core_coverage_decisions();
    const unsigned int outcomes = count_outcomes(mask & required);

    CHECK(decisions == UINT64_C(13));
    CHECK(required == UINT64_C(0x03FFFFFF));
    CHECK(mask == required);
    CHECK(outcomes == 26U);
    CHECK(oracle_cases == 8816U);
    printf("COSMOS_RUNTIME_CORE_ORACLE_CASES %u\n", oracle_cases);
    printf("COSMOS_RUNTIME_CORE_SIMPLE_DECISIONS %llu/13\n",
           (unsigned long long)decisions);
    printf("COSMOS_RUNTIME_CORE_SIMPLE_OUTCOMES %u/26\n", outcomes);
    return 0;
}

int main(void) {
    cosmos_runtime_core_coverage_reset();
    CHECK(test_memory_and_aliases() == 0);
    CHECK(test_strings() == 0);
    CHECK(test_division() == 0);
    CHECK(test_memory_oracle_parity() == 0);
    CHECK(test_division_oracle_parity() == 0);
    CHECK(test_runtime_core_decision_manifest() == 0);
    puts("cosmos runtime contract: PASS");
    return 0;
}
