#include <limits.h>
#include <stdint.h>
#include <stdio.h>

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

int main(void) {
    CHECK(test_memory_and_aliases() == 0);
    CHECK(test_strings() == 0);
    CHECK(test_division() == 0);
    puts("cosmos runtime contract: PASS");
    return 0;
}
