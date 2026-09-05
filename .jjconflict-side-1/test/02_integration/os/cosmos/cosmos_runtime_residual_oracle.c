/* Independent frozen C oracle: the six pre-extraction production bodies. */
#include "cosmos_runtime_residual_oracle.h"

#define ORACLE_SCAN_LIMIT 1000000U

void *cosmos_runtime_residual_oracle_memmove(void *dst, const void *src,
                                             unsigned int size) {
    volatile unsigned char *d = (volatile unsigned char *)dst;
    const volatile unsigned char *s = (const volatile unsigned char *)src;
    unsigned int i;
    if (dst == (void *)0 || src == (const void *)0 || dst == src) {
        return dst;
    }
    if (d < s) {
        for (i = 0; i < size; i = i + 1U) d[i] = s[i];
    } else {
        for (i = size; i != 0U;) {
            i = i - 1U;
            d[i] = s[i];
        }
    }
    return dst;
}

int cosmos_runtime_residual_oracle_memcmp(const void *left, const void *right,
                                          unsigned int size) {
    const volatile unsigned char *a = (const volatile unsigned char *)left;
    const volatile unsigned char *b = (const volatile unsigned char *)right;
    unsigned int i;
    if (left == (const void *)0 || right == (const void *)0)
        return left == right ? 0 : (left == (const void *)0 ? -1 : 1);
    for (i = 0; i < size; i = i + 1U)
        if (a[i] != b[i]) return (int)a[i] - (int)b[i];
    return 0;
}

unsigned int cosmos_runtime_residual_oracle_strlen(const char *text) {
    const volatile unsigned char *s = (const volatile unsigned char *)text;
    unsigned int i;
    if (text == (const char *)0) return 0U;
    for (i = 0; i < ORACLE_SCAN_LIMIT; i = i + 1U)
        if (s[i] == 0U) return i;
    return ORACLE_SCAN_LIMIT;
}

int cosmos_runtime_residual_oracle_strcmp(const char *left,
                                          const char *right) {
    const volatile unsigned char *a = (const volatile unsigned char *)left;
    const volatile unsigned char *b = (const volatile unsigned char *)right;
    unsigned int i;
    if (left == (const char *)0 || right == (const char *)0)
        return left == right ? 0 : (left == (const char *)0 ? -1 : 1);
    for (i = 0; i < ORACLE_SCAN_LIMIT; i = i + 1U) {
        if (a[i] != b[i]) return (int)a[i] - (int)b[i];
        if (a[i] == 0U) return 0;
    }
    return 0;
}

int cosmos_runtime_residual_oracle_strncmp(const char *left,
                                           const char *right,
                                           unsigned int size) {
    const volatile unsigned char *a = (const volatile unsigned char *)left;
    const volatile unsigned char *b = (const volatile unsigned char *)right;
    unsigned int i;
    if (left == (const char *)0 || right == (const char *)0)
        return left == right ? 0 : (left == (const char *)0 ? -1 : 1);
    for (i = 0; i < size; i = i + 1U) {
        if (a[i] != b[i]) return (int)a[i] - (int)b[i];
        if (a[i] == 0U) return 0;
    }
    return 0;
}

char *cosmos_runtime_residual_oracle_strncpy(char *dst, const char *src,
                                             unsigned int size) {
    volatile unsigned char *d = (volatile unsigned char *)dst;
    const volatile unsigned char *s = (const volatile unsigned char *)src;
    unsigned int i;
    if (dst == (char *)0 || src == (const char *)0) return dst;
    for (i = 0; i < size; i = i + 1U) {
        d[i] = s[i];
        if (s[i] == 0U) {
            i = i + 1U;
            for (; i < size; i = i + 1U) d[i] = 0U;
            break;
        }
    }
    return dst;
}
