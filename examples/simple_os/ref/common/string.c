/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * common/string.c — Minimal freestanding memory utility functions
 *
 * These are required because clang may lower struct assignments and
 * zero-initialisations to calls to memcpy / memset even with
 * -ffreestanding.
 */

#include "common/string.h"

void *memcpy(void *dst, const void *src, uint32_t n)
{
    uint8_t       *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;

    for (uint32_t i = 0; i < n; i++) {
        d[i] = s[i];
    }
    return dst;
}

void *memset(void *s, int c, uint32_t n)
{
    uint8_t *p = (uint8_t *)s;

    for (uint32_t i = 0; i < n; i++) {
        p[i] = (uint8_t)c;
    }
    return s;
}

int memcmp(const void *s1, const void *s2, uint32_t n)
{
    const uint8_t *a = (const uint8_t *)s1;
    const uint8_t *b = (const uint8_t *)s2;

    for (uint32_t i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return (int)a[i] - (int)b[i];
        }
    }
    return 0;
}
