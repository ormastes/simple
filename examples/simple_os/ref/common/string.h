/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * common/string.h — Minimal freestanding memory utility functions
 *
 * No libc dependency. Provides memcpy/memset/memcmp that clang may
 * implicitly emit for struct assignments and zero-initialisation.
 */

#ifndef SIMPLE_OS_STRING_H
#define SIMPLE_OS_STRING_H

#include "common/types.h"

void *memcpy(void *dst, const void *src, uint32_t n);
void *memset(void *s, int c, uint32_t n);
int   memcmp(const void *s1, const void *s2, uint32_t n);

#endif /* SIMPLE_OS_STRING_H */
