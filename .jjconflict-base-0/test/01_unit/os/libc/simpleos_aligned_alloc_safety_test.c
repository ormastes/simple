#define malloc simpleos_test_malloc
#define free simpleos_test_free
#define calloc simpleos_test_calloc
#define realloc simpleos_test_realloc

#include <stddef.h>
#include <stdint.h>

int errno;

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c,
                         int64_t d, int64_t e)
{
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    return -1; /* controlled Linux-host mmap fallback for dlmalloc */
}

#include "src/os/libc/simpleos_dlmalloc.c"
#include "src/os/libc/simpleos_alloc.c"

int main(void)
{
    void *ptr = (void *)(uintptr_t)0x1234;
    if (posix_memalign(&ptr, 16U, 64U) != 0 || !ptr) return 1;
    if (((uintptr_t)ptr & 15U) != 0) return 2;
    simpleos_test_free(ptr);

    ptr = (void *)(uintptr_t)0x5678;
    if (posix_memalign(&ptr, 64U, 64U) != ENOMEM) return 3;
    if (ptr != (void *)(uintptr_t)0x5678) return 4;
    if (posix_memalign(&ptr, 3U, 64U) != EINVAL) return 5;
    errno = 0;
    if (aligned_alloc(16U, 17U) != NULL || errno != EINVAL) return 6;
    errno = 0;
    if (aligned_alloc(64U, 64U) != NULL || errno != ENOMEM) return 7;
    errno = 0;
    if (valloc(1U) != NULL || errno != ENOMEM) return 8;
    errno = 0;
    if (pvalloc((size_t)-1) != NULL || errno != ENOMEM) return 9;
    return 0;
}
