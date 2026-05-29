/*
 * SimpleOS Libc Shim — Aligned memory allocation
 *
 * Provides posix_memalign, aligned_alloc, memalign, valloc, pvalloc.
 * Page-aligned (or larger) requests use mmap directly via syscall 10.
 * Smaller alignments over-allocate from malloc and align the pointer.
 */

#include "include/stdlib.h"
#include "include/errno.h"
#include "include/string.h"

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);
extern int errno;

#define PAGE_SIZE 4096

/* ====================================================================
 * posix_memalign — aligned allocation (POSIX)
 * ==================================================================== */

int posix_memalign(void **memptr, size_t alignment, size_t size) {
    /* alignment must be a power of two and >= sizeof(void *) */
    if (alignment < sizeof(void *) || (alignment & (alignment - 1)) != 0)
        return EINVAL;

    if (size == 0) {
        *memptr = NULL;
        return 0;
    }

    /* For page-aligned or larger, use mmap directly */
    if (alignment >= PAGE_SIZE) {
        size_t alloc_size = (size + alignment - 1) & ~(alignment - 1);
        alloc_size = (alloc_size + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);
        /* syscall 10 = Mmap: addr=0, len, prot=3 (RW), flags=0, fd=0 */
        int64_t addr = simpleos_syscall(10, 0, alloc_size, 3, 0, 0);
        if (addr <= 0) return ENOMEM;
        *memptr = (void *)addr;
        return 0;
    }

    /* For small alignments, over-allocate and align */
    void *raw = malloc(size + alignment);
    if (!raw) return ENOMEM;
    uintptr_t aligned = ((uintptr_t)raw + alignment - 1) & ~(alignment - 1);
    *memptr = (void *)aligned;
    return 0;
}

/* ====================================================================
 * C11 / legacy aligned allocation wrappers
 * ==================================================================== */

void *aligned_alloc(size_t alignment, size_t size) {
    void *ptr = NULL;
    if (posix_memalign(&ptr, alignment, size) != 0) return NULL;
    return ptr;
}

void *memalign(size_t alignment, size_t size) {
    return aligned_alloc(alignment, size);
}

void *valloc(size_t size) {
    return aligned_alloc(PAGE_SIZE, size);
}

void *pvalloc(size_t size) {
    size_t aligned_size = (size + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);
    return aligned_alloc(PAGE_SIZE, aligned_size);
}
