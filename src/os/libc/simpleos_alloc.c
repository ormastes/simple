/*
 * SimpleOS Libc Shim — Aligned memory allocation
 *
 * Provides posix_memalign, aligned_alloc, memalign, valloc, pvalloc.
 * This facade must never return an allocation that the primary allocator does
 * not own: callers are entitled to pass every successful result to free().
 * The current dlmalloc owner guarantees 16-byte payload alignment, but it has
 * no registered over-aligned allocation format.  Requests above that proven
 * contract therefore fail closed until the allocator grows an owned aligned
 * block representation.
 */

#include "include/stdlib.h"
#include "include/errno.h"
#include "include/string.h"

extern int errno;

#ifndef SIMPLEOS_MALLOC_ALIGNMENT
#define SIMPLEOS_MALLOC_ALIGNMENT 16
#endif

static int _valid_alignment(size_t alignment) {
    return alignment >= sizeof(void *) &&
           (alignment & (alignment - 1)) == 0;
}

/* ====================================================================
 * posix_memalign — aligned allocation (POSIX)
 * ==================================================================== */

int posix_memalign(void **memptr, size_t alignment, size_t size) {
    /* alignment must be a power of two and >= sizeof(void *) */
    if (!_valid_alignment(alignment))
        return EINVAL;

    if (size == 0) {
        *memptr = NULL;
        return 0;
    }

    /*
     * Do not use an anonymous mmap or return an interior over-allocation.
     * Neither has an ownership record understood by simpleos_dlmalloc free()
     * and both make a valid free() silently leak.  The allocator's payload
     * layout is explicitly rounded to this alignment.
     */
    if (alignment > SIMPLEOS_MALLOC_ALIGNMENT)
        return ENOMEM;

    void *raw = malloc(size);
    if (!raw) return ENOMEM;
    *memptr = raw;
    return 0;
}

/* ====================================================================
 * C11 / legacy aligned allocation wrappers
 * ==================================================================== */

void *aligned_alloc(size_t alignment, size_t size) {
    void *ptr = NULL;
    if (!_valid_alignment(alignment) || size % alignment != 0) {
        errno = EINVAL;
        return NULL;
    }
    int result = posix_memalign(&ptr, alignment, size);
    if (result != 0) {
        errno = result;
        return NULL;
    }
    return ptr;
}

void *memalign(size_t alignment, size_t size) {
    return aligned_alloc(alignment, size);
}

void *valloc(size_t size) {
    (void)size;
    errno = ENOMEM;
    return NULL;
}

void *pvalloc(size_t size) {
    (void)size;
    errno = ENOMEM;
    return NULL;
}
