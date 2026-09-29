#define SIMPLEOS_DLMALLOC_TESTING 1
#define malloc simpleos_test_malloc
#define free simpleos_test_free
#define calloc simpleos_test_calloc
#define realloc simpleos_test_realloc

#include <stddef.h>
#include <stdint.h>

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c,
                         int64_t d, int64_t e) {
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    return -1;
}

#include "src/os/libc/simpleos_dlmalloc.c"

int main(void) {
    unsigned char *left = (unsigned char *)simpleos_test_malloc(128U);
    unsigned char *right = (unsigned char *)simpleos_test_malloc(24U);
    if (!left || !right) return 1;
    simpleos_test_free(left);

    /* First insertion is the split remainder. It fails, then the exact former
     * free node must be restored, so the next allocation remains usable. */
    simpleos_dlmalloc_test_fail_next_insert();
    if (simpleos_test_malloc(32U) != NULL) return 2;
    if (allocator_poisoned) return 3;
    unsigned char *reused = (unsigned char *)simpleos_test_malloc(32U);
    if (!reused) return 4;
    simpleos_test_free(reused);

    /* A damaged successor backlink must reject free before it mutates either
     * the live block or its free predecessor.  Restore the injected damage so
     * the fixture can verify the normal coalesce path afterwards. */
    block_header *right_header = (block_header *)(right - HEADER_SIZE);
    size_t saved_prev_size = right_header->prev_size;
    right_header->prev_size += 16U;
    simpleos_test_free(right);
    if (!BLOCK_INUSE(right_header)) return 8;
    right_header->prev_size = saved_prev_size;
    simpleos_test_free(right);

    /* Exhaust the free list/regions only in metadata by starting a separate
     * fresh-process test path is unnecessary: the forced failure of a later
     * fresh remainder must poison rather than publish a ghost allocation. */
    free_list_sentinel.next = &free_list_sentinel;
    free_list_sentinel.prev = &free_list_sentinel;
    region_count = 0;
    allocator_poisoned = 0;
    simpleos_dlmalloc_test_fail_next_insert();
    if (simpleos_test_malloc(32U) != NULL) return 5;
    if (!allocator_poisoned || region_count != 0) return 6;
    if (simpleos_test_malloc(16U) != NULL) return 7;
    return 0;
}
