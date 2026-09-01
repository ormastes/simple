#define malloc simpleos_test_malloc
#define free simpleos_test_free
#define calloc simpleos_test_calloc
#define realloc simpleos_test_realloc

#include <stddef.h>
#include <stdint.h>

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c,
                         int64_t d, int64_t e)
{
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    return -1; /* select the controlled Linux-host mmap fallback */
}

#include "src/os/libc/simpleos_dlmalloc.c"

static int aligned16(const void *ptr)
{
    return ((uintptr_t)ptr & 15U) == 0;
}

int main(void)
{
    if (simpleos_test_malloc((size_t)-1) != NULL) return 1;
    if (simpleos_test_calloc((size_t)-1, 2U) != NULL) return 2;

    /* Keep a large remainder live in the free list, then request an exact
     * freed block.  Traversal must validate the remaining node without
     * treating its existence as corruption. */
    unsigned char *exact = (unsigned char *)simpleos_test_malloc(128U);
    unsigned char *exact_guard = (unsigned char *)simpleos_test_malloc(128U);
    if (!exact || !exact_guard) return 3;
    simpleos_test_free(exact);
    unsigned char *exact_reuse = (unsigned char *)simpleos_test_malloc(128U);
    if (!exact_reuse || !aligned16(exact_reuse)) return 4;
    simpleos_test_free(exact_reuse);
    simpleos_test_free(exact_guard);

    unsigned char *first = (unsigned char *)simpleos_test_malloc(24U);
    unsigned char *second = (unsigned char *)simpleos_test_malloc(24U);
    if (!first || !second || !aligned16(first) || !aligned16(second)) return 5;
    for (size_t i = 0; i < 24U; ++i) first[i] = (unsigned char)(i + 1U);

    simpleos_test_free(first + 1U); /* interior pointer must not mutate state */
    simpleos_test_free(first);
    simpleos_test_free(first);      /* double free must not relink the node */
    unsigned char *reuse = (unsigned char *)simpleos_test_malloc(24U);
    if (!reuse || !aligned16(reuse)) return 6;

    unsigned char *grown = (unsigned char *)simpleos_test_realloc(second, 96U);
    if (!grown || !aligned16(grown)) return 7;
    if (simpleos_test_realloc(grown + 1U, 128U) != NULL) return 8;
    simpleos_test_free(grown);
    simpleos_test_free(reuse);

    unsigned char *split_left = (unsigned char *)simpleos_test_malloc(128U);
    unsigned char *split_right = (unsigned char *)simpleos_test_malloc(24U);
    if (!split_left || !split_right) return 9;
    simpleos_test_free(split_left);
    unsigned char *split_reuse = (unsigned char *)simpleos_test_malloc(32U);
    if (!split_reuse || !aligned16(split_reuse)) return 10;
    simpleos_test_free(split_reuse);
    simpleos_test_free(split_right);

    unsigned char *left = (unsigned char *)simpleos_test_malloc(24U);
    unsigned char *middle = (unsigned char *)simpleos_test_malloc(24U);
    unsigned char *right = (unsigned char *)simpleos_test_malloc(24U);
    if (!left || !middle || !right) return 11;
    middle[0] = 0x5a;
    block_header *right_header = (block_header *)(right - HEADER_SIZE);
    right_header->prev_size += BLOCK_SIZE((block_header *)(middle - HEADER_SIZE));
    simpleos_test_free(right); /* corrupt backlink must reject without merge */
    if (middle[0] != 0x5a) return 12;
    right_header->prev_size = BLOCK_SIZE((block_header *)(middle - HEADER_SIZE));
    simpleos_test_free(right);
    simpleos_test_free(middle);
    simpleos_test_free(left);

    while (simpleos_test_malloc(65537U)) { }
    if (region_count != MAX_REGIONS) return 13;
    if (simpleos_test_malloc(65537U) != NULL) return 14;
    if (!simpleos_test_malloc(16U)) return 15; /* existing free-list remains usable */

    /* A reciprocal self-cycle is metadata corruption, not an excuse to spin
     * forever while holding the allocator lock. */
    free_node *poisoned = free_list_sentinel.next;
    if (poisoned == &free_list_sentinel) return 16;
    poisoned->next = poisoned;
    poisoned->prev = poisoned;
    if (simpleos_test_malloc(16U) != NULL) return 17;
    return 0;
}
