#include <stdint.h>
#include <stddef.h>

static unsigned char g_heap[64] __attribute__((aligned(16)));
static uintptr_t g_heap_off = 0;

#define BAREMETAL_ENABLE_ALIGNED_ALLOC 1
#include "examples/09_embedded/simple_os/arch/common/baremetal_bump_heap.h"

static int aligned16(const void *ptr)
{
    return ((uintptr_t)ptr & 15U) == 0;
}

int main(void)
{
    void *first = rv_alloc(1);
    if (!first || !aligned16(first) || g_heap_off != 16U) return 1;

    uintptr_t before = g_heap_off;
    if (rv_alloc((size_t)-1) != 0 || g_heap_off != before) return 2;
    if (rv_alloc((size_t)-8) != 0 || g_heap_off != before) return 3;

    g_heap_off = 1U;
    before = g_heap_off;
    if (rv_alloc_aligned((size_t)-1, 16U) != 0 || g_heap_off != before) return 4;
    if (rv_alloc_aligned(64U, 32U) != 0 || g_heap_off != before) return 5;

    g_heap_off = 1U;
    void *aligned = rv_alloc_aligned(1U, 32U);
    if (!aligned || ((uintptr_t)aligned & 31U) != 0U || g_heap_off != 48U) return 6;

    g_heap_off = 0;
    if (rv_calloc((size_t)-1, 2U) != 0 || g_heap_off != 0U) return 7;
    unsigned char *zeroed = (unsigned char *)rv_calloc(2U, 8U);
    if (!zeroed || g_heap_off != 16U) return 8;
    for (size_t i = 0; i < 16U; ++i) if (zeroed[i] != 0U) return 9;

    before = g_heap_off;
    if (rv_realloc(zeroed, 32U) != 0 || g_heap_off != before) return 10;
    if (!rv_realloc(0, 1U) || g_heap_off != before + 16U) return 11;

    g_heap_off = sizeof(g_heap) - 16U;
    if (!rv_alloc(1) || g_heap_off != sizeof(g_heap)) return 12;
    if (rv_alloc(1) != 0 || g_heap_off != sizeof(g_heap)) return 13;
    return 0;
}
