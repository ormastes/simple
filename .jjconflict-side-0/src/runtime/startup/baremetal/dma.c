/*
 * FR-DRIVER-0005 — Shared DMA pool + sync dispatch (baremetal).
 *
 * Page-aligned static .bss pool, slot-table keyed by handle, plus
 * rt_dma_sync_for_{device,cpu} that dispatch to the per-arch clean /
 * invalidate hooks defined in dma_<arch>.c.
 *
 * Single-threaded usage assumed (driver probe happens on one CPU
 * before any scheduler is up); we do not lock here. When SMP boot
 * is added, a spinlock around alloc/free is the minimal change.
 *
 * Build: compiled into spl_crt_baremetal_<arch>.a with exactly one
 * dma_<arch>.c sibling, chosen by CMake.
 */

#include "dma.h"

/* Page-aligned static pool. __attribute__((aligned)) on an array
 * in .bss guarantees the array's base is page-aligned; crt_baremetal's
 * __spl_zero_bss() zeroes it before main() runs. */
static uint8_t g_pool[RT_DMA_POOL_BYTES] __attribute__((aligned(RT_DMA_PAGE_SIZE)));

/* Bump pointer into g_pool (bytes consumed). */
static int64_t g_pool_used = 0;

/* Slot table — index i in [0, RT_DMA_MAX_SLOTS) is the handle. */
struct rt_dma_slot {
    void   *virt;   /* non-NULL iff in_use */
    int64_t phys;   /* identity-mapped: equals (int64_t)(uintptr_t)virt */
    int64_t size;   /* rounded up to page */
    int     in_use;
};

static struct rt_dma_slot g_slots[RT_DMA_MAX_SLOTS];

static int64_t align_up(int64_t x, int64_t a) {
    return (x + (a - 1)) & ~(a - 1);
}

int64_t rt_dma_alloc(int64_t size, int32_t dir_raw) {
    (void)dir_raw; /* direction hint — reserved for NUMA / coherent-pool selection later */

    if (size <= 0) {
        return -1;
    }

    const int64_t req = align_up(size, RT_DMA_PAGE_SIZE);

    /* Find a free slot. */
    int slot = -1;
    for (int i = 0; i < RT_DMA_MAX_SLOTS; i++) {
        if (!g_slots[i].in_use) {
            slot = i;
            break;
        }
    }
    if (slot < 0) {
        return -1;
    }

    /* Bump-allocate from the pool. No freelist: DMA buffers live
     * for the driver's lifetime; reuse requires rebooting in this
     * seed. TODO(FR-DRIVER-0006): proper reclaim once an allocator
     * is in place. */
    if (g_pool_used + req > (int64_t)RT_DMA_POOL_BYTES) {
        return -1;
    }

    uint8_t *p = &g_pool[g_pool_used];
    g_pool_used += req;

    g_slots[slot].virt   = (void *)p;
    g_slots[slot].phys   = (int64_t)(uintptr_t)p;
    g_slots[slot].size   = req;
    g_slots[slot].in_use = 1;

    return (int64_t)slot;
}

void rt_dma_free(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_MAX_SLOTS) {
        return;
    }
    /* Mark free; bump pool is not reclaimed (see TODO above). */
    g_slots[handle].in_use = 0;
    g_slots[handle].virt   = (void *)0;
    g_slots[handle].phys   = 0;
    g_slots[handle].size   = 0;
}

int64_t rt_dma_virt_of(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_MAX_SLOTS || !g_slots[handle].in_use) {
        return 0;
    }
    return (int64_t)(uintptr_t)g_slots[handle].virt;
}

int64_t rt_dma_phys_of(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_MAX_SLOTS || !g_slots[handle].in_use) {
        return 0;
    }
    return g_slots[handle].phys;
}

void rt_dma_sync_for_device(int64_t handle, int32_t dir_raw) {
    if (handle < 0 || handle >= RT_DMA_MAX_SLOTS || !g_slots[handle].in_use) {
        /* Still issue a full barrier so the caller's stores drain even
         * when we have no slot metadata (consistent with the Simple
         * fallback's barrier-only behaviour). */
        __rt_dma_arch_clean((const void *)0, 0);
        return;
    }
    /* ToDevice / Bidirectional: CPU just wrote; clean cache so the
     * device reads committed data. FromDevice: no writes from CPU,
     * but the store barrier in dma.spl already ran — a clean here is
     * defensive and cheap. */
    (void)dir_raw;
    __rt_dma_arch_clean(g_slots[handle].virt, g_slots[handle].size);
}

void rt_dma_sync_for_cpu(int64_t handle, int32_t dir_raw) {
    if (handle < 0 || handle >= RT_DMA_MAX_SLOTS || !g_slots[handle].in_use) {
        __rt_dma_arch_invalidate((void *)0, 0);
        return;
    }
    /* FromDevice / Bidirectional: device just wrote; invalidate so
     * CPU re-reads from DRAM. ToDevice: no-op semantically, but the
     * invalidate is a conservative way to drop speculative fills. */
    (void)dir_raw;
    __rt_dma_arch_invalidate(g_slots[handle].virt, g_slots[handle].size);
}

int64_t rt_dma_cache_line_size(void) {
    return __rt_dma_arch_cache_line_size();
}
