/*
 * FR-DRIVER-0005 — aarch64 DMA cache-maintenance runtime.
 *
 * ARMv8 is NOT implicitly coherent with non-snooping DMA masters.
 * The driver contract is:
 *   - sync_for_device: `DC CVAC` (clean by VA to Point-of-Coherency)
 *     over the buffer range, then `DSB SY` so the clean completes
 *     before the device is kicked.
 *   - sync_for_cpu: `DC IVAC` (invalidate by VA to PoC) + `DSB SY`
 *     so the CPU drops cache lines that may be stale after the
 *     device write. Invalidate requires the address range to be
 *     cache-line aligned; the shared pool aligns to a page so this
 *     holds trivially.
 *
 * CTR_EL0.DminLine gives the true line size in log2(words); we
 * hard-code 64 bytes here for all current Cortex-A cores that
 * SimpleOS targets. If a future platform exposes a different line
 * size we can probe CTR_EL0 from the kernel init path and override.
 *
 * References: ARMv8-A ARM §D7.2 "Cache maintenance instructions",
 * and Linux's arch/arm64/mm/cache.S for the canonical loop pattern.
 */

#include "dma.h"

#define ARM64_CACHE_LINE 64

static void clean_range(const void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("dsb sy" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)ARM64_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += ARM64_CACHE_LINE) {
        __asm__ volatile ("dc cvac, %0" :: "r" (p) : "memory");
    }
    __asm__ volatile ("dsb sy" ::: "memory");
}

static void invalidate_range(void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("dsb sy" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)ARM64_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += ARM64_CACHE_LINE) {
        __asm__ volatile ("dc ivac, %0" :: "r" (p) : "memory");
    }
    __asm__ volatile ("dsb sy" ::: "memory");
}

void __rt_dma_arch_clean(const void *addr, int64_t size) {
    clean_range(addr, size);
}

void __rt_dma_arch_invalidate(void *addr, int64_t size) {
    invalidate_range(addr, size);
}

int64_t __rt_dma_arch_cache_line_size(void) {
    return ARM64_CACHE_LINE;
}
