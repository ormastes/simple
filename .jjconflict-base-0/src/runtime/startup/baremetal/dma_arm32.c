/*
 * FR-DRIVER-0005 — ARMv7 (arm32) DMA cache-maintenance runtime.
 *
 * ARMv7-A uses CP15 coprocessor writes to drive data-cache
 * maintenance by MVA (modified virtual address):
 *   - Clean to PoC:      MCR p15, 0, <Rd>, c7, c10, 1  (DCCMVAC)
 *   - Invalidate to PoC: MCR p15, 0, <Rd>, c7, c6,  1  (DCIMVAC)
 * Each op acts on a single cache line; we loop the line stride
 * (32 B on Cortex-A8/A9/A5; 64 B on A15/A7 — 32 B is the safe
 * smallest-common-denominator, so we over-clean on larger lines
 * which is correct and cheap).
 *
 * `DSB SY` (MCR p15, 0, Rd, c7, c10, 4 on pre-v7ve) orders the
 * maintenance with device access. ARMv7 assemblers accept the
 * mnemonic `dsb sy`.
 */

#include "dma.h"

#define ARM32_CACHE_LINE 32

static void clean_range(const void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("dsb sy" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)ARM32_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += ARM32_CACHE_LINE) {
        /* DCCMVAC — clean by MVA to PoC. */
        __asm__ volatile ("mcr p15, 0, %0, c7, c10, 1" :: "r" (p) : "memory");
    }
    __asm__ volatile ("dsb sy" ::: "memory");
}

static void invalidate_range(void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("dsb sy" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)ARM32_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += ARM32_CACHE_LINE) {
        /* DCIMVAC — invalidate by MVA to PoC. */
        __asm__ volatile ("mcr p15, 0, %0, c7, c6, 1" :: "r" (p) : "memory");
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
    return ARM32_CACHE_LINE;
}
