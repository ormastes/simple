/*
 * FR-DRIVER-0005 — riscv32 DMA cache-maintenance runtime.
 *
 * Mirrors dma_riscv64.c: base RV32 has no standard cache ops so
 * `fence rw,rw` is the only portable barrier. Zicbom provides
 * `cbo.clean` / `cbo.inval` when the toolchain defines
 * `__riscv_zicbom` (e.g. `-march=rv32imac_zicbom`).
 *
 * Line size: 32 bytes is typical on embedded RV32 MCUs (BOOM-lite,
 * Andes N25), but 64 is the safe minimum covering larger targets.
 * We pick 32 B here — the smaller floor — so iteration covers every
 * line; over-clean on 64-B-line cores is correct and cheap.
 */

#include "dma.h"

#define RISCV32_CACHE_LINE 32

#if defined(__riscv_zicbom)

static void clean_range(const void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("fence rw, rw" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)RISCV32_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += RISCV32_CACHE_LINE) {
        __asm__ volatile ("cbo.clean 0(%0)" :: "r" (p) : "memory");
    }
    __asm__ volatile ("fence rw, rw" ::: "memory");
}

static void invalidate_range(void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("fence rw, rw" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)RISCV32_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += RISCV32_CACHE_LINE) {
        __asm__ volatile ("cbo.inval 0(%0)" :: "r" (p) : "memory");
    }
    __asm__ volatile ("fence rw, rw" ::: "memory");
}

#else /* !__riscv_zicbom */

static void clean_range(const void *addr, int64_t size) {
    (void)addr;
    (void)size;
    __asm__ volatile ("fence rw, rw" ::: "memory");
}

static void invalidate_range(void *addr, int64_t size) {
    (void)addr;
    (void)size;
    __asm__ volatile ("fence rw, rw" ::: "memory");
}

#endif /* __riscv_zicbom */

void __rt_dma_arch_clean(const void *addr, int64_t size) {
    clean_range(addr, size);
}

void __rt_dma_arch_invalidate(void *addr, int64_t size) {
    invalidate_range(addr, size);
}

int64_t __rt_dma_arch_cache_line_size(void) {
    return RISCV32_CACHE_LINE;
}
