/*
 * FR-DRIVER-0005 — riscv64 DMA cache-maintenance runtime.
 *
 * Base RV64 has no standard cache-ops instruction; coherency is
 * implementation-defined. Two worlds:
 *
 *   - Coherent (SiFive U74 + default QEMU `virt`): `fence rw,rw`
 *     is sufficient — caches snoop DMA masters. `sync_for_device`
 *     and `sync_for_cpu` collapse to a full fence.
 *   - Non-coherent + Zicbom (T-Head C906 / newer Andes): emit
 *     `cbo.clean 0(rs1)` for clean and `cbo.inval 0(rs1)` for
 *     invalidate over the buffer range, followed by a fence.
 *
 * Zicbom is gated by `__riscv_zicbom` which the toolchain defines
 * when `-march=...+zicbom` is in effect. Without Zicbom the fence-
 * only path is software-correct on coherent HW and fails closed on
 * non-coherent HW (device sees stale data) — that is a kernel-
 * config bug, not ours.
 *
 * Line size: 64 bytes covers all extant RV implementations with
 * Zicbom; smaller is safe (over-clean), larger would under-clean
 * so 64 is the floor.
 */

#include "dma.h"

#define RISCV64_CACHE_LINE 64

#if defined(__riscv_zicbom)

static void clean_range(const void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("fence rw, rw" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)RISCV64_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += RISCV64_CACHE_LINE) {
        __asm__ volatile ("cbo.clean 0(%0)" :: "r" (p) : "memory");
    }
    __asm__ volatile ("fence rw, rw" ::: "memory");
}

static void invalidate_range(void *addr, int64_t size) {
    if (size <= 0) {
        __asm__ volatile ("fence rw, rw" ::: "memory");
        return;
    }
    uintptr_t start = (uintptr_t)addr & ~((uintptr_t)RISCV64_CACHE_LINE - 1);
    uintptr_t end   = (uintptr_t)addr + (uintptr_t)size;
    for (uintptr_t p = start; p < end; p += RISCV64_CACHE_LINE) {
        __asm__ volatile ("cbo.inval 0(%0)" :: "r" (p) : "memory");
    }
    __asm__ volatile ("fence rw, rw" ::: "memory");
}

#else /* !__riscv_zicbom — coherent-HW path */

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
    return RISCV64_CACHE_LINE;
}
