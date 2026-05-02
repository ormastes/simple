/*
 * FR-DRIVER-0005 — x86 (32-bit) DMA cache-maintenance runtime.
 *
 * Same coherency story as x86_64 — PCI/PCIe snoops the L1/L2, so
 * no clean/invalidate loops are needed. `mfence` was introduced in
 * SSE2 (Pentium 4) and is present on every chip our 32-bit baremetal
 * targets run on; for pre-SSE2 we'd fall back to a locked-op fence,
 * but that path is not supported here.
 */

#include "dma.h"

void __rt_dma_arch_clean(const void *addr, int64_t size) {
    (void)addr;
    (void)size;
    __asm__ volatile ("mfence" ::: "memory");
}

void __rt_dma_arch_invalidate(void *addr, int64_t size) {
    (void)addr;
    (void)size;
    __asm__ volatile ("mfence" ::: "memory");
}

int64_t __rt_dma_arch_cache_line_size(void) {
    return 64;
}
