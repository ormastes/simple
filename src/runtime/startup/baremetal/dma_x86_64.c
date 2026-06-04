/*
 * FR-DRIVER-0005 — x86_64 DMA cache-maintenance runtime.
 *
 * x86_64 is cache-coherent with respect to DMA on every platform we
 * target (PCIe + snooping MESI). Clean/invalidate therefore collapse
 * to an `mfence`: the device sees CPU stores in program order, and
 * subsequent CPU loads see device stores without manual invalidation.
 *
 * Cache line: 64 bytes on every current Intel/AMD microarch; ARM-
 * style line sizes do not apply here.
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
