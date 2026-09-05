/*
 * FR-DRIVER-0005 — Per-arch DMA runtime (shared header)
 *
 * Shared declarations for the coherent-DMA pool + per-arch cache-
 * maintenance dispatch. The shared layer owns:
 *   - a fixed-size, page-aligned static .bss pool
 *   - a slot-table keyed by handle (0..RT_DMA_MAX_SLOTS-1)
 *   - the public rt_dma_{alloc,free,virt_of,phys_of} ABI
 *   - rt_dma_cache_line_size() (AC-3 of FR-DRIVER-0005)
 *   - rt_dma_sync_for_device / rt_dma_sync_for_cpu that delegate to
 *     __rt_dma_arch_clean / __rt_dma_arch_invalidate (one per arch).
 *
 * Each dma_<arch>.c supplies:
 *   - void __rt_dma_arch_clean(const void *addr, int64_t size);
 *   - void __rt_dma_arch_invalidate(void *addr, int64_t size);
 *   - int64_t __rt_dma_arch_cache_line_size(void);
 *
 * virt == phys in this seed layer: baremetal boot is identity-mapped
 * at the point drivers run; paging, if any, comes later and can
 * override rt_dma_phys_of via a hook table.
 */

#ifndef SPL_RT_DMA_H
#define SPL_RT_DMA_H

#include <stddef.h>
#include <stdint.h>

/* Pool geometry — tuneable per kernel image. 256 KiB / 4 KiB pages
 * gives 64 pages, sufficient for a handful of descriptor rings on a
 * small driver set without inflating every baremetal image. */
#ifndef RT_DMA_POOL_BYTES
#define RT_DMA_POOL_BYTES (256 * 1024)
#endif

#ifndef RT_DMA_PAGE_SIZE
#define RT_DMA_PAGE_SIZE 4096
#endif

#ifndef RT_DMA_MAX_SLOTS
#define RT_DMA_MAX_SLOTS 32
#endif

/* Direction enum raw values — keep in sync with dir_to_raw() in
 * src/lib/nogc_sync_mut/io/dma.spl. */
#define RT_DMA_DIR_TO_DEVICE     0
#define RT_DMA_DIR_FROM_DEVICE   1
#define RT_DMA_DIR_BIDIRECTIONAL 2

/* Public ABI — called from Simple via SFFI. Defined in dma.c. */
int64_t rt_dma_alloc(int64_t size, int32_t dir_raw);
void    rt_dma_free(int64_t handle);
int64_t rt_dma_virt_of(int64_t handle);
int64_t rt_dma_phys_of(int64_t handle);
void    rt_dma_sync_for_device(int64_t handle, int32_t dir_raw);
void    rt_dma_sync_for_cpu(int64_t handle, int32_t dir_raw);
int64_t rt_dma_cache_line_size(void);

/* Per-arch hooks — defined in dma_<arch>.c. */
void    __rt_dma_arch_clean(const void *addr, int64_t size);
void    __rt_dma_arch_invalidate(void *addr, int64_t size);
int64_t __rt_dma_arch_cache_line_size(void);

#endif /* SPL_RT_DMA_H */
