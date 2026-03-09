// SPDX-License-Identifier: GPL-2.0
/**
 * @file core_ioctl.h
 * @brief IOCTL definitions for GPL core driver (/dev/gpu_p2p_core)
 */

#ifndef CORE_IOCTL_H
#define CORE_IOCTL_H

#ifdef __KERNEL__
#include <linux/types.h>
#include <linux/ioctl.h>
#else
#include <stdint.h>
#include <sys/ioctl.h>
#endif

/**
 * @brief Physical page information from NVIDIA bridge driver
 *
 * Array of these structures is passed from userspace (filled by NVIDIA bridge)
 * to the GPL core driver for DMA mapping.
 */
struct core_page_info {
	uint64_t phys_addr;  /**< Physical address of GPU page */
	uint32_t page_size;  /**< Page size in bytes (4K/64K/128K) */
	uint32_t reserved;   /**< Reserved for alignment */
};

/**
 * @brief IOVA segment output structure
 */
struct core_iova_seg {
	uint64_t dma_iova;  /**< DMA IOVA address for NVMe */
	uint64_t len;       /**< Length of contiguous segment */
};

/**
 * @brief DMA mapping request structure
 *
 * Userspace (wrapper library) provides:
 * - NVMe device BDF
 * - Array of physical pages from NVIDIA driver
 * - Output buffer for IOVA segments
 *
 * Core driver returns:
 * - Array of IOVA segments
 * - Number of segments created
 */
struct core_dma_req {
	uint64_t nvme_pci_bdf;           /**< NVMe device BDF (domain:bus:dev.fn) */
	uint32_t num_pages;              /**< Number of pages in pages_user_ptr */
	uint32_t flags;                  /**< Reserved flags */
	uint64_t pages_user_ptr;         /**< User pointer to core_page_info[] */
	uint64_t out_iova_segments_ptr;  /**< User pointer to core_iova_seg[] output */
	uint32_t max_segments;           /**< Max segments in output buffer */
	uint32_t num_segments;           /**< [OUT] Actual number of segments */
};

/**
 * @brief DMA unmap request structure
 */
struct core_dma_unmap_req {
	uint64_t mapping_handle;  /**< Handle from map operation */
	uint32_t flags;           /**< Reserved flags */
	uint32_t reserved;
};

/* IOCTL magic number */
#define GPU_P2P_CORE_IOCTL_MAGIC  'G'

/* IOCTL commands */
#define GPU_P2P_CORE_DMA_MAP    _IOWR(GPU_P2P_CORE_IOCTL_MAGIC, 0xC0, struct core_dma_req)
#define GPU_P2P_CORE_DMA_UNMAP  _IOW(GPU_P2P_CORE_IOCTL_MAGIC, 0xC1, struct core_dma_unmap_req)

/**
 * @brief NVMe queue mapping request for GPU-initiated I/O
 *
 * Maps host NVMe queues to GPU-accessible addresses using cuMemHostRegister.
 * The GPU kernel can then directly read/write the queue entries.
 *
 * Note: This does NOT map to GPU VRAM - it registers host memory for GPU access.
 */
struct core_nvme_queue_info {
	uint64_t sq_gpu_va;     /**< Output: GPU-accessible VA for SQ */
	uint64_t cq_gpu_va;     /**< Output: GPU-accessible VA for CQ */
	uint16_t sq_depth;      /**< Output: SQ depth (entries) */
	uint16_t cq_depth;      /**< Output: CQ depth (entries) */
	uint16_t qid;           /**< Output: Queue ID */
	uint8_t  sq_phase;      /**< Output: Current SQ phase bit */
	uint8_t  cq_phase;      /**< Output: Current CQ phase bit */
	uint32_t sq_tail;       /**< Output: Current SQ tail index */
	uint32_t cq_head;       /**< Output: Current CQ head index */
};

struct core_nvme_queue_req {
	uint64_t nvme_pci_bdf;  /**< Input: NVMe device BDF */
	uint64_t sq_host_va;    /**< Input: Host VA of SQ */
	uint64_t cq_host_va;    /**< Input: Host VA of CQ */
	uint64_t p2p_token;     /**< Input: GPU P2P token */
	uint32_t va_space;      /**< Input: GPU VA space */
	uint16_t qid;           /**< Input: Queue ID */
	uint16_t sq_depth;      /**< Input: SQ depth */
	uint16_t cq_depth;      /**< Input: CQ depth */
	uint16_t reserved1;     /**< Padding */
	uint32_t flags;         /**< Input: Reserved (must be 0) */
	uint32_t reserved2;     /**< Padding */
	struct core_nvme_queue_info out; /**< Output: GPU-accessible metadata */
};

/* Compat: userspace uses GPU_P2P_MAP_NVME_QUEUES with 0xE1 code */
#define GPU_P2P_CORE_MAP_NVME_QUEUES _IOWR(GPU_P2P_CORE_IOCTL_MAGIC, 0xE1, struct core_nvme_queue_req)

/**
 * @note GPU-to-NVMe MMIO doorbell writes are NOT SUPPORTED
 *
 * GPU kernels CANNOT write to PCIe MMIO regions (NVMe BAR0 doorbell registers).
 * This is a fundamental PCIe/GPU architecture limitation.
 *
 * Alternative doorbell mechanisms:
 * - Mode 2/3: Hardware DBC (NVMe controller polls shadow buffer in host memory)
 * - Mode 5: Software daemon (CPU polls shadow buffer, writes MMIO on GPU's behalf)
 *
 * See: 51.Knowledge_and_VFIO_Setup/51.2.NVMe_Fundamentals/README.md#gpu-cannot-access-mmio-doorbells
 */

#endif /* CORE_IOCTL_H */
