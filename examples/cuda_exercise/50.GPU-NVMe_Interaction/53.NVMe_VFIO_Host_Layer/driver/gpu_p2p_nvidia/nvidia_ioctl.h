// SPDX-License-Identifier: Proprietary
/**
 * @file nvidia_ioctl.h
 * @brief IOCTL definitions for NVIDIA bridge driver (/dev/gpu_p2p_nvidia)
 */

#ifndef NVIDIA_IOCTL_H
#define NVIDIA_IOCTL_H

#ifdef __KERNEL__
#include <linux/types.h>
#include <linux/ioctl.h>
#else
#include <stdint.h>
#include <sys/ioctl.h>
#endif

/**
 * @brief Physical page information output structure
 *
 * NVIDIA bridge fills this with information from nvidia_p2p_page_table.
 */
struct nv_page_info {
	uint64_t phys_addr;  /**< Physical address */
	uint32_t page_size;  /**< Page size in bytes */
	uint32_t reserved;
};

/**
 * @brief Get GPU pages request structure
 *
 * Userspace provides CUDA P2P token and GPU virtual address.
 * NVIDIA bridge calls nvidia_p2p_get_pages() and returns:
 * - Opaque page table handle
 * - Array of physical page information
 */
struct nv_get_pages_req {
	uint64_t gpu_va;             /**< GPU virtual address */
	uint64_t bytes;              /**< Size in bytes */
	uint64_t p2p_token;          /**< CUDA P2P token */
	uint32_t va_space;           /**< CUDA VA space ID */
	uint32_t flags;              /**< Reserved flags */
	uint64_t page_table_handle;  /**< [OUT] Opaque handle for cleanup */
	uint64_t pages_user_ptr;     /**< [OUT] Pointer to nv_page_info[] */
	uint32_t num_pages;          /**< [OUT] Number of pages */
	uint32_t page_size;          /**< [OUT] Page size type (4K/64K/128K) */
};

/**
 * @brief Put GPU pages request structure
 *
 * Userspace provides the handle from get_pages.
 * NVIDIA bridge calls nvidia_p2p_put_pages() and nvidia_p2p_free_page_table().
 */
struct nv_put_pages_req {
	uint64_t page_table_handle;  /**< Handle from get_pages */
	uint64_t gpu_va;             /**< GPU virtual address (for validation) */
	uint64_t p2p_token;          /**< CUDA P2P token */
	uint32_t va_space;           /**< CUDA VA space ID */
	uint32_t flags;              /**< Reserved flags */
};

/**
 * @brief Map GPU pages into a peer device IOMMU (e.g., NVMe) and return IOVA list.
 */
struct nv_dma_map_req {
	uint64_t page_table_handle;     /**< Handle from get_pages */
	uint64_t nvme_pci_bdf;          /**< Encoded BDF: domain<<32 | bus<<16 | dev<<8 | fn */
	uint64_t dma_user_ptr;          /**< [IN] userspace buffer for IOVAs (uint64_t[]) */
	uint32_t max_entries;           /**< [IN] max entries writable to dma_user_ptr */
	uint32_t num_entries;           /**< [OUT] total DMA entries produced */
	uint32_t page_size_bytes;       /**< [OUT] page size in bytes */
	uint32_t reserved;              /**< Reserved for alignment */
};

/* IOCTL magic number */
#define GPU_P2P_NV_IOCTL_MAGIC  'N'

/* IOCTL commands */
#define GPU_P2P_NV_GET_PAGES  _IOWR(GPU_P2P_NV_IOCTL_MAGIC, 0xE0, struct nv_get_pages_req)
#define GPU_P2P_NV_PUT_PAGES  _IOW(GPU_P2P_NV_IOCTL_MAGIC, 0xE1, struct nv_put_pages_req)
#define GPU_P2P_NV_DMA_MAP    _IOWR(GPU_P2P_NV_IOCTL_MAGIC, 0xE2, struct nv_dma_map_req)

#endif /* NVIDIA_IOCTL_H */
