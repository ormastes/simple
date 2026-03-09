// SPDX-License-Identifier: GPL-2.0 OR MIT
/**
 * @file gpu_p2p_wrapper.h
 * @brief Public API for GPU P2P wrapper library
 *
 * This library provides a unified interface that matches the original
 * gpu_p2p driver API, but internally uses the dual-driver architecture
 * (GPL core + NVIDIA bridge) to avoid licensing conflicts.
 */

#ifndef GPU_P2P_WRAPPER_H
#define GPU_P2P_WRAPPER_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief GPU P2P IOVA segment (output)
 *
 * Same structure as the original driver's gpu_p2p_seg.
 */
struct gpu_p2p_seg {
	uint64_t dma_iova;  /**< DMA IOVA address for NVMe */
	uint64_t len;       /**< Length of contiguous segment */
};

/**
 * @brief GPU P2P mapping request
 *
 * Same structure as the original driver's gpu_p2p_req.
 * Application code using this should not need any changes.
 */
struct gpu_p2p_req {
	uint64_t gpu_va;        /**< GPU virtual address */
	uint64_t bytes;         /**< Size in bytes */
	uint64_t nvme_pci_bdf;  /**< NVMe device BDF (domain:bus:dev.fn) */
	uint64_t out_user_ptr;  /**< Pointer to output gpu_p2p_seg array */
	uint32_t max_segs;      /**< Max segments in output array */
	uint32_t num_segs;      /**< [OUT] Actual number of segments */
	uint64_t p2p_token;     /**< CUDA P2P token */
	uint32_t va_space;      /**< CUDA VA space ID */
	uint32_t flags;         /**< Reserved flags */
};

/**
 * @brief Map GPU buffer for NVMe DMA
 *
 * This function replaces the original GPU_P2P_MAP ioctl.
 * Internally, it:
 * 1. Calls NVIDIA bridge driver to get GPU pages
 * 2. Calls GPL core driver to map pages to NVMe DMA
 * 3. Returns IOVA segments to the application
 *
 * @param fd Dummy parameter (ignored, for API compatibility)
 * @param req Pointer to mapping request structure
 * @return 0 on success, negative error code on failure
 */
int gpu_p2p_map_buffer(int fd, struct gpu_p2p_req *req);

/**
 * @brief Unmap GPU buffer
 *
 * This function replaces the original GPU_P2P_UNMAP ioctl.
 *
 * @param fd Dummy parameter (ignored, for API compatibility)
 * @param gpu_va GPU virtual address to unmap
 * @return 0 on success, negative error code on failure
 */
int gpu_p2p_unmap_buffer(int fd, uint64_t gpu_va);

/**
 * @note GPU-to-NVMe MMIO doorbell mapping is NOT SUPPORTED
 *
 * GPU kernels cannot write to PCIe MMIO regions (NVMe BAR0 doorbell registers).
 * This is a fundamental PCIe/GPU architecture limitation.
 *
 * Use shadow doorbell mechanisms instead:
 * - Hardware DBC (Mode 2/3): NVMe controller polls shadow buffer in host memory
 * - Software daemon (Mode 5): CPU daemon polls shadow buffer, writes MMIO
 *
 * The previous gpu_p2p_map_doorbell() function has been removed as it provided
 * misleading physical addresses that GPUs cannot actually access.
 */

/**
 * @brief Initialize wrapper library (optional)
 *
 * Explicitly opens driver file descriptors.
 * This is optional - the library will initialize automatically on first use.
 *
 * @return 0 on success, negative error code on failure
 */
int gpu_p2p_wrapper_init(void);

/**
 * @brief Cleanup wrapper library (optional)
 *
 * Closes driver file descriptors and cleans up resources.
 * This is optional - the library will cleanup automatically at process exit.
 */
void gpu_p2p_wrapper_cleanup(void);

#ifdef __cplusplus
}
#endif

#endif /* GPU_P2P_WRAPPER_H */
