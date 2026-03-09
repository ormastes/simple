/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Opaque types for GPU P2P backend interface
 * This allows GPL modules to use P2P without including nvidia headers
 */
#pragma once

#include <linux/types.h>

struct pci_dev;

/*
 * Opaque handles for NVIDIA P2P structures
 * These hide nvidia_p2p_page_table and nvidia_p2p_dma_mapping
 * from GPL-licensed code
 */
struct gpu_p2p_page_table;
struct gpu_p2p_dma_mapping;

/* Page size types (mirrors nvidia_p2p_page_size_type) */
enum gpu_p2p_page_size {
	GPU_P2P_PAGE_SIZE_4KB = 0,
	GPU_P2P_PAGE_SIZE_64KB = 1,
	GPU_P2P_PAGE_SIZE_128KB = 2,
};

/*
 * Backend operations interface
 * All operations use opaque types to avoid GPL contamination
 */
struct gpu_p2p_backend_ops {
	int (*get_pages)(void *priv, __u64 p2p_token, __u32 va_space,
			 __u64 gpu_va, __u64 length,
			 struct gpu_p2p_page_table **page_table,
			 void (*free_callback)(void *), void *data);

	int (*dma_map_pages)(void *priv, struct pci_dev *pdev,
			     struct gpu_p2p_page_table *page_table,
			     struct gpu_p2p_dma_mapping **dma_mapping);

	void (*dma_unmap_pages)(void *priv, struct pci_dev *pdev,
				struct gpu_p2p_page_table *page_table,
				struct gpu_p2p_dma_mapping *dma_mapping);

	void (*free_dma_mapping)(void *priv,
				 struct gpu_p2p_dma_mapping *dma_mapping);

	void (*put_pages)(void *priv, __u64 p2p_token, __u32 va_space,
			  __u64 gpu_va, struct gpu_p2p_page_table *page_table);

	void (*free_page_table)(void *priv,
				struct gpu_p2p_page_table *page_table);

	/* Query page table properties */
	enum gpu_p2p_page_size (*get_page_size)(void *priv,
						struct gpu_p2p_dma_mapping *dma_mapping);

	__u32 (*get_num_entries)(void *priv,
				 struct gpu_p2p_dma_mapping *dma_mapping);

	__u64 (*get_dma_address)(void *priv,
				 struct gpu_p2p_dma_mapping *dma_mapping,
				 __u32 index);
};

/*
 * Backend registration (GPL-exported)
 * Proprietary backend modules call these to register their operations
 */
int gpu_p2p_register_backend(const struct gpu_p2p_backend_ops *ops,
			     void *priv);
void gpu_p2p_unregister_backend(const struct gpu_p2p_backend_ops *ops,
				void *priv);

/*
 * Backend query API (GPL-exported)
 * GPL modules use these to check if backend is available
 */
const struct gpu_p2p_backend_ops *gpu_p2p_get_backend(void **priv);
void gpu_p2p_put_backend(void);
