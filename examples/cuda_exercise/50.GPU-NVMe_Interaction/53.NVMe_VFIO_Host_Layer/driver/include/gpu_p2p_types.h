/* SPDX-License-Identifier: GPL-2.0 */
/*
 * GPU P2P Opaque Type Definitions
 * These types hide NVIDIA proprietary structures from GPL code
 */
#pragma once

#include <linux/types.h>

struct pci_dev;

/*
 * Opaque handles - no structure definition in GPL code
 * Backend module casts these to/from nvidia_p2p_* types
 */
struct gpu_p2p_page_table;
struct gpu_p2p_dma_mapping;

/*
 * Page size enumeration (mirrors NVIDIA types)
 */
enum gpu_p2p_page_size {
	GPU_P2P_PAGE_SIZE_4KB = 0,
	GPU_P2P_PAGE_SIZE_64KB = 1,
	GPU_P2P_PAGE_SIZE_128KB = 2,
};

/*
 * Backend operations - complete abstraction layer
 * All operations use opaque types and primitives only
 */
struct gpu_p2p_backend_ops {
	/* Memory mapping operations */
	int (*get_pages)(void *priv,
			 __u64 p2p_token,
			 __u32 va_space,
			 __u64 gpu_va,
			 __u64 length,
			 struct gpu_p2p_page_table **page_table,
			 void (*free_callback)(void *data),
			 void *callback_data);

	/* Persistent API - does not require p2p_token */
	int (*get_pages_persistent)(void *priv,
				    __u64 gpu_va,
				    __u64 length,
				    struct gpu_p2p_page_table **page_table,
				    __u32 flags);

	void (*put_pages_persistent)(void *priv,
				     __u64 gpu_va,
				     struct gpu_p2p_page_table *page_table,
				     __u32 flags);

	int (*dma_map_pages)(void *priv,
			     struct pci_dev *peer_dev,
			     struct gpu_p2p_page_table *page_table,
			     struct gpu_p2p_dma_mapping **dma_mapping);

	void (*dma_unmap_pages)(void *priv,
				struct pci_dev *peer_dev,
				struct gpu_p2p_page_table *page_table,
				struct gpu_p2p_dma_mapping *dma_mapping);

	void (*free_dma_mapping)(void *priv,
				 struct gpu_p2p_dma_mapping *dma_mapping);

	void (*put_pages)(void *priv,
			  __u64 p2p_token,
			  __u32 va_space,
			  __u64 gpu_va,
			  struct gpu_p2p_page_table *page_table);

	void (*free_page_table)(void *priv,
				struct gpu_p2p_page_table *page_table);

	/* Query operations - access DMA mapping properties */
	enum gpu_p2p_page_size (*get_page_size_type)(void *priv,
						     struct gpu_p2p_dma_mapping *dma_mapping);

	__u32 (*get_entries_count)(void *priv,
				   struct gpu_p2p_dma_mapping *dma_mapping);

	__u64 (*get_dma_address)(void *priv,
				 struct gpu_p2p_dma_mapping *dma_mapping,
				 __u32 index);

	/* Version compatibility checks */
	bool (*is_page_table_compatible)(void *priv,
					 struct gpu_p2p_page_table *page_table);

	bool (*is_dma_mapping_compatible)(void *priv,
					  struct gpu_p2p_dma_mapping *dma_mapping);
};

/*
 * Backend registration API
 * Exported by main GPL module, called by backend module
 */
int gpu_p2p_register_backend(const struct gpu_p2p_backend_ops *ops,
			     void *priv);
void gpu_p2p_unregister_backend(const struct gpu_p2p_backend_ops *ops,
				void *priv);

/*
 * Backend query API (internal to main module)
 */
const struct gpu_p2p_backend_ops *gpu_p2p_get_backend(void **priv_out);
void gpu_p2p_put_backend(void);

/*
 * Helper: Convert page size enum to bytes
 */
static inline __u64 gpu_p2p_page_size_bytes(enum gpu_p2p_page_size type)
{
	switch (type) {
	case GPU_P2P_PAGE_SIZE_4KB:
		return 4ULL << 10;
	case GPU_P2P_PAGE_SIZE_64KB:
		return 64ULL << 10;
	case GPU_P2P_PAGE_SIZE_128KB:
		return 128ULL << 10;
	default:
		return 0;
	}
}
