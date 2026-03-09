// SPDX-License-Identifier: GPL-2.0 OR MIT
/**
 * @file gpu_p2p_wrapper.c
 * @brief Userspace wrapper library implementation
 *
 * This library bridges the GPL core driver and NVIDIA bridge driver
 * to provide a unified API that matches the original gpu_p2p driver.
 */

#include "gpu_p2p_wrapper.h"
#include "../gpu_p2p_core/core_ioctl.h"
#include "../gpu_p2p_nvidia/nvidia_ioctl.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <pthread.h>

#define MAX_PAGES 1024  /* Maximum pages per mapping */

/**
 * @brief Mapping tracking entry
 */
struct mapping_entry {
	uint64_t gpu_va;                /**< GPU virtual address */
	uint64_t p2p_token;             /**< CUDA P2P token */
	uint32_t va_space;              /**< CUDA VA space */
	uint64_t nv_handle;             /**< NVIDIA page table handle */
	uint64_t core_handle;           /**< Core DMA mapping handle */
	struct mapping_entry *next;
};

/**
 * @brief Global wrapper context
 */
static struct {
	int core_fd;                    /**< /dev/gpu_p2p_core fd */
	int nvidia_fd;                  /**< /dev/gpu_p2p_nvidia fd */
	struct mapping_entry *mappings; /**< Linked list of active mappings */
	pthread_mutex_t mutex;          /**< Protects mappings list */
	int initialized;                /**< Init flag */
} g_ctx = {
	.core_fd = -1,
	.nvidia_fd = -1,
	.mappings = NULL,
	.initialized = 0,
};

/**
 * @brief Initialize wrapper library
 */
int gpu_p2p_wrapper_init(void)
{
	if (g_ctx.initialized)
		return 0;

	/* Open GPL core driver */
	g_ctx.core_fd = open("/dev/gpu_p2p_core", O_RDWR);
	if (g_ctx.core_fd < 0) {
		fprintf(stderr, "gpu_p2p_wrapper: Failed to open /dev/gpu_p2p_core: %s\n",
			strerror(errno));
		return -errno;
	}

	/* Open NVIDIA bridge driver */
	g_ctx.nvidia_fd = open("/dev/gpu_p2p_nvidia", O_RDWR);
	if (g_ctx.nvidia_fd < 0) {
		fprintf(stderr, "gpu_p2p_wrapper: Failed to open /dev/gpu_p2p_nvidia: %s\n",
			strerror(errno));
		close(g_ctx.core_fd);
		g_ctx.core_fd = -1;
		return -errno;
	}

	/* Initialize mutex */
	if (pthread_mutex_init(&g_ctx.mutex, NULL) != 0) {
		fprintf(stderr, "gpu_p2p_wrapper: Failed to initialize mutex\n");
		close(g_ctx.nvidia_fd);
		close(g_ctx.core_fd);
		g_ctx.nvidia_fd = -1;
		g_ctx.core_fd = -1;
		return -ENOMEM;
	}

	g_ctx.initialized = 1;

	fprintf(stderr, "gpu_p2p_wrapper: Initialized (core_fd=%d, nvidia_fd=%d)\n",
		g_ctx.core_fd, g_ctx.nvidia_fd);

	return 0;
}

/**
 * @brief Cleanup wrapper library
 */
void gpu_p2p_wrapper_cleanup(void)
{
	struct mapping_entry *entry, *next;

	if (!g_ctx.initialized)
		return;

	/* Clean up any remaining mappings */
	pthread_mutex_lock(&g_ctx.mutex);
	entry = g_ctx.mappings;
	while (entry) {
		fprintf(stderr, "gpu_p2p_wrapper: Warning: Cleaning up leaked mapping gpu_va=0x%llx\n",
			(unsigned long long)entry->gpu_va);

		/* Unmap from core driver */
		if (entry->core_handle != 0) {
			struct core_dma_unmap_req unmap_req = {
				.mapping_handle = entry->core_handle,
			};
			ioctl(g_ctx.core_fd, GPU_P2P_CORE_DMA_UNMAP, &unmap_req);
		}

		/* Put pages from NVIDIA driver */
		if (entry->nv_handle != 0) {
			struct nv_put_pages_req put_req = {
				.page_table_handle = entry->nv_handle,
				.gpu_va = entry->gpu_va,
				.p2p_token = entry->p2p_token,
				.va_space = entry->va_space,
			};
			ioctl(g_ctx.nvidia_fd, GPU_P2P_NV_PUT_PAGES, &put_req);
		}

		next = entry->next;
		free(entry);
		entry = next;
	}
	g_ctx.mappings = NULL;
	pthread_mutex_unlock(&g_ctx.mutex);

	pthread_mutex_destroy(&g_ctx.mutex);

	if (g_ctx.nvidia_fd >= 0) {
		close(g_ctx.nvidia_fd);
		g_ctx.nvidia_fd = -1;
	}

	if (g_ctx.core_fd >= 0) {
		close(g_ctx.core_fd);
		g_ctx.core_fd = -1;
	}

	g_ctx.initialized = 0;

	fprintf(stderr, "gpu_p2p_wrapper: Cleanup complete\n");
}

/**
 * @brief Map GPU buffer for NVMe DMA (main function)
 */
int gpu_p2p_map_buffer(int fd, struct gpu_p2p_req *req)
{
	struct nv_get_pages_req nv_req = {0};
	struct nv_page_info *pages = NULL;
	struct core_page_info *core_pages = NULL;
	struct core_dma_req core_req = {0};
	struct mapping_entry *entry = NULL;
	int ret = 0;

	if (!req) {
		fprintf(stderr, "gpu_p2p_wrapper: Invalid request pointer\n");
		return -EINVAL;
	}

	/* Lazy initialization */
	if (!g_ctx.initialized) {
		ret = gpu_p2p_wrapper_init();
		if (ret < 0)
			return ret;
	}

	fprintf(stderr, "gpu_p2p_wrapper: Map buffer: gpu_va=0x%llx, bytes=%llu, nvme_bdf=0x%llx\n",
		(unsigned long long)req->gpu_va, (unsigned long long)req->bytes,
		(unsigned long long)req->nvme_pci_bdf);

	/* Allocate temporary buffers */
	pages = malloc(MAX_PAGES * sizeof(*pages));
	if (!pages) {
		fprintf(stderr, "gpu_p2p_wrapper: Failed to allocate pages buffer\n");
		return -ENOMEM;
	}

	core_pages = malloc(MAX_PAGES * sizeof(*core_pages));
	if (!core_pages) {
		fprintf(stderr, "gpu_p2p_wrapper: Failed to allocate core_pages buffer\n");
		free(pages);
		return -ENOMEM;
	}

	/* Step 1: Get GPU pages from NVIDIA bridge */
	nv_req.gpu_va = req->gpu_va;
	nv_req.bytes = req->bytes;
	nv_req.p2p_token = req->p2p_token;
	nv_req.va_space = req->va_space;
	nv_req.flags = req->flags;
	nv_req.pages_user_ptr = (uint64_t)pages;

	ret = ioctl(g_ctx.nvidia_fd, GPU_P2P_NV_GET_PAGES, &nv_req);
	if (ret < 0) {
		fprintf(stderr, "gpu_p2p_wrapper: NVIDIA get_pages failed: %s\n",
			strerror(errno));
		free(core_pages);
		free(pages);
		return -errno;
	}

	fprintf(stderr, "gpu_p2p_wrapper: NVIDIA returned %u pages, handle=0x%llx\n",
		nv_req.num_pages, (unsigned long long)nv_req.page_table_handle);

	/* Convert nv_page_info to core_page_info */
	for (uint32_t i = 0; i < nv_req.num_pages; i++) {
		core_pages[i].phys_addr = pages[i].phys_addr;
		core_pages[i].page_size = pages[i].page_size;
		core_pages[i].reserved = 0;
	}

	free(pages);  /* Don't need nv_page_info anymore */

	/* Step 2: Map to NVMe DMA via GPL core driver */
	core_req.nvme_pci_bdf = req->nvme_pci_bdf;
	core_req.num_pages = nv_req.num_pages;
	core_req.flags = req->flags;
	core_req.pages_user_ptr = (uint64_t)core_pages;
	core_req.out_iova_segments_ptr = req->out_user_ptr;
	core_req.max_segments = req->max_segs;

	ret = ioctl(g_ctx.core_fd, GPU_P2P_CORE_DMA_MAP, &core_req);
	if (ret < 0) {
		fprintf(stderr, "gpu_p2p_wrapper: Core DMA map failed: %s\n",
			strerror(errno));

		/* Cleanup: put NVIDIA pages */
		struct nv_put_pages_req put_req = {
			.page_table_handle = nv_req.page_table_handle,
			.gpu_va = req->gpu_va,
			.p2p_token = req->p2p_token,
			.va_space = req->va_space,
		};
		ioctl(g_ctx.nvidia_fd, GPU_P2P_NV_PUT_PAGES, &put_req);

		free(core_pages);
		return -errno;
	}

	free(core_pages);  /* Don't need core_page_info anymore */

	fprintf(stderr, "gpu_p2p_wrapper: Core DMA map success: %u segments\n",
		core_req.num_segments);

	/* Step 3: Track mapping for cleanup */
	entry = malloc(sizeof(*entry));
	if (!entry) {
		fprintf(stderr, "gpu_p2p_wrapper: Warning: Failed to allocate tracking entry\n");
		/* Continue anyway - mapping is successful, just can't track it */
	} else {
		entry->gpu_va = req->gpu_va;
		entry->p2p_token = req->p2p_token;
		entry->va_space = req->va_space;
		entry->nv_handle = nv_req.page_table_handle;
		entry->core_handle = 0;  /* Core driver doesn't return handle yet */

		pthread_mutex_lock(&g_ctx.mutex);
		entry->next = g_ctx.mappings;
		g_ctx.mappings = entry;
		pthread_mutex_unlock(&g_ctx.mutex);
	}

	/* Return results */
	req->num_segs = core_req.num_segments;

	fprintf(stderr, "gpu_p2p_wrapper: Map buffer success: %u segments\n",
		req->num_segs);

	return 0;
}

/**
 * @brief Unmap GPU buffer
 */
int gpu_p2p_unmap_buffer(int fd, uint64_t gpu_va)
{
	struct mapping_entry *entry, *prev = NULL;
	int ret = -EINVAL;

	if (!g_ctx.initialized) {
		fprintf(stderr, "gpu_p2p_wrapper: Not initialized\n");
		return -EINVAL;
	}

	fprintf(stderr, "gpu_p2p_wrapper: Unmap buffer: gpu_va=0x%llx\n",
		(unsigned long long)gpu_va);

	/* Find mapping entry */
	pthread_mutex_lock(&g_ctx.mutex);
	entry = g_ctx.mappings;
	while (entry) {
		if (entry->gpu_va == gpu_va) {
			/* Unmap from core driver */
			if (entry->core_handle != 0) {
				struct core_dma_unmap_req unmap_req = {
					.mapping_handle = entry->core_handle,
				};
				ret = ioctl(g_ctx.core_fd, GPU_P2P_CORE_DMA_UNMAP, &unmap_req);
				if (ret < 0) {
					fprintf(stderr, "gpu_p2p_wrapper: Core unmap failed: %s\n",
						strerror(errno));
				}
			}

			/* Put pages from NVIDIA driver */
			if (entry->nv_handle != 0) {
				struct nv_put_pages_req put_req = {
					.page_table_handle = entry->nv_handle,
					.gpu_va = entry->gpu_va,
					.p2p_token = entry->p2p_token,
					.va_space = entry->va_space,
				};
				ret = ioctl(g_ctx.nvidia_fd, GPU_P2P_NV_PUT_PAGES, &put_req);
				if (ret < 0) {
					fprintf(stderr, "gpu_p2p_wrapper: NVIDIA put_pages failed: %s\n",
						strerror(errno));
				}
			}

			/* Remove from list */
			if (prev)
				prev->next = entry->next;
			else
				g_ctx.mappings = entry->next;

			free(entry);
			ret = 0;
			break;
		}
		prev = entry;
		entry = entry->next;
	}
	pthread_mutex_unlock(&g_ctx.mutex);

	if (ret != 0) {
		fprintf(stderr, "gpu_p2p_wrapper: Mapping not found for gpu_va=0x%llx\n",
			(unsigned long long)gpu_va);
		return -EINVAL;
	}

	fprintf(stderr, "gpu_p2p_wrapper: Unmap buffer success\n");
	return 0;
}

/**
 * @brief Map NVMe doorbell registers
 */
int gpu_p2p_map_doorbell(int fd, struct gpu_p2p_doorbell_req *req)
{
	struct core_doorbell_req core_req;
	int ret;

	if (!req) {
		fprintf(stderr, "gpu_p2p_wrapper: Invalid request pointer\n");
		return -EINVAL;
	}

	/* Lazy initialization */
	if (!g_ctx.initialized) {
		ret = gpu_p2p_wrapper_init();
		if (ret < 0)
			return ret;
	}

	fprintf(stderr, "gpu_p2p_wrapper: Map doorbell: nvme_bdf=0x%x, gpu_bdf=0x%x, qid=%d\n",
		req->nvme_bdf, req->gpu_bdf, req->qid);

	/* Forward directly to GPL core driver */
	core_req.nvme_bdf = req->nvme_bdf;
	core_req.gpu_bdf = req->gpu_bdf;
	core_req.qid = req->qid;
	core_req.flags = req->flags;

	ret = ioctl(g_ctx.core_fd, GPU_P2P_CORE_MAP_DB, &core_req);
	if (ret < 0) {
		fprintf(stderr, "gpu_p2p_wrapper: Core map_doorbell failed: %s\n",
			strerror(errno));
		return -errno;
	}

	/* Return results */
	req->sq_doorbell_gpu = core_req.sq_doorbell_gpu;
	req->cq_doorbell_gpu = core_req.cq_doorbell_gpu;

	fprintf(stderr, "gpu_p2p_wrapper: Map doorbell success: SQ=0x%llx, CQ=0x%llx\n",
		(unsigned long long)req->sq_doorbell_gpu,
		(unsigned long long)req->cq_doorbell_gpu);

	return 0;
}

/**
 * @brief Automatic cleanup on process exit
 */
__attribute__((destructor))
static void auto_cleanup(void)
{
	gpu_p2p_wrapper_cleanup();
}
