// SPDX-License-Identifier: GPL-2.0
/**
 * @file gpu_p2p_nvidia.c
 * @brief Proprietary NVIDIA bridge driver for GPU P2P operations
 *
 * This driver serves as a thin wrapper around NVIDIA's proprietary P2P API.
 * It uses ONLY non-GPL kernel symbols to avoid licensing conflicts:
 * - Uses __register_chrdev instead of alloc_chrdev_region+cdev
 * - Uses kmalloc instead of kzalloc
 * - Minimal kernel API surface
 *
 * This works in conjunction with the GPL core driver and userspace wrapper.
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/uaccess.h>
#include <linux/slab.h>
#include <linux/list.h>
#include <linux/mutex.h>
#include <linux/pci.h>

#include <nv-p2p.h>
#include "nvidia_ioctl.h"

#define DRIVER_NAME "gpu_p2p_nvidia"
#define DEVICE_NAME "gpu_p2p_nvidia"

static int nvidia_major = 0;  /* Dynamic major number */

/**
 * @brief Page table tracking structure
 *
 * Stores the nvidia_p2p_page_table pointer along with metadata
 * for cleanup.
 */
struct page_table_entry {
	uint64_t handle;                            /* Unique handle */
	uint64_t gpu_va;                           /* GPU virtual address */
	uint64_t p2p_token;                        /* CUDA P2P token */
	uint32_t va_space;                         /* CUDA VA space */
	struct nvidia_p2p_page_table *page_table;  /* NVIDIA page table */
	struct nvidia_p2p_dma_mapping *dma_mapping;/* IOMMU DMA mapping */
	struct pci_dev *peer_dev;                  /* Peer device owning the mapping */
	struct list_head list;
};

static struct mutex tables_mutex;
static struct list_head tables_list;
static atomic64_t next_handle_nv = ATOMIC64_INIT(0x1000);  /* Start at 0x1000 */

/**
 * @brief Get GPU pages via NVIDIA P2P API
 */
static int nv_get_pages_impl(struct nv_get_pages_req *req)
{
	struct nvidia_p2p_page_table *page_table = NULL;
	struct nv_page_info *pages = NULL;
	struct page_table_entry *entry = NULL;
	uint32_t i;
	int ret;

	pr_info(DRIVER_NAME ": Get pages: gpu_va=0x%llx, bytes=%llu, token=0x%llx\n",
		req->gpu_va, req->bytes, req->p2p_token);

	/* NVIDIA P2P API requires 64KB alignment for persistent API
	 * Align down the address and align up the length
	 */
	uint64_t aligned_va = req->gpu_va & ~(64ULL * 1024ULL - 1ULL);
	uint64_t aligned_len = req->bytes + (req->gpu_va - aligned_va);
	aligned_len = (aligned_len + (64ULL * 1024ULL - 1ULL)) & ~(64ULL * 1024ULL - 1ULL);

	pr_info(DRIVER_NAME ": Aligned: va=0x%llx->0x%llx, len=%llu->%llu\n",
		req->gpu_va, aligned_va, req->bytes, aligned_len);

	/* Call NVIDIA P2P API
	 * Use persistent API when token=0 (doesn't require p2p_token)
	 * Use regular API when token!=0 (IPC/RDMA scenarios)
	 */
	if (req->p2p_token == 0) {
		pr_info(DRIVER_NAME ": Using nvidia_p2p_get_pages_persistent (token=0)\n");
		ret = nvidia_p2p_get_pages_persistent(aligned_va, aligned_len,
						      &page_table, 0 /* flags */);
	} else {
		ret = nvidia_p2p_get_pages(req->p2p_token, req->va_space,
					   aligned_va, aligned_len,
					   &page_table, NULL, NULL);
	}

	if (ret != 0) {
		pr_err(DRIVER_NAME ": nvidia_p2p_get_pages%s failed: %d\n",
		       req->p2p_token == 0 ? "_persistent" : "", ret);
		return ret;
	}

	if (!page_table || !page_table->entries) {
		pr_err(DRIVER_NAME ": Invalid page table returned\n");
		return -EINVAL;
	}

	pr_info(DRIVER_NAME ": Got %u pages, page_size=%u\n",
		page_table->entries, page_table->page_size);

	/* Allocate temporary buffer for page info */
	pages = kmalloc(page_table->entries * sizeof(*pages), GFP_KERNEL);
	if (!pages) {
		nvidia_p2p_put_pages(req->p2p_token, req->va_space,
				     req->gpu_va, page_table);
		nvidia_p2p_free_page_table(page_table);
		return -ENOMEM;
	}

	/* Extract physical addresses */
	for (i = 0; i < page_table->entries; i++) {
		pages[i].phys_addr = page_table->pages[i]->physical_address;

		/* Convert page_size enum to bytes */
		switch (page_table->page_size) {
		case NVIDIA_P2P_PAGE_SIZE_4KB:
			pages[i].page_size = 4096;
			break;
		case NVIDIA_P2P_PAGE_SIZE_64KB:
			pages[i].page_size = 65536;
			break;
		case NVIDIA_P2P_PAGE_SIZE_128KB:
			pages[i].page_size = 131072;
			break;
		default:
			pages[i].page_size = 4096;
		}
		pages[i].reserved = 0;
	}

	/* Copy to userspace */
	if (copy_to_user((void __user *)req->pages_user_ptr,
			 pages, page_table->entries * sizeof(*pages))) {
		kfree(pages);
		nvidia_p2p_put_pages(req->p2p_token, req->va_space,
				     req->gpu_va, page_table);
		nvidia_p2p_free_page_table(page_table);
		return -EFAULT;
	}

	kfree(pages);

	/* Create tracking entry */
	entry = kmalloc(sizeof(*entry), GFP_KERNEL);
	if (!entry) {
		nvidia_p2p_put_pages(req->p2p_token, req->va_space,
				     req->gpu_va, page_table);
		nvidia_p2p_free_page_table(page_table);
		return -ENOMEM;
	}

	entry->handle = atomic64_inc_return(&next_handle_nv);
	entry->gpu_va = req->gpu_va;
	entry->p2p_token = req->p2p_token;
	entry->va_space = req->va_space;
	entry->page_table = page_table;

	mutex_lock(&tables_mutex);
	list_add(&entry->list, &tables_list);
	mutex_unlock(&tables_mutex);

	/* Return results */
	req->page_table_handle = entry->handle;
	req->num_pages = page_table->entries;
	req->page_size = page_table->page_size;

	pr_info(DRIVER_NAME ": Get pages success: handle=0x%llx, %u pages\n",
		entry->handle, page_table->entries);

	return 0;
}

/**
 * @brief Put GPU pages via NVIDIA P2P API
 */
static int nv_put_pages_impl(struct nv_put_pages_req *req)
{
	struct page_table_entry *entry, *tmp;
	int ret = -EINVAL;

	pr_info(DRIVER_NAME ": Put pages: handle=0x%llx\n", req->page_table_handle);

	mutex_lock(&tables_mutex);
	list_for_each_entry_safe(entry, tmp, &tables_list, list) {
		if (entry->handle == req->page_table_handle) {
			/* Validate parameters */
			if (entry->gpu_va != req->gpu_va ||
			    entry->p2p_token != req->p2p_token ||
			    entry->va_space != req->va_space) {
				pr_err(DRIVER_NAME ": Put pages validation failed\n");
				ret = -EINVAL;
				break;
			}

			/* Unmap DMA mapping if still active */
			if (entry->dma_mapping) {
				if (entry->peer_dev)
					nvidia_p2p_dma_unmap_pages(entry->peer_dev,
								   entry->page_table,
								   entry->dma_mapping);
				nvidia_p2p_free_dma_mapping(entry->dma_mapping);
				if (entry->peer_dev)
					pci_dev_put(entry->peer_dev);
				entry->dma_mapping = NULL;
				entry->peer_dev = NULL;
			}

			/* Call NVIDIA API to release pages
			 * Use persistent API when token=0
			 */
			if (entry->p2p_token == 0) {
				nvidia_p2p_put_pages_persistent(entry->gpu_va,
								entry->page_table,
								0 /* flags */);
			} else {
				nvidia_p2p_put_pages(entry->p2p_token, entry->va_space,
						     entry->gpu_va, entry->page_table);
			}
			nvidia_p2p_free_page_table(entry->page_table);

			list_del(&entry->list);
			kfree(entry);

			pr_info(DRIVER_NAME ": Put pages success: handle=0x%llx\n",
				req->page_table_handle);
			ret = 0;
			break;
		}
	}
	mutex_unlock(&tables_mutex);

	if (ret != 0)
		pr_err(DRIVER_NAME ": Put pages failed: handle=0x%llx not found\n",
		       req->page_table_handle);

	return ret;
}

static struct pci_dev *find_pci_dev_from_bdf(uint64_t bdf_numeric)
{
	uint16_t domain = (bdf_numeric >> 32) & 0xffff;
	uint8_t bus = (bdf_numeric >> 16) & 0xff;
	uint8_t dev = (bdf_numeric >> 8) & 0x1f;
	uint8_t func = bdf_numeric & 0x7;

	return pci_get_domain_bus_and_slot(domain, bus, PCI_DEVFN(dev, func));
}

static int nv_dma_map_impl(struct nv_dma_map_req *req)
{
	struct page_table_entry *entry;
	struct nvidia_p2p_dma_mapping *dma_mapping = NULL;
	struct pci_dev *pdev;
	uint32_t i;
	int ret = 0;

	mutex_lock(&tables_mutex);
	list_for_each_entry(entry, &tables_list, list) {
		if (entry->handle == req->page_table_handle)
			goto found_entry;
	}
	mutex_unlock(&tables_mutex);
	pr_err(DRIVER_NAME ": DMA map failed: handle=0x%llx not found\n",
	       req->page_table_handle);
	return -EINVAL;

found_entry:
	/* Prevent double-mapping without cleanup */
	if (entry->dma_mapping) {
		mutex_unlock(&tables_mutex);
		pr_err(DRIVER_NAME ": DMA map failed: handle=0x%llx already mapped\n",
		       req->page_table_handle);
		return -EBUSY;
	}
	mutex_unlock(&tables_mutex);

	pdev = find_pci_dev_from_bdf(req->nvme_pci_bdf);
	if (!pdev) {
		pr_err(DRIVER_NAME ": DMA map failed: could not resolve PCI device for BDF=0x%llx\n",
		       req->nvme_pci_bdf);
		return -ENODEV;
	}

	ret = nvidia_p2p_dma_map_pages(pdev, entry->page_table, &dma_mapping);
	if (ret != 0) {
		pr_err(DRIVER_NAME ": nvidia_p2p_dma_map_pages failed: %d\n", ret);
		pci_dev_put(pdev);
		return ret;
	}

	if (!dma_mapping || !dma_mapping->dma_addresses || dma_mapping->entries == 0) {
		pr_err(DRIVER_NAME ": Invalid DMA mapping returned\n");
		nvidia_p2p_dma_unmap_pages(pdev, entry->page_table, dma_mapping);
		nvidia_p2p_free_dma_mapping(dma_mapping);
		pci_dev_put(pdev);
		return -EINVAL;
	}

	/* Copy DMA addresses to userspace */
	req->num_entries = dma_mapping->entries;
	switch (dma_mapping->page_size_type) {
	case NVIDIA_P2P_PAGE_SIZE_64KB:
		req->page_size_bytes = 65536;
		break;
	case NVIDIA_P2P_PAGE_SIZE_128KB:
		req->page_size_bytes = 131072;
		break;
	default:
		req->page_size_bytes = 4096;
		break;
	}

	if (req->max_entries < dma_mapping->entries) {
		pr_warn(DRIVER_NAME ": DMA map: truncating address copy (%u of %u)\n",
			req->max_entries, dma_mapping->entries);
	}

	for (i = 0; i < dma_mapping->entries && i < req->max_entries; i++) {
		if (copy_to_user((void __user *)(req->dma_user_ptr + i * sizeof(uint64_t)),
				 &dma_mapping->dma_addresses[i],
				 sizeof(uint64_t))) {
			nvidia_p2p_dma_unmap_pages(pdev, entry->page_table, dma_mapping);
			nvidia_p2p_free_dma_mapping(dma_mapping);
			pci_dev_put(pdev);
			return -EFAULT;
		}
	}

	/* Hold mapping for later unmap when pages are released */
	mutex_lock(&tables_mutex);
	entry->dma_mapping = dma_mapping;
	entry->peer_dev = pdev;
	mutex_unlock(&tables_mutex);

	pr_info(DRIVER_NAME ": DMA map success: handle=0x%llx, entries=%u, page_size=%u\n",
		entry->handle, dma_mapping->entries, req->page_size_bytes);
	return 0;
}

/**
 * @brief IOCTL handler
 */
static long nvidia_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
	int ret = 0;

	switch (cmd) {
	case GPU_P2P_NV_GET_PAGES: {
		struct nv_get_pages_req req;
		if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
			return -EFAULT;
		ret = nv_get_pages_impl(&req);
		if (ret == 0 && copy_to_user((void __user *)arg, &req, sizeof(req)))
			return -EFAULT;
		break;
	}

	case GPU_P2P_NV_PUT_PAGES: {
		struct nv_put_pages_req req;
		if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
			return -EFAULT;
		ret = nv_put_pages_impl(&req);
		break;
	}

	case GPU_P2P_NV_DMA_MAP: {
		struct nv_dma_map_req req;
		if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
			return -EFAULT;
		ret = nv_dma_map_impl(&req);
		if (ret == 0 && copy_to_user((void __user *)arg, &req, sizeof(req)))
			return -EFAULT;
		break;
	}

	default:
		pr_err(DRIVER_NAME ": Unknown ioctl cmd=0x%x\n", cmd);
		ret = -EINVAL;
	}

	return ret;
}

static int nvidia_open(struct inode *inode, struct file *filp)
{
	return 0;
}

static int nvidia_release(struct inode *inode, struct file *filp)
{
	return 0;
}

static const struct file_operations nvidia_fops = {
	.owner = THIS_MODULE,
	.open = nvidia_open,
	.release = nvidia_release,
	.unlocked_ioctl = nvidia_ioctl,
};

/**
 * @brief Module initialization
 *
 * Uses __register_chrdev (non-GPL) instead of alloc_chrdev_region+cdev
 * to avoid GPL-only symbols.
 */
static int __init gpu_p2p_nvidia_init(void)
{
	int ret;

	pr_info(DRIVER_NAME ": Initializing NVIDIA bridge driver\n");

	/* Initialize list and mutex */
	INIT_LIST_HEAD(&tables_list);
	mutex_init(&tables_mutex);

	/* Register character device with dynamic major number */
	/* register_chrdev returns the allocated major number if successful */
	ret = register_chrdev(0, DEVICE_NAME, &nvidia_fops);
	if (ret < 0) {
		pr_err(DRIVER_NAME ": Failed to register character device: %d\n", ret);
		return ret;
	}
	nvidia_major = ret;

	pr_info(DRIVER_NAME ": Initialized successfully, major=%d\n", nvidia_major);
	pr_info(DRIVER_NAME ": Create device node with: mknod /dev/%s c %d 0\n",
		DEVICE_NAME, nvidia_major);

	return 0;
}

/**
 * @brief Module cleanup
 */
static void __exit gpu_p2p_nvidia_exit(void)
{
	struct page_table_entry *entry, *tmp;

	pr_info(DRIVER_NAME ": Cleaning up\n");

	/* Clean up any remaining page tables */
	mutex_lock(&tables_mutex);
	list_for_each_entry_safe(entry, tmp, &tables_list, list) {
		pr_warn(DRIVER_NAME ": Cleaning up leaked page table handle=0x%llx\n",
			entry->handle);

		nvidia_p2p_put_pages(entry->p2p_token, entry->va_space,
				     entry->gpu_va, entry->page_table);
		nvidia_p2p_free_page_table(entry->page_table);

		list_del(&entry->list);
		kfree(entry);
	}
	mutex_unlock(&tables_mutex);

	if (nvidia_major > 0)
		unregister_chrdev(nvidia_major, DEVICE_NAME);

	pr_info(DRIVER_NAME ": Cleanup complete\n");
}

module_init(gpu_p2p_nvidia_init);
module_exit(gpu_p2p_nvidia_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("CUDA Exercise Project");
MODULE_DESCRIPTION("NVIDIA GPUDirect Bridge - Proprietary P2P wrapper");
MODULE_VERSION("1.0");
MODULE_SOFTDEP("pre: nvidia");
