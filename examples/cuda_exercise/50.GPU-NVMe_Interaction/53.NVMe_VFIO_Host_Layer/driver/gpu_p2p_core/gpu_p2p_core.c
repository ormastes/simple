// SPDX-License-Identifier: GPL-2.0
/**
 * @file gpu_p2p_core.c
 * @brief GPL core driver for GPU P2P DMA mapping and doorbell operations
 *
 * This driver handles all GPL-only kernel interactions:
 * - Character device registration
 * - PCI DMA mapping for NVMe devices
 * - IOVA address management
 * - Doorbell MMIO mapping
 *
 * It works in conjunction with the proprietary NVIDIA bridge driver and
 * userspace wrapper library to provide GPU P2P functionality.
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/cdev.h>
#include <linux/device.h>
#include <linux/pci.h>
#include <linux/mm.h>
#include <linux/io.h>
#include <linux/uaccess.h>
#include <linux/slab.h>

#include "core_ioctl.h"

#define DRIVER_NAME "gpu_p2p_core"
#define DEVICE_NAME "gpu_p2p_core"

/* Device state */
static dev_t dev_num;
static struct cdev cdev;
static struct class *dev_class;
static struct device *device;

/**
 * @brief DMA mapping state for cleanup
 */
struct dma_mapping_state {
	struct pci_dev *pdev;
	dma_addr_t *iovas;
	uint32_t num_pages;
	uint64_t handle;  /* Unique handle for this mapping */
	struct list_head list;
};

static DEFINE_MUTEX(mappings_mutex);
static LIST_HEAD(mappings_list);
static atomic64_t next_handle = ATOMIC64_INIT(1);

/**
 * @brief Map physical pages to NVMe device DMA
 *
 * Takes physical addresses from NVIDIA driver and creates DMA mappings
 * for the specified NVMe device.
 */
static int core_dma_map_pages(struct core_dma_req *req)
{
	struct pci_dev *nvme_dev = NULL;
	struct core_page_info *pages = NULL;
	struct core_iova_seg *segs = NULL;
	dma_addr_t *iovas = NULL;
	struct dma_mapping_state *state = NULL;
	unsigned int domain, bus, dev, fn;
	uint32_t i, seg_idx = 0;
	uint64_t current_iova, current_len;
	int ret = 0;

	pr_info(DRIVER_NAME ": DMA map request: nvme_bdf=0x%llx, num_pages=%u\n",
		req->nvme_pci_bdf, req->num_pages);

	/* Parse BDF */
	domain = (req->nvme_pci_bdf >> 32) & 0xFFFF;
	bus = (req->nvme_pci_bdf >> 16) & 0xFF;
	dev = (req->nvme_pci_bdf >> 8) & 0x1F;
	fn = req->nvme_pci_bdf & 0x7;

	/* Get NVMe PCI device */
	nvme_dev = pci_get_domain_bus_and_slot(domain, bus, PCI_DEVFN(dev, fn));
	if (!nvme_dev) {
		pr_err(DRIVER_NAME ": NVMe device %04x:%02x:%02x.%x not found\n",
		       domain, bus, dev, fn);
		return -ENODEV;
	}

	/* Allocate temporary buffer for pages */
	pages = kmalloc_array(req->num_pages, sizeof(*pages), GFP_KERNEL);
	if (!pages) {
		ret = -ENOMEM;
		goto out_put_dev;
	}

	/* Copy page info from userspace */
	if (copy_from_user(pages, (void __user *)req->pages_user_ptr,
			   req->num_pages * sizeof(*pages))) {
		ret = -EFAULT;
		goto out_free_pages;
	}

	/* Allocate IOVA array */
	iovas = kmalloc_array(req->num_pages, sizeof(*iovas), GFP_KERNEL);
	if (!iovas) {
		ret = -ENOMEM;
		goto out_free_pages;
	}

	/* Map each page to NVMe device */
	for (i = 0; i < req->num_pages; i++) {
		struct page *page = pfn_to_page(pages[i].phys_addr >> PAGE_SHIFT);

		iovas[i] = dma_map_page(&nvme_dev->dev, page, 0,
					pages[i].page_size, DMA_BIDIRECTIONAL);

		if (dma_mapping_error(&nvme_dev->dev, iovas[i])) {
			pr_err(DRIVER_NAME ": DMA mapping failed for page %u\n", i);
			/* Unmap previously mapped pages */
			while (i > 0) {
				i--;
				dma_unmap_page(&nvme_dev->dev, iovas[i],
					       pages[i].page_size, DMA_BIDIRECTIONAL);
			}
			ret = -EIO;
			goto out_free_iovas;
		}
	}

	/* Coalesce IOVAs into contiguous segments */
	segs = kmalloc_array(req->max_segments, sizeof(*segs), GFP_KERNEL);
	if (!segs) {
		ret = -ENOMEM;
		goto out_unmap_all;
	}

	current_iova = iovas[0];
	current_len = pages[0].page_size;

	for (i = 1; i < req->num_pages; i++) {
		if (iovas[i] == current_iova + current_len) {
			/* Contiguous - extend current segment */
			current_len += pages[i].page_size;
		} else {
			/* Non-contiguous - start new segment */
			if (seg_idx >= req->max_segments) {
				pr_err(DRIVER_NAME ": Too many segments (max %u)\n",
				       req->max_segments);
				ret = -E2BIG;
				goto out_free_segs;
			}
			segs[seg_idx].dma_iova = current_iova;
			segs[seg_idx].len = current_len;
			seg_idx++;

			current_iova = iovas[i];
			current_len = pages[i].page_size;
		}
	}

	/* Add last segment */
	if (seg_idx >= req->max_segments) {
		pr_err(DRIVER_NAME ": Too many segments (max %u)\n",
		       req->max_segments);
		ret = -E2BIG;
		goto out_free_segs;
	}
	segs[seg_idx].dma_iova = current_iova;
	segs[seg_idx].len = current_len;
	seg_idx++;

	/* Copy segments to userspace */
	if (copy_to_user((void __user *)req->out_iova_segments_ptr,
			 segs, seg_idx * sizeof(*segs))) {
		ret = -EFAULT;
		goto out_free_segs;
	}

	/* Create mapping state for cleanup */
	state = kzalloc(sizeof(*state), GFP_KERNEL);
	if (!state) {
		ret = -ENOMEM;
		goto out_free_segs;
	}

	state->pdev = pci_dev_get(nvme_dev);  /* Take reference */
	state->iovas = iovas;
	state->num_pages = req->num_pages;
	state->handle = atomic64_inc_return(&next_handle);

	mutex_lock(&mappings_mutex);
	list_add(&state->list, &mappings_list);
	mutex_unlock(&mappings_mutex);

	/* Return results */
	req->num_segments = seg_idx;

	pr_info(DRIVER_NAME ": DMA map success: %u pages → %u segments, handle=0x%llx\n",
		req->num_pages, seg_idx, state->handle);

	kfree(segs);
	kfree(pages);
	pci_dev_put(nvme_dev);
	return 0;

out_free_segs:
	kfree(segs);
out_unmap_all:
	for (i = 0; i < req->num_pages; i++) {
		dma_unmap_page(&nvme_dev->dev, iovas[i],
			       pages[i].page_size, DMA_BIDIRECTIONAL);
	}
out_free_iovas:
	kfree(iovas);
out_free_pages:
	kfree(pages);
out_put_dev:
	pci_dev_put(nvme_dev);
	return ret;
}

/**
 * @brief Unmap DMA mapping
 */
static int core_dma_unmap_pages(struct core_dma_unmap_req *req)
{
	struct dma_mapping_state *state, *tmp;
	int ret = -EINVAL;

	mutex_lock(&mappings_mutex);
	list_for_each_entry_safe(state, tmp, &mappings_list, list) {
		if (state->handle == req->mapping_handle) {
			uint32_t i;

			/* Unmap all pages */
			for (i = 0; i < state->num_pages; i++) {
				dma_unmap_page(&state->pdev->dev, state->iovas[i],
					       PAGE_SIZE, DMA_BIDIRECTIONAL);
			}

			list_del(&state->list);
			pci_dev_put(state->pdev);
			kfree(state->iovas);
			kfree(state);

			pr_info(DRIVER_NAME ": DMA unmap success: handle=0x%llx\n",
				req->mapping_handle);
			ret = 0;
			break;
		}
	}
	mutex_unlock(&mappings_mutex);

	if (ret != 0)
		pr_err(DRIVER_NAME ": DMA unmap failed: handle=0x%llx not found\n",
		       req->mapping_handle);

	return ret;
}

/**
 * @note GPU-to-MMIO doorbell mapping has been REMOVED
 *
 * Previous implementation calculated NVMe doorbell physical addresses,
 * but GPU kernels CANNOT write to PCIe MMIO regions.
 *
 * This is a fundamental limitation: GPUs cannot access device BAR registers
 * directly via PCIe peer-to-peer writes.
 *
 * Working alternatives:
 * - Hardware DBC: NVMe controller polls shadow buffer in host memory
 * - Software daemon: CPU polls shadow buffer, writes MMIO on GPU's behalf
 *
 * See: 51.2.NVMe_Fundamentals/README.md for detailed explanation
 */

/**
 * @brief Map NVMe queues for GPU access
 *
 * For GPU-initiated I/O, the GPU kernel needs to access NVMe submission/completion
 * queues. Since these queues are already in host memory (allocated by VFIO),
 * we simply return their addresses - the GPU can access host memory directly
 * when it's page-locked (which VFIO memory is).
 *
 * Note: This is a "pass-through" implementation. The actual GPU accessibility
 * depends on the memory being pinned/page-locked by VFIO.
 */
static int core_map_nvme_queues(struct core_nvme_queue_req *req)
{
	pr_info(DRIVER_NAME ": Map NVMe queues: bdf=0x%llx, sq_va=0x%llx, cq_va=0x%llx\n",
		req->nvme_pci_bdf, req->sq_host_va, req->cq_host_va);

	/* For VFIO-bound NVMe devices, the queue memory is already page-locked
	 * and accessible from both CPU and GPU (via unified memory or page-locked access).
	 * We simply pass through the host addresses - the GPU can access them directly.
	 */
	req->out.sq_gpu_va = req->sq_host_va;
	req->out.cq_gpu_va = req->cq_host_va;
	req->out.sq_depth = req->sq_depth;
	req->out.cq_depth = req->cq_depth;
	req->out.qid = req->qid;
	req->out.sq_phase = 0;
	req->out.cq_phase = 1;  /* CQ phase starts at 1 */
	req->out.sq_tail = 0;
	req->out.cq_head = 0;

	pr_info(DRIVER_NAME ": Queue mapping success: sq_gpu=0x%llx, cq_gpu=0x%llx\n",
		req->out.sq_gpu_va, req->out.cq_gpu_va);

	return 0;
}

/**
 * @brief IOCTL handler
 */
static long core_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
	int ret = 0;

	switch (cmd) {
	case GPU_P2P_CORE_DMA_MAP: {
		struct core_dma_req req;
		if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
			return -EFAULT;
		ret = core_dma_map_pages(&req);
		if (ret == 0 && copy_to_user((void __user *)arg, &req, sizeof(req)))
			return -EFAULT;
		break;
	}

	case GPU_P2P_CORE_DMA_UNMAP: {
		struct core_dma_unmap_req req;
		if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
			return -EFAULT;
		ret = core_dma_unmap_pages(&req);
		break;
	}

	case GPU_P2P_CORE_MAP_NVME_QUEUES: {
		struct core_nvme_queue_req req;
		if (copy_from_user(&req, (void __user *)arg, sizeof(req)))
			return -EFAULT;
		ret = core_map_nvme_queues(&req);
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

static const struct file_operations core_fops = {
	.owner = THIS_MODULE,
	.unlocked_ioctl = core_ioctl,
};

/**
 * @brief Module initialization
 */
static int __init gpu_p2p_core_init(void)
{
	int ret;

	pr_info(DRIVER_NAME ": Initializing GPL core driver\n");

	/* Allocate character device number */
	ret = alloc_chrdev_region(&dev_num, 0, 1, DRIVER_NAME);
	if (ret < 0) {
		pr_err(DRIVER_NAME ": Failed to allocate device number\n");
		return ret;
	}

	/* Initialize character device */
	cdev_init(&cdev, &core_fops);
	cdev.owner = THIS_MODULE;

	ret = cdev_add(&cdev, dev_num, 1);
	if (ret < 0) {
		pr_err(DRIVER_NAME ": Failed to add character device\n");
		goto err_unregister_chrdev;
	}

	/* Create device class */
	dev_class = class_create(DRIVER_NAME);
	if (IS_ERR(dev_class)) {
		pr_err(DRIVER_NAME ": Failed to create device class\n");
		ret = PTR_ERR(dev_class);
		goto err_cdev_del;
	}

	/* Create device node */
	device = device_create(dev_class, NULL, dev_num, NULL, DEVICE_NAME);
	if (IS_ERR(device)) {
		pr_err(DRIVER_NAME ": Failed to create device\n");
		ret = PTR_ERR(device);
		goto err_class_destroy;
	}

	pr_info(DRIVER_NAME ": Initialized successfully, device /dev/%s\n", DEVICE_NAME);
	return 0;

err_class_destroy:
	class_destroy(dev_class);
err_cdev_del:
	cdev_del(&cdev);
err_unregister_chrdev:
	unregister_chrdev_region(dev_num, 1);
	return ret;
}

/**
 * @brief Module cleanup
 */
static void __exit gpu_p2p_core_exit(void)
{
	struct dma_mapping_state *state, *tmp;

	pr_info(DRIVER_NAME ": Cleaning up\n");

	/* Clean up any remaining mappings */
	mutex_lock(&mappings_mutex);
	list_for_each_entry_safe(state, tmp, &mappings_list, list) {
		uint32_t i;

		pr_warn(DRIVER_NAME ": Cleaning up leaked mapping handle=0x%llx\n",
			state->handle);

		for (i = 0; i < state->num_pages; i++) {
			dma_unmap_page(&state->pdev->dev, state->iovas[i],
				       PAGE_SIZE, DMA_BIDIRECTIONAL);
		}

		list_del(&state->list);
		pci_dev_put(state->pdev);
		kfree(state->iovas);
		kfree(state);
	}
	mutex_unlock(&mappings_mutex);

	device_destroy(dev_class, dev_num);
	class_destroy(dev_class);
	cdev_del(&cdev);
	unregister_chrdev_region(dev_num, 1);

	pr_info(DRIVER_NAME ": Cleanup complete\n");
}

module_init(gpu_p2p_core_init);
module_exit(gpu_p2p_core_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("CUDA Exercise Project");
MODULE_DESCRIPTION("GPU P2P Core - GPL driver for DMA/MMIO operations");
MODULE_VERSION("1.0");
