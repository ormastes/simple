/**
 * @file gpu_p2p_ioctl.h
 * @brief GPU P2P ioctl interface for NVMe kernel module
 *
 * Defines ioctl commands and data structures for GPU-NVMe P2P mapping:
 * - GPU_P2P_MAP: Map GPU memory to NVMe device
 * - GPU_P2P_MAP_NVME_QUEUES: Map NVMe queues to GPU
 * - GPU_P2P_MAP_NVME_DOORBELLS: Map NVMe doorbells to GPU
 *
 * Compatible with both kernel and userspace code.
 */

#pragma once

#ifdef __KERNEL__
#include <linux/types.h>
#include <linux/ioctl.h>
#else
#include "cuda_utils.h"
#include <sys/ioctl.h>
// Only define these types if not already defined by system headers
#if !defined(__u8) && !defined(_ASM_GENERIC_INT_LL64_H)
typedef uint8_t  __u8;
typedef uint16_t __u16;
typedef uint32_t __u32;
typedef uint64_t __u64;
#endif
#endif

#define GPU_P2P_MAP             _IOWR('G', 0xE0, struct gpu_p2p_req)
#define GPU_P2P_MAP_NVME_QUEUES _IOWR('G', 0xE1, struct gpu_p2p_nvme_queue_req)
#define GPU_P2P_MAP_NVME_DOORBELLS _IOWR('G', 0xE2, struct gpu_p2p_nvme_doorbell_req)
#define GPU_P2P_MAP_DOORBELL    _IOWR('G', 0xE3, struct gpu_p2p_doorbell_req)

#define GPU_P2P_MAX_SEGMENTS 4096U

struct gpu_p2p_seg {
	__u64 dma_iova;
	__u64 len;
};

struct gpu_p2p_req {
	__u64 gpu_va;
	__u64 bytes;
	__u64 nvme_pci_bdf;
	__u64 out_user_ptr;
	__u32 max_segs;
	__u32 num_segs;
	__u64 p2p_token;
	__u32 va_space;
	__u32 flags;
};

// GPU-side NVMe submission: Queue mapping structures
struct gpu_p2p_nvme_queue_info {
	__u64 sq_gpu_va;          // Output: GPU virtual address for SQ
	__u64 cq_gpu_va;          // Output: GPU virtual address for CQ
	__u16 sq_depth;           // Output: SQ depth (entries)
	__u16 cq_depth;           // Output: CQ depth (entries)
	__u16 qid;                // Output: Queue ID
	__u8  sq_phase;           // Output: Current SQ phase bit
	__u8  cq_phase;           // Output: Current CQ phase bit
	__u32 sq_tail;            // Output: Current SQ tail index (unsigned int for atomics)
	__u32 cq_head;            // Output: Current CQ head index (unsigned int for atomics)
};

struct gpu_p2p_nvme_queue_req {
	__u64 nvme_pci_bdf;       // Input: NVMe device (domain:bus:dev.fn)
	__u64 sq_host_va;         // Input: Host virtual address of SQ
	__u64 cq_host_va;         // Input: Host virtual address of CQ
	__u64 p2p_token;          // Input: GPU P2P token
	__u32 va_space;           // Input: GPU VA space
	__u16 qid;                // Input: Queue ID (1 for IO queue)
	__u16 sq_depth;           // Input: SQ depth
	__u16 cq_depth;           // Input: CQ depth
	__u16 reserved1;          // Padding
	__u32 flags;              // Input: Reserved (must be 0)
	__u32 reserved2;          // Padding for 8-byte alignment
	struct gpu_p2p_nvme_queue_info out; // Output: GPU-accessible metadata
};

// GPU-side NVMe submission: Doorbell mapping structures
struct gpu_p2p_doorbell_req {
	__u32 nvme_bdf;           // Input: NVMe device BDF (numeric)
	__u32 gpu_bdf;            // Input: GPU device BDF (numeric, optional)
	__u16 qid;                // Input: Queue ID
	__u16 reserved1;          // Padding
	__u32 flags;              // Input: Reserved (must be 0)
	__u64 sq_doorbell_gpu;    // Output: GPU address for SQ doorbell
	__u64 cq_doorbell_gpu;    // Output: GPU address for CQ doorbell
};

// Legacy structure for compatibility
struct gpu_p2p_nvme_doorbell_req {
	__u64 nvme_pci_bdf;       // Input: NVMe device BDF
	__u64 p2p_token;          // Input: GPU P2P token
	__u32 va_space;           // Input: GPU VA space
	__u32 flags;              // Input: Reserved (must be 0)
	__u64 db_gpu_va;          // Output: GPU virtual address for doorbell base
	__u32 db_stride;          // Output: Doorbell stride (bytes between SQ/CQ doorbells)
	__u32 reserved;           // Padding for alignment
};

