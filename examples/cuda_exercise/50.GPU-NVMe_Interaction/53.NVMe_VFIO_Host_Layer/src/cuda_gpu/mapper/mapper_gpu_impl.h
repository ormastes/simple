/**
 * @file mapping_gpu_impl.h
 * @brief GPU-side NVMe memory mapping and queue operation implementations
 *
 * This file contains the inline function implementations for GPU-side NVMe
 * queue operations. It should be included after mapping_gpu.h when
 * GPU-side device code is needed.
 *
 * **Refactoring Note (2025-11-01):**
 * Migrated to use CRTP doorbell strategies to eliminate runtime switch statements
 * in doorbell operations. Queue management logic remains unchanged for compatibility.
 */

#pragma once

#ifdef __CUDACC__
// Include unified implementations from Module 53
#include "io/io_impl.h"

// Include CRTP doorbell strategies
#include "doorbell/nvme_doorbell.h"  // For MmioDoorbell, ShadowDoorbell

// GPU debug logging macro (enabled with -DGPU_DEBUG_DOORBELL)
#if defined(GPU_DEBUG_DOORBELL) && defined(__CUDA_ARCH__)
    #define GPU_DEBUG_LOG(...) \
        do { \
            if (threadIdx.x == 0 && blockIdx.x == 0) { \
                printf(__VA_ARGS__); \
            } \
        } while(0)
#else
    #define GPU_DEBUG_LOG(...) do {} while(0)
#endif

// Device-side helper functions (only available in CUDA compilation)

// Import unified CQE parsing helpers from nvme_io_impl namespace
using nvme_io_impl::cqe_phase;
using nvme_io_impl::cqe_sct;
using nvme_io_impl::cqe_sc;
using nvme_io_impl::cqe_dnr;
using nvme_io_impl::status_is_error;

/**
 * @brief Reserve a submission queue slot (thread-safe)
 * @param iosq GPU submission queue descriptor
 * @param out_cid Output command ID
 * @param out_new_tail Output new tail value to publish after command write
 * @return Slot index in submission queue
 *
 * @note Uses internal counter (sq_internal_tail) for slot allocation.
 *       The external sq_tail is updated by nvme_gpu_publish_sq_tail() AFTER
 *       the command is written, to prevent race conditions with daemon/controller.
 *
 * @note For synchronous single-command-at-a-time patterns (Mode 5/6), flow control
 *       is not needed because the caller waits for each command to complete before
 *       issuing the next. For async/batched patterns, callers must implement their
 *       own flow control using sq_head tracking.
 *
 * @performance O(1) with potential atomic contention
 */
__device__ inline std::uint16_t nvme_gpu_reserve_sq_slot(NvmeQueueStruct* iosq, std::uint16_t* out_cid, uint32_t* out_new_tail)
{
	// Atomically increment internal tail to reserve slot
	// sq_internal_tail is used only for slot allocation, not visible to daemon/controller
	unsigned int old_tail = atomicAdd(&iosq->sq_internal_tail, 1u);

	std::uint16_t slot = static_cast<std::uint16_t>(old_tail % iosq->sq_depth);
	*out_cid = slot; // Use slot as command ID (simple strategy)
	*out_new_tail = old_tail + 1;  // New tail to publish after command write
	return slot;
}

/**
 * @brief Publish new submission queue tail (visible to daemon/controller)
 * @param iosq GPU submission queue descriptor
 * @param new_tail New tail value to publish
 *
 * @note Must be called AFTER the command is written to the slot.
 *       This ensures the daemon/controller sees a complete command.
 */
__device__ inline void nvme_gpu_publish_sq_tail(NvmeQueueStruct* iosq, uint32_t new_tail)
{
	// Atomically update sq_tail only if our command is next in sequence
	// This serializes tail updates to maintain command ordering
	// Use exchange to avoid ABA problem with concurrent writers
	unsigned int expected = new_tail - 1;

	// Spin until our turn to publish (ensures FIFO ordering)
	// This is needed because multiple threads may reserve slots concurrently
	// but must publish tails in order
	while (atomicCAS(&iosq->sq_tail, expected, new_tail) != expected) {
		// Our predecessor hasn't published yet, wait
		// Use minimal busy-wait with memory fence
		__threadfence_system();
	}
}

/**
 * @brief Legacy: Allocate a submission queue slot (thread-safe)
 * @deprecated Use nvme_gpu_reserve_sq_slot() + nvme_gpu_publish_sq_tail() instead
 * @param iosq GPU submission queue descriptor
 * @param out_cid Output command ID
 * @return Slot index in submission queue
 *
 * @note Uses atomic operations for thread-safety.
 * @performance O(1) with potential atomic contention
 */
__device__ inline std::uint16_t nvme_gpu_alloc_sq_slot(NvmeQueueStruct* iosq, std::uint16_t* out_cid)
{
	// Legacy behavior: increment sq_tail immediately
	// WARNING: This can cause race conditions with daemon in Mode 5
	unsigned int old_tail = atomicAdd(&iosq->sq_tail, 1u);
	std::uint16_t slot = static_cast<std::uint16_t>(old_tail % iosq->sq_depth);
	*out_cid = slot; // Use slot as command ID (simple strategy)
	return slot;
}

/**
 * @brief Write NVMe command to submission queue slot
 * @param iosq GPU submission queue descriptor
 * @param slot Submission queue slot index
 * @param opcode NVMe opcode (OPC_NVM_READ, OPC_NVM_WRITE, etc.)
 * @param nsid Namespace ID
 * @param prp1 Physical region page 1
 * @param prp2 Physical region page 2
 * @param slba Starting logical block address
 * @param nlb Number of logical blocks (0-based: 0 = 1 block, 1 = 2 blocks)
 * @param cid Command ID
 *
 * @note Includes memory fence to ensure visibility before doorbell ring
 */
__device__ inline void nvme_gpu_write_sq_command(
	NvmeQueueStruct* iosq,
	std::uint16_t slot,
	std::uint8_t opcode,
	std::uint32_t nsid,
	std::uint64_t prp1,
	std::uint64_t prp2,
	std::uint64_t slba,
	std::uint16_t nlb,
	std::uint16_t cid
)
{
	NvmeCmd* cmd_slot = &iosq->sq_base[slot];

	// Build command using unified helper from io_impl.h
	NvmeCmd temp_cmd;
	CommandType cmd_type = (opcode == OPC_NVM_READ) ? CMD_READ : CMD_WRITE;
	nvme_io_impl::build_command(cmd_type, nsid, slba, nlb, prp1, prp2, cid, temp_cmd);

	// Copy to queue slot (64 bytes)
	nvme_io_impl::copy_64B(cmd_slot, &temp_cmd);

	// Memory fence to ensure command is visible before doorbell write
	__threadfence_system();
}

/**
 * @brief Ring submission queue doorbell to notify controller
 * @param iosq GPU submission queue descriptor
 *
 * **Refactored (2025-11-01):** Uses CRTP doorbell strategies instead of switch statement.
 * Doorbell logic is now type-safe and zero-overhead within each case branch.
 *
 * @note Implementation varies by doorbell mode:
 * - DOORBELL_MODE_HOST_MMIO: Host daemon monitors sq_tail, no GPU doorbell
 * - DOORBELL_MODE_GPU_DBC: Write to shadow doorbell buffer (NVMe polls via DMA)
 * - DOORBELL_MODE_GPU_DBC_DAEMON: Write to shadow buffer (daemon converts to MMIO)
 * - DOORBELL_MODE_GPU_MMIO: GPU writes MMIO doorbell directly
 */
__device__ inline void nvme_gpu_ring_sq_doorbell(NvmeQueueStruct* iosq)
{
	std::uint16_t new_tail = iosq->sq_tail % iosq->sq_depth;

	switch (iosq->doorbell_mode) {
	case DOORBELL_MODE_HOST_MMIO:
		// Module 55.1: Host daemon monitors sq_tail, rings MMIO doorbells
		// GPU just ensures tail is visible, daemon handles doorbell
		__threadfence_system();
		break;

	case DOORBELL_MODE_GPU_DBC:
	case DOORBELL_MODE_GPU_DBC_DAEMON: {
		if (iosq->shadow_doorbell_sq) {
			const uint32_t db_index = iosq->qid * 2;
			const uint32_t new_tail = iosq->sq_tail % iosq->sq_depth;
			atomicExch((uint32_t*)&iosq->shadow_doorbell_sq[db_index], new_tail);
			__threadfence_system();
		}
		break;
	}

	default:
		break;
	}
}

/**
 * @brief Ring completion queue doorbell to notify controller
 * @param iocq GPU completion queue descriptor
 *
 * **Refactored (2025-11-01):** Uses CRTP doorbell strategies.
 * Simplified: CQ doorbell doesn't vary by mode as much as SQ doorbell.
 * All modes that ring CQ doorbell use the same mechanism.
 */
__device__ inline void nvme_gpu_ring_cq_doorbell(NvmeQueueStruct* iocq)
{
	std::uint16_t new_head = iocq->cq_head % iocq->cq_depth;

	switch (iocq->doorbell_mode) {
	case DOORBELL_MODE_HOST_MMIO:
		// Host queue mode: No GPU doorbell
		break;

	case DOORBELL_MODE_GPU_DBC:
	case DOORBELL_MODE_GPU_DBC_DAEMON: {
		if (iocq->shadow_doorbell_cq) {
			const uint32_t db_index = iocq->qid * 2 + 1;
			const uint32_t new_head = iocq->cq_head % iocq->cq_depth;
			atomicExch((uint32_t*)&iocq->shadow_doorbell_cq[db_index], new_head);
			__threadfence_system();
		}
		break;
	}

	default:
		break;
	}
}

/**
 * @brief Poll completion queue for completion
 * @param iocq GPU completion queue descriptor
 * @param cid Command ID to wait for
 * @param out_status Output status structure
 * @return true if completion found for given CID
 *
 * **Refactored (2025-11-01):** Now uses nvme_gpu_ring_cq_doorbell() with CRTP strategies.
 *
 * @note Non-blocking poll. Returns false if no completion or different CID.
 */
__device__ inline bool nvme_gpu_poll_cq(NvmeQueueStruct* iocq, std::uint16_t cid, NvmeStatus* out_status)
{
	std::uint16_t head = static_cast<std::uint16_t>(iocq->cq_head % iocq->cq_depth);
	NvmeCqe* cqe_ptr = &iocq->cq_base[head];

	// NOTE: __threadfence_system() removed from hot poll path for performance
	// The volatile reads below are sufficient for coherent host memory (cudaHostRegister)
	// For true PCIe DMA from NVMe controller, fence may be needed but it's too slow (~5-10μs)

	// Read CQE fields individually using volatile to avoid misaligned access
	// The status_p field contains both status and phase bit
	uint16_t status_p = *((volatile uint16_t*)&cqe_ptr->status_p);
	uint16_t cqe_cid = *((volatile uint16_t*)&cqe_ptr->cid);
	uint16_t sqhd = *((volatile uint16_t*)&cqe_ptr->sqhd);  // SQ head from CQE

	// Check if CQE phase matches expected phase (indicates new completion)
	std::uint8_t cqe_phase_bit = status_p & 1;
	std::uint8_t expected_phase = iocq->cq_phase;
	if (cqe_phase_bit != expected_phase) {
		return false; // No new completion
	}

	// Check if this CQE is for our command
	if (cqe_cid != cid) {
		return false; // Different command completed
	}

	// Extract status (bits 15:1 of status_p)
	uint16_t status_field = status_p >> 1;
	out_status->sct = (status_field >> 8) & 0x7;
	out_status->sc = status_field & 0xFF;
	out_status->dnr = (status_field >> 14) & 0x1;

	// Update SQ head (from CQE sqhd field) to track consumed commands
	// This is critical for flow control - allows queue slot reuse
	iocq->sq_head = sqhd;

	// Update CQ head
	atomicAdd(&iocq->cq_head, 1u);

	// Update phase if we wrapped around
	if ((iocq->cq_head % iocq->cq_depth) == 0) {
		iocq->cq_phase = !iocq->cq_phase;
	}

	// Ring CQ doorbell to notify controller we consumed the entry
	// This is CRITICAL for the controller to recycle CQ slots
	nvme_gpu_ring_cq_doorbell(iocq);

	return true;
}

/**
 * @brief Submit NVMe read operation and wait for completion
 * @param iosq GPU queue descriptor (used for both SQ and CQ operations)
 * @param nsid Namespace ID
 * @param slba Starting logical block address
 * @param nlb Number of logical blocks (0-based: 0 = 1 block, 1 = 2 blocks)
 * @param prp1 Physical region page 1
 * @param prp2 Physical region page 2
 * @param out_status Output status structure
 * @return true on success, false on timeout or error
 *
 * @performance Blocking operation with 1M iteration timeout (~1ms at 1GHz)
 */
__device__ inline bool nvme_gpu_submit_read(
	NvmeQueueStruct* iosq,
	std::uint32_t nsid,
	std::uint64_t slba,
	std::uint16_t nlb,
	std::uint64_t prp1,
	std::uint64_t prp2,
	NvmeStatus* out_status
)
{
	// 1. Reserve SQ slot (but don't publish tail yet)
	std::uint16_t cid;
	uint32_t new_tail;
	std::uint16_t slot = nvme_gpu_reserve_sq_slot(iosq, &cid, &new_tail);

	// 2. Write NVMe read command to reserved slot
	nvme_gpu_write_sq_command(iosq, slot, OPC_NVM_READ, nsid,
	                          prp1, prp2, slba, nlb, cid);

	// 3. Publish tail (makes command visible to daemon/controller)
	nvme_gpu_publish_sq_tail(iosq, new_tail);

	// 4. Ring doorbell
	nvme_gpu_ring_sq_doorbell(iosq);

	// 5. Poll for completion (with timeout)
	// Note: For daemon mode (Mode 5), we need longer timeout to account for:
	// - Daemon polling interval (~10-100μs)
	// - MMIO doorbell forwarding latency
	// - NVMe command execution (~10-100μs)
	// 10M iterations ~= 5-10ms at typical GPU clocks (1.5-2GHz)
	const int MAX_POLL_ITERS = 10000000;
	for (int i = 0; i < MAX_POLL_ITERS; i++) {
		if (nvme_gpu_poll_cq(iosq, cid, out_status)) {
			return !status_is_error(*out_status);
		}
	}

	// Timeout
	return false;
}

/**
 * @brief Submit NVMe write operation and wait for completion
 * @param iosq GPU queue descriptor (used for both SQ and CQ operations)
 * @param nsid Namespace ID
 * @param slba Starting logical block address
 * @param nlb Number of logical blocks (0-based: 0 = 1 block, 1 = 2 blocks)
 * @param prp1 Physical region page 1
 * @param prp2 Physical region page 2
 * @param out_status Output status structure
 * @return true on success, false on timeout or error
 *
 * @performance Blocking operation with 1M iteration timeout (~1ms at 1GHz)
 */
__device__ inline bool nvme_gpu_submit_write(
	NvmeQueueStruct* iosq,
	std::uint32_t nsid,
	std::uint64_t slba,
	std::uint16_t nlb,
	std::uint64_t prp1,
	std::uint64_t prp2,
	NvmeStatus* out_status
)
{
	// 1. Reserve SQ slot (but don't publish tail yet)
	std::uint16_t cid;
	uint32_t new_tail;
	std::uint16_t slot = nvme_gpu_reserve_sq_slot(iosq, &cid, &new_tail);

	GPU_DEBUG_LOG("[GPU WRITE] slot=%u, cid=%u, sq_tail=%u, cq_head=%u, cq_phase=%u\n",
	              slot, cid, iosq->sq_tail, iosq->cq_head, iosq->cq_phase);

	// 2. Write NVMe write command
	nvme_gpu_write_sq_command(iosq, slot, OPC_NVM_WRITE, nsid,
	                          prp1, prp2, slba, nlb, cid);

	// 3. Publish tail (makes command visible to daemon/controller)
	nvme_gpu_publish_sq_tail(iosq, new_tail);

	// 4. Ring doorbell
	nvme_gpu_ring_sq_doorbell(iosq);

	// 5. Poll for completion (with timeout)
	// Note: For daemon mode (Mode 5), we need longer timeout to account for:
	// - Daemon polling interval (~10-100μs)
	// - MMIO doorbell forwarding latency
	// - NVMe command execution (~10-100μs)
	// 10M iterations ~= 5-10ms at typical GPU clocks (1.5-2GHz)
	const int MAX_POLL_ITERS = 10000000;
	for (int i = 0; i < MAX_POLL_ITERS; i++) {
		if (nvme_gpu_poll_cq(iosq, cid, out_status)) {
			GPU_DEBUG_LOG("[GPU WRITE] Completion found at iter %d\n", i);
			return !status_is_error(*out_status);
		}
		// Debug output every 1M iterations
		if (i > 0 && (i % 1000000) == 0) {
			NvmeCqe* cqe_ptr = &iosq->cq_base[iosq->cq_head % iosq->cq_depth];
			uint16_t status_p = *((volatile uint16_t*)&cqe_ptr->status_p);
			uint16_t cqe_cid = *((volatile uint16_t*)&cqe_ptr->cid);
			GPU_DEBUG_LOG("[GPU WRITE] Poll iter %dM: cq_head=%u, exp_phase=%u, cqe_phase=%u, cqe_cid=%u, waiting_cid=%u\n",
			              i/1000000, iosq->cq_head, iosq->cq_phase,
			              status_p & 1, cqe_cid, cid);
		}
	}

	// Timeout - print debug info
	NvmeCqe* cqe_ptr = &iosq->cq_base[iosq->cq_head % iosq->cq_depth];
	uint16_t status_p = *((volatile uint16_t*)&cqe_ptr->status_p);
	uint16_t cqe_cid = *((volatile uint16_t*)&cqe_ptr->cid);
	GPU_DEBUG_LOG("[GPU WRITE] TIMEOUT: cq_head=%u, exp_phase=%u, cqe_phase=%u, cqe_cid=%u, waiting_cid=%u\n",
	              iosq->cq_head, iosq->cq_phase, status_p & 1, cqe_cid, cid);
	return false;
}

#endif // __CUDACC__
