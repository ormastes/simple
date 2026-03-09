/**
 * @file io_impl.h
 * @brief Shared I/O operation implementations
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cstring>  // For memcpy in host code
#include "nvme_types.h"  // For NvmeCmd, NvmeCqe, NvmeStatus, etc.
#include "cuda_utils.h"  // For CUDA compatibility macros

namespace nvme_io_impl {

// ============================================================================
// Command Building
// ============================================================================

/**
 * @brief Build NVMe command structure
 * @param cmd_type Command type (CMD_READ or CMD_WRITE)
 * @param nsid Namespace ID
 * @param slba Starting LBA
 * @param nlb Number of blocks (0-based)
 * @param prp1 PRP1
 * @param prp2 PRP2
 * @param cid Command ID
 * @param cmd Output command
 */
__device__ __host__ inline void build_command(CommandType cmd_type,
                                               uint32_t nsid,
                                               uint64_t slba,
                                               uint16_t nlb,
                                               uint64_t prp1,
                                               uint64_t prp2,
                                               uint16_t cid,
                                               NvmeCmd& cmd)
{
  cmd = {};
  cmd.opc = (cmd_type == CMD_READ) ? OPC_NVM_READ : OPC_NVM_WRITE;
  cmd.cid = cid;
  cmd.nsid = nsid;
  cmd.prp1 = prp1;
  cmd.prp2 = prp2;
  cmd.cdw10 = (uint32_t)(slba & 0xFFFFFFFFu);
  cmd.cdw11 = (uint32_t)(slba >> 32);
  cmd.cdw12 = (uint32_t)nlb;
}

/**
 * @brief Copy 64 bytes efficiently
 * @param dst Destination pointer
 * @param src Source pointer
 *
 * @note This function does NOT require alignment. Stack variables in CUDA
 *       may not be 16-byte aligned, especially for packed structs.
 */
__device__ __host__ inline void copy_64B(void* dst, const void* src) {
#ifdef __CUDA_ARCH__
  // GPU: Use 8-byte loads/stores (uint64_t) for safety
  // uint4 (16-byte) requires 16-byte alignment which is not guaranteed
  // for stack variables or packed structs like NvmeCmd
  uint64_t* d = (uint64_t*)dst;
  const uint64_t* s = (const uint64_t*)src;
  #pragma unroll
  for (int i = 0; i < 8; i++) {
    d[i] = s[i];
  }
#else
  // Host: Use memcpy (compiler optimized)
  memcpy(dst, src, 64);
#endif
}

// ============================================================================
// Completion Queue Entry (CQE) Parsing
// ============================================================================

/**
 * @brief Extract phase bit from CQE
 * @param cqe Completion entry
 * @return Phase bit
 */
__device__ __host__ inline uint8_t cqe_phase(const NvmeCqe& cqe) {
  return static_cast<uint8_t>(cqe.status_p & 1u);
}

/**
 * @brief Extract Status Code Type from CQE
 * @param cqe Completion entry
 * @return Status code type
 */
__device__ __host__ inline uint8_t cqe_sct(const NvmeCqe& cqe) {
  return static_cast<uint8_t>((cqe.status_p >> 9) & 0x7);
}

/**
 * @brief Extract Status Code from CQE
 * @param cqe Completion entry
 * @return Status code
 */
__device__ __host__ inline uint8_t cqe_sc(const NvmeCqe& cqe) {
  return static_cast<uint8_t>((cqe.status_p >> 1) & 0xFF);
}

/**
 * @brief Extract DNR bit from CQE
 * @param cqe Completion entry
 * @return DNR bit
 */
__device__ __host__ inline uint8_t cqe_dnr(const NvmeCqe& cqe) {
  return static_cast<uint8_t>((cqe.status_p >> 15) & 1);
}

/**
 * @brief Check if status indicates error
 * @param status NVMe status
 * @return true if error
 */
__device__ __host__ inline bool status_is_error(const NvmeStatus& status) {
  return status.sct || status.sc;
}

// Note: Legacy host-side Queue operations have been removed.
// Modern code uses HostNvmeQueue template class (queue/host_nvme_queue.h)

} // namespace nvme_io_impl
