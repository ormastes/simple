/**
 * @file nvme_types.h
 * @brief Core NVMe protocol types (host and GPU agnostic)
 *
 * This header contains pure NVMe protocol definitions that are independent
 * of host/GPU implementation. No external dependencies required.
 */

#pragma once
#include "cuda_utils.h"  // Provides short type names (uint32_t, size_t, etc.)
#include "doorbell/nvme_doorbell.h"

// ============================================================================
// NVMe Command and Completion Structures
// ============================================================================

#pragma pack(push,1)

/**
 * @brief NVMe command structure (64 bytes)
 *
 * NVMe 1.4 specification, Section 4.2 (Submission Queue Entry - Command Format)
 */
struct NvmeCmd {
    uint8_t  opc;         ///< Opcode
    uint8_t  fuse_psdt;   ///< Fused operation and PRP/SGL descriptor type
    uint16_t cid;         ///< Command identifier
    uint32_t nsid;        ///< Namespace identifier
    uint64_t rsvd2;       ///< Reserved
    uint64_t mptr;        ///< Metadata pointer
    uint64_t prp1;        ///< Physical region page 1
    uint64_t prp2;        ///< Physical region page 2 or PRP list pointer
    uint32_t cdw10;       ///< Command dword 10
    uint32_t cdw11;       ///< Command dword 11
    uint32_t cdw12;       ///< Command dword 12
    uint32_t cdw13;       ///< Command dword 13
    uint32_t cdw14;       ///< Command dword 14
    uint32_t cdw15;       ///< Command dword 15
};

/**
 * @brief NVMe completion queue entry (16 bytes)
 *
 * NVMe 1.4 specification, Section 4.6 (Completion Queue Entry)
 */
struct NvmeCqe {
    uint32_t dw0;         ///< Command specific dword 0
    uint32_t rsvd;        ///< Reserved
    uint16_t sqhd;        ///< Submission queue head pointer
    uint16_t sqid;        ///< Submission queue identifier
    uint16_t cid;         ///< Command identifier
    uint16_t status_p;    ///< Status field [15:1] and phase tag [0]
};

#pragma pack(pop)

// ============================================================================
// NVMe Opcodes
// ============================================================================

enum : uint8_t {
    OPC_ADMIN_CREATE_IO_SQ = 0x01,  ///< Admin: Create I/O Submission Queue
    OPC_ADMIN_CREATE_IO_CQ = 0x05,  ///< Admin: Create I/O Completion Queue
    OPC_NVM_READ           = 0x02,  ///< NVM: Read
    OPC_NVM_WRITE          = 0x01   ///< NVM: Write
};

// ============================================================================
// Status and Error Codes
// ============================================================================

/**
 * @brief NVMe command completion status
 */
struct NvmeStatus {
    uint8_t sct{0};   ///< Status code type
    uint8_t sc{0};    ///< Status code
    bool dnr{false};       ///< Do not retry

    /**
     * @brief Check if status indicates an error
     * @return true if error occurred (sct or sc is non-zero)
     */
    inline bool is_error() const {
        return sct || sc;
    }
};

/**
 * @brief Enhanced error codes for queue operations
 */
constexpr uint16_t NVME_CID_QUEUE_FULL = 0xFFFE;  ///< Submission queue is full
constexpr uint16_t NVME_CID_ERROR      = 0xFFFF;  ///< Invalid arguments or error

// ============================================================================
// Operation Control Enums
// ============================================================================

/**
 * @brief Completion queue poll result codes
 */
enum PollResult : uint8_t {
    POLL_READY     = 0,  ///< Completion available
    POLL_NOT_READY = 1,  ///< No completion yet (async mode only)
    POLL_TIMEOUT   = 2,  ///< Timeout expired (sync mode only)
    POLL_ERROR     = 3   ///< Invalid parameters
};

/**
 * @brief Async type for poll operations
 */
enum AsyncType : uint8_t {
    ASYNC_TYPE_SYNC  = 0,  ///< Blocking with optional timeout (default)
    ASYNC_TYPE_ASYNC = 1   ///< Non-blocking, return immediately
};

/**
 * @brief Command type for unified submit API
 */
enum CommandType : uint8_t {
    CMD_READ  = 0,  ///< NVM Read command
    CMD_WRITE = 1   ///< NVM Write command
};
