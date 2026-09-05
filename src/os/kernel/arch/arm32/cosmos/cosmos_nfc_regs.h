#ifndef SIMPLE_COSMOS_NFC_REGS_H
#define SIMPLE_COSMOS_NFC_REGS_H

#include "cosmos_hal.h"

/*
 * Tiger4NSC/V2F contract from Cosmos-OpenSSD/Cosmos-plus-OpenSSD commit
 * 78601486bb5581e40628ec7e841dea8e97eff034:
 *   source/software/GreedyFTL-3.0.0/nsc_driver.{h,c}
 *   source/software/GreedyFTL-3.0.0/ftl_config.h
 *   source/software/GreedyFTL-3.0.0/request_schedule.c
 *   source/hardware/nfc-substrate/tiger4_nfc_substrate-1.0.0/Dispatcher.v
 *   source/hardware/nfc-substrate/tiger4_nfc_substrate-1.0.0/Decoder.v
 *   source/hardware/nfc-substrate/tiger4_nfc_substrate-1.0.0/
 *     CompletionDataChannel.v
 *   source/hardware/nfc-substrate/tiger4_nfc_substrate-1.0.0/
 *     BCHDecoderOutputControl.v
 *   project/Prebuild/8Ch8Way-3.0.0/OpenSSD2-8C8W-Prebuild-3.0.0.hdf
 * The HDF's OpenSSD2.hwh binds eight Tiger4NSC v1.1.0 instances, eight
 * ways each, at 0x43c00000..0x43c7ffff. The IP exposes no identity register.
 * Command values below are uProgROM entry addresses, so they are bitstream
 * specific rather than portable NAND opcodes.
 */
#define COSMOS_NFC_CHANNEL0_BASE             0x43C00000U
#define COSMOS_NFC_CHANNEL_STRIDE            0x00010000U
#define COSMOS_NFC_CHANNEL_COUNT             8U
#define COSMOS_NFC_WAY_COUNT                 8U

#define COSMOS_NFC_CMD_SELECT                0x00U
#define COSMOS_NFC_ROW_ADDRESS               0x04U
#define COSMOS_NFC_USER_DATA                 0x08U
#define COSMOS_NFC_DATA_ADDRESS              0x0CU
#define COSMOS_NFC_SPARE_ADDRESS             0x10U
#define COSMOS_NFC_ERROR_COUNT_ADDRESS       0x14U
#define COSMOS_NFC_COMPLETION_ADDRESS        0x18U
#define COSMOS_NFC_WAY_SELECTION             0x1CU
#define COSMOS_NFC_CHANNEL_BUSY              0x20U
#define COSMOS_NFC_READY_BUSY                0x24U
#define COSMOS_NFC_CONTROLLER_IDLE           0x2CU

#define COSMOS_NFC_CMD_RESET                 1U
#define COSMOS_NFC_CMD_SET_FEATURES          6U
#define COSMOS_NFC_CMD_READ_PAGE_TRIGGER     13U
#define COSMOS_NFC_CMD_READ_PAGE_TRANSFER    18U
#define COSMOS_NFC_CMD_READ_PAGE_TRANSFER_RAW 55U
#define COSMOS_NFC_CMD_PROGRAM_PAGE          28U
#define COSMOS_NFC_CMD_BLOCK_ERASE           37U
#define COSMOS_NFC_CMD_STATUS_CHECK          41U

#define COSMOS_NFC_PAGE_DATA_BYTES           16384U
#define COSMOS_NFC_PAGE_SPARE_BYTES          256U
#define COSMOS_NFC_RAW_ROW_BYTES              18048U
#define COSMOS_NFC_ERROR_INFO_WORDS          11U
#define COSMOS_NFC_ECC_WARNING_THRESHOLD     20U
#define COSMOS_NFC_ROWS_PER_BLOCK            256U
#define COSMOS_NFC_LUN0_BASE_ROW              0x00000000U
#define COSMOS_NFC_LUN1_BASE_ROW              0x00200000U
#define COSMOS_NFC_ROWS_PER_LUN               0x00105800U
#ifndef COSMOS_NFC_POLL_LIMIT
#define COSMOS_NFC_POLL_LIMIT                COSMOS_POLL_LIMIT
#endif

#define COSMOS_NFC_STATUS_REPORT_DONE        0x1U
#define COSMOS_NFC_TRANSFER_COMPLETE         0xA5000001U
#define COSMOS_NFC_STATUS_COMPLETE_MASK      0x60U
#define COSMOS_NFC_STATUS_FAIL_MASK          0x03U
#define COSMOS_NFC_ECC_CRC_VALID             0x10000000U
#define COSMOS_NFC_ECC_SPARE_VALID           0x01000000U
#define COSMOS_NFC_ECC_WORST_MASK            0x00FF0000U
#define COSMOS_NFC_ECC_WORST_SHIFT           16U

/*
 * The trusted package step may emit this token only after verifying the
 * official HDF bitstream whose OpenSSD2.bit SHA-256 is
 * 66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2.
 */
#if defined(COSMOS_NFC_PACKAGE_VERIFIED_OPENSSD2_8C8W_3_0_0)
#define COSMOS_NFC_REGISTER_CONTRACT_BOUND 1
#else
#define COSMOS_NFC_REGISTER_CONTRACT_BOUND 0
#endif

/*
 * Exact GreedyFTL-3.0.0 memory_map.h pools for the 8-channel/8-way profile.
 * Host MMIO tests use the production addresses so range checks cannot pass
 * through a synthetic all-purpose DMA window.
 */
#if defined(COSMOS_MMIO_TEST)
#define COSMOS_NFC_NVME_MANAGEMENT_BASE        0x00200000U
#define COSMOS_NFC_NVME_MANAGEMENT_END         0x002FFFFFU
#define COSMOS_NFC_DATA_POOL_BASE              0x10000000U
#define COSMOS_NFC_DATA_POOL_END               0x110FFFFFU
#define COSMOS_NFC_SPARE_POOL_BASE             0x11100000U
#define COSMOS_NFC_SPARE_POOL_END              0x11143FFFU
#define COSMOS_NFC_COMPLETION_POOL_BASE        0x17000000U
#define COSMOS_NFC_COMPLETION_POOL_END         0x170000FFU
#define COSMOS_NFC_STATUS_POOL_BASE            0x17000100U
#define COSMOS_NFC_STATUS_POOL_END             0x170001FFU
#define COSMOS_NFC_ERROR_POOL_BASE             0x17000200U
#define COSMOS_NFC_ERROR_POOL_END              0x17000CFFU
#define COSMOS_NFC_TOGGLE_POOL_BASE            0x17000D00U
#define COSMOS_NFC_TOGGLE_POOL_END             0x17001CFFU
#endif

#if COSMOS_NFC_REGISTER_CONTRACT_BOUND && \
    defined(COSMOS_NFC_DATA_POOL_BASE) && \
    defined(COSMOS_NFC_DATA_POOL_END) && \
    defined(COSMOS_NFC_SPARE_POOL_BASE) && \
    defined(COSMOS_NFC_SPARE_POOL_END) && \
    defined(COSMOS_NFC_COMPLETION_POOL_BASE) && \
    defined(COSMOS_NFC_COMPLETION_POOL_END) && \
    defined(COSMOS_NFC_STATUS_POOL_BASE) && \
    defined(COSMOS_NFC_STATUS_POOL_END) && \
    defined(COSMOS_NFC_ERROR_POOL_BASE) && \
    defined(COSMOS_NFC_ERROR_POOL_END) && \
    defined(COSMOS_NFC_TOGGLE_POOL_BASE) && \
    defined(COSMOS_NFC_TOGGLE_POOL_END)
#define COSMOS_NFC_IO_CONTRACT_BOUND 1
#else
#define COSMOS_NFC_IO_CONTRACT_BOUND 0
#endif

#ifndef COSMOS_NFC_NVME_MANAGEMENT_BASE
#define COSMOS_NFC_NVME_MANAGEMENT_BASE        0U
#endif
#ifndef COSMOS_NFC_NVME_MANAGEMENT_END
#define COSMOS_NFC_NVME_MANAGEMENT_END         0U
#endif
#ifndef COSMOS_NFC_DATA_POOL_BASE
#define COSMOS_NFC_DATA_POOL_BASE              0U
#endif
#ifndef COSMOS_NFC_DATA_POOL_END
#define COSMOS_NFC_DATA_POOL_END               0U
#endif
#ifndef COSMOS_NFC_SPARE_POOL_BASE
#define COSMOS_NFC_SPARE_POOL_BASE             0U
#endif
#ifndef COSMOS_NFC_SPARE_POOL_END
#define COSMOS_NFC_SPARE_POOL_END              0U
#endif
#ifndef COSMOS_NFC_COMPLETION_POOL_BASE
#define COSMOS_NFC_COMPLETION_POOL_BASE        0U
#endif
#ifndef COSMOS_NFC_COMPLETION_POOL_END
#define COSMOS_NFC_COMPLETION_POOL_END         0U
#endif
#ifndef COSMOS_NFC_STATUS_POOL_BASE
#define COSMOS_NFC_STATUS_POOL_BASE            0U
#endif
#ifndef COSMOS_NFC_STATUS_POOL_END
#define COSMOS_NFC_STATUS_POOL_END             0U
#endif
#ifndef COSMOS_NFC_ERROR_POOL_BASE
#define COSMOS_NFC_ERROR_POOL_BASE             0U
#endif
#ifndef COSMOS_NFC_ERROR_POOL_END
#define COSMOS_NFC_ERROR_POOL_END              0U
#endif
#ifndef COSMOS_NFC_TOGGLE_POOL_BASE
#define COSMOS_NFC_TOGGLE_POOL_BASE            0U
#endif
#ifndef COSMOS_NFC_TOGGLE_POOL_END
#define COSMOS_NFC_TOGGLE_POOL_END             0U
#endif

#define COSMOS_NFC_ERROR_INFO_BYTES \
    (COSMOS_NFC_ERROR_INFO_WORDS * sizeof(unsigned int))

struct cosmos_nfc_io {
    unsigned int channel;
    unsigned int way;
    unsigned int row_address;         /* Tiger4NSC consumes 24 bits. */
    unsigned int data_address;        /* 16 KiB uncached DMA region. */
    unsigned int spare_address;       /* 256-byte uncached DMA region. */
    unsigned int error_info_address;  /* Eleven uncached DMA words. */
    unsigned int completion_address;  /* One uncached DMA word. */
    unsigned int status_report_address; /* One uncached status word. */
};

struct cosmos_nfc_ecc {
    unsigned int crc_valid;           /* Error word 0, bit 28. */
    unsigned int spare_valid;         /* Error word 0, bit 24. */
    unsigned int page_valid;          /* Error word 1 is 0xffffffff. */
    unsigned int worst_chunk_errors;  /* Error word 0, bits 23:16. */
    unsigned int needs_refresh;       /* GreedyFTL threshold: >20. */
};

/*
 * Calls are synchronous and serialized per channel. After COSMOS_TIMEOUT, all
 * supplied DMA regions remain globally controller-owned until an explicit
 * SoC/PL hardware reset.
 */
int cosmos_nfc_read_page(const struct cosmos_nfc_io *io,
                         struct cosmos_nfc_ecc *ecc);
/*
 * Raw marker read: command 55 DMA-writes one contiguous 18,048-byte NAND row
 * at data_address. spare_address and error_info_address are not consumed.
 */
int cosmos_nfc_read_page_raw(const struct cosmos_nfc_io *io);
int cosmos_nfc_program_page(const struct cosmos_nfc_io *io);
int cosmos_nfc_erase_block(unsigned int channel, unsigned int way,
                           unsigned int row_address,
                           unsigned int status_report_address);
int cosmos_nfc_status(unsigned int channel, unsigned int way,
                      unsigned int status_report_address,
                      unsigned int *nand_status);
int cosmos_nfc_decode_ecc(const volatile unsigned int *error_info,
                          struct cosmos_nfc_ecc *ecc);

#endif
