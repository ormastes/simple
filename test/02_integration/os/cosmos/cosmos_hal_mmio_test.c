#define _GNU_SOURCE

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "cosmos_hal.h"
#include "cosmos_nfc_regs.h"
#include "cosmos_pcie_regs.h"
#include "cosmos_zynq_regs.h"

#define TEST_BUFFER_MAP_BASE  COSMOS_NFC_DATA_POOL_BASE
#define TEST_BUFFER_MAP_BYTES \
    (COSMOS_NFC_SPARE_POOL_END - COSMOS_NFC_DATA_POOL_BASE + 1U)
#define TEST_CONTROL_MAP_BASE COSMOS_NFC_COMPLETION_POOL_BASE
#define TEST_CONTROL_MAP_BYTES 0x00002000U
#define TEST_TOGGLE_ADDRESS    COSMOS_NFC_TOGGLE_POOL_BASE
#define TEST_NO_CHANNEL        UINT_MAX

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                     \
                    __FILE__, __LINE__, #condition);                          \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define CHECK_STATUS(call, expected)                                          \
    do {                                                                      \
        int actual_status = (call);                                           \
        if (actual_status != (expected)) {                                    \
            fprintf(stderr, "%s:%d: %s returned %d, expected %d\n",          \
                    __FILE__, __LINE__, #call, actual_status, (expected));     \
            return 1;                                                         \
        }                                                                     \
    } while (0)

struct mock_nfc_channel {
    unsigned int registers[(COSMOS_NFC_CONTROLLER_IDLE / 4U) + 1U];
    unsigned int busy_reads;
};

struct mock_mmio {
    unsigned int slcr_lock;
    unsigned int arm_clock;
    unsigned int ddr_clock;
    unsigned int pss_reset;
    unsigned int a9_reset;
    unsigned int devcfg_status;
    unsigned int pcie_status;
    unsigned int pcie_function;
    unsigned int pcie_nvme;
    unsigned int pcie_admin;
    unsigned int pcie_irq_status;
    unsigned int pcie_irq_mask;
    unsigned int pcie_irq_clear;
    unsigned int pcie_queue_clears;
    unsigned int pcie_status_reads;
    unsigned int pl_reads;
    unsigned int pl_writes;
    unsigned int nfc_writes;
    unsigned int nfc_commands[64];
    unsigned int force_busy_channel;
    unsigned int suppress_transfer_channel;
    unsigned int raw_completion_error_channel;
    struct mock_nfc_channel nfc[COSMOS_NFC_CHANNEL_COUNT];
};

static struct mock_mmio mock;

static void mock_fail(const char *message, unsigned int address) {
    fprintf(stderr, "mock MMIO failure: %s at 0x%08x\n", message, address);
    _exit(90);
}

static int mock_is_nfc(unsigned int address) {
    return address >= COSMOS_NFC_CHANNEL0_BASE &&
        address < COSMOS_NFC_CHANNEL0_BASE +
            COSMOS_NFC_CHANNEL_COUNT * COSMOS_NFC_CHANNEL_STRIDE;
}

static int mock_is_pcie(unsigned int address) {
    return address >= COSMOS_PCIE_HOST_BASE &&
        address < COSMOS_PCIE_HOST_BASE + COSMOS_PCIE_HOST_SPAN;
}

static int mock_is_pcie_queue_control(unsigned int offset) {
    unsigned int queue;

    for (queue = 0U; queue < COSMOS_PCIE_IO_QUEUE_COUNT; ++queue) {
        unsigned int control =
            queue * COSMOS_PCIE_IO_QUEUE_STRIDE +
            COSMOS_PCIE_IO_QUEUE_CONTROL_WORD;

        if (offset == COSMOS_PCIE_IO_SQ_OFFSET + control ||
            offset == COSMOS_PCIE_IO_CQ_OFFSET + control) {
            return 1;
        }
    }
    return 0;
}

static void mock_require_configured_pl(unsigned int address) {
    if ((mock.devcfg_status & COSMOS_ZYNQ_DEVCFG_PCFG_DONE) == 0U) {
        mock_fail("unconfigured PL aperture access", address);
    }
}

static volatile unsigned int *mock_dma_word(unsigned int address) {
    int in_buffers =
        address >= TEST_BUFFER_MAP_BASE &&
        address <= COSMOS_NFC_SPARE_POOL_END - sizeof(unsigned int) + 1U;
    int in_control =
        address >= TEST_CONTROL_MAP_BASE &&
        address <= COSMOS_NFC_TOGGLE_POOL_END - sizeof(unsigned int) + 1U;
    if ((!in_buffers && !in_control) ||
        (address & 3U) != 0U) {
        mock_fail("invalid DMA address", address);
    }
    return (volatile unsigned int *)(uintptr_t)address;
}

static void mock_reset(void) {
    memset(&mock, 0, sizeof(mock));
    memset((void *)(uintptr_t)TEST_BUFFER_MAP_BASE, 0,
           TEST_BUFFER_MAP_BYTES);
    memset((void *)(uintptr_t)TEST_CONTROL_MAP_BASE, 0,
           TEST_CONTROL_MAP_BYTES);
    mock.force_busy_channel = TEST_NO_CHANNEL;
    mock.suppress_transfer_channel = TEST_NO_CHANNEL;
    mock.raw_completion_error_channel = TEST_NO_CHANNEL;
}

static void mock_valid_fsbl(int pcfg_done) {
    mock.slcr_lock = 1U;
    mock.arm_clock = 0x1FU << 24U;
    mock.ddr_clock = 3U;
    mock.pss_reset = 0U;
    mock.a9_reset = 0U;
    mock.devcfg_status =
        pcfg_done ? COSMOS_ZYNQ_DEVCFG_PCFG_DONE : 0U;
}

static unsigned int mock_nfc_read(unsigned int address) {
    unsigned int relative = address - COSMOS_NFC_CHANNEL0_BASE;
    unsigned int channel = relative / COSMOS_NFC_CHANNEL_STRIDE;
    unsigned int offset = relative % COSMOS_NFC_CHANNEL_STRIDE;

    if (channel >= COSMOS_NFC_CHANNEL_COUNT ||
        offset > COSMOS_NFC_CONTROLLER_IDLE || (offset & 3U) != 0U) {
        mock_fail("unknown NFC read", address);
    }
    if (offset == COSMOS_NFC_CHANNEL_BUSY) {
        mock.nfc[channel].busy_reads++;
        return channel == mock.force_busy_channel ? 1U : 0U;
    }
    if (offset == COSMOS_NFC_READY_BUSY) {
        return (1U << COSMOS_NFC_WAY_COUNT) - 1U;
    }
    if (offset == COSMOS_NFC_CONTROLLER_IDLE) {
        return 1U;
    }
    mock_fail("unknown NFC read", address);
    return 0U;
}

static void mock_complete_status(unsigned int channel) {
    unsigned int address =
        mock.nfc[channel]
            .registers[COSMOS_NFC_COMPLETION_ADDRESS / 4U];

    *mock_dma_word(address) = 0xC1U;
}

static void mock_complete_read(unsigned int channel) {
    unsigned int data =
        mock.nfc[channel]
            .registers[COSMOS_NFC_DATA_ADDRESS / 4U];
    unsigned int spare =
        mock.nfc[channel]
            .registers[COSMOS_NFC_SPARE_ADDRESS / 4U];
    unsigned int completion =
        mock.nfc[channel]
            .registers[COSMOS_NFC_COMPLETION_ADDRESS / 4U];
    unsigned int error_info =
        mock.nfc[channel]
            .registers[COSMOS_NFC_ERROR_COUNT_ADDRESS / 4U];
    volatile unsigned int *errors;

    if (channel == mock.suppress_transfer_channel) {
        return;
    }
    memset((void *)(uintptr_t)data, 0x5AU, COSMOS_NFC_PAGE_DATA_BYTES);
    memset((void *)(uintptr_t)spare, 0xA5U, COSMOS_NFC_PAGE_SPARE_BYTES);
    errors = mock_dma_word(error_info);
    errors[0] = COSMOS_NFC_ECC_CRC_VALID |
        COSMOS_NFC_ECC_SPARE_VALID |
        (21U << COSMOS_NFC_ECC_WORST_SHIFT);
    errors[1] = 0xFFFFFFFFU;
    *mock_dma_word(completion) = COSMOS_NFC_TRANSFER_COMPLETE;
}

static void mock_complete_raw_read(unsigned int channel) {
    unsigned int data =
        mock.nfc[channel].registers[COSMOS_NFC_DATA_ADDRESS / 4U];
    unsigned int completion =
        mock.nfc[channel].registers[COSMOS_NFC_COMPLETION_ADDRESS / 4U];

    if (channel == mock.suppress_transfer_channel) {
        return;
    }
    memset((void *)(uintptr_t)data, 0xB6U, COSMOS_NFC_RAW_ROW_BYTES);
    *(volatile unsigned char *)(uintptr_t)(
        data + COSMOS_NFC_PAGE_DATA_BYTES) = 0x4DU;
    *mock_dma_word(completion) =
        channel == mock.raw_completion_error_channel ?
        0xA5000002U : COSMOS_NFC_TRANSFER_COMPLETE;
}

static void mock_nfc_write(unsigned int address, unsigned int value) {
    unsigned int relative = address - COSMOS_NFC_CHANNEL0_BASE;
    unsigned int channel = relative / COSMOS_NFC_CHANNEL_STRIDE;
    unsigned int offset = relative % COSMOS_NFC_CHANNEL_STRIDE;

    if (channel >= COSMOS_NFC_CHANNEL_COUNT ||
        offset > COSMOS_NFC_CONTROLLER_IDLE || (offset & 3U) != 0U) {
        mock_fail("unknown NFC write", address);
    }
    if (offset != COSMOS_NFC_CMD_SELECT &&
        offset != COSMOS_NFC_ROW_ADDRESS &&
        offset != COSMOS_NFC_USER_DATA &&
        offset != COSMOS_NFC_DATA_ADDRESS &&
        offset != COSMOS_NFC_SPARE_ADDRESS &&
        offset != COSMOS_NFC_ERROR_COUNT_ADDRESS &&
        offset != COSMOS_NFC_COMPLETION_ADDRESS &&
        offset != COSMOS_NFC_WAY_SELECTION) {
        mock_fail("unknown NFC write", address);
    }
    mock.nfc_writes++;
    mock.nfc[channel].registers[offset / 4U] = value;
    if (offset != COSMOS_NFC_CMD_SELECT) {
        return;
    }
    if (value >= sizeof(mock.nfc_commands) /
            sizeof(mock.nfc_commands[0])) {
        mock_fail("unknown NFC command", address);
    }
    mock.nfc_commands[value]++;
    if (value == COSMOS_NFC_CMD_SET_FEATURES) {
        unsigned int payload =
            mock.nfc[channel].registers[COSMOS_NFC_USER_DATA / 4U];
        volatile unsigned int *words = mock_dma_word(payload);

        if (payload != TEST_TOGGLE_ADDRESS ||
            words[0] != 0x00000006U ||
            words[1] != 0x00000008U ||
            words[2] != 0x00000020U) {
            mock_fail("invalid NFC toggle payload", payload);
        }
    } else if (value == COSMOS_NFC_CMD_STATUS_CHECK) {
        mock_complete_status(channel);
    } else if (value == COSMOS_NFC_CMD_READ_PAGE_TRANSFER) {
        mock_complete_read(channel);
    } else if (value == COSMOS_NFC_CMD_READ_PAGE_TRANSFER_RAW) {
        mock_complete_raw_read(channel);
    }
}

unsigned int cosmos_mmio_test_read32(unsigned int address) {
    if (address == COSMOS_ZYNQ_DEVCFG_BASE +
            COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET) {
        return mock.devcfg_status;
    }
    if (address == COSMOS_SLCR_BASE + COSMOS_ZYNQ_SLCR_LOCKSTA_OFFSET) {
        return mock.slcr_lock;
    }
    if (address == COSMOS_SLCR_BASE + COSMOS_ZYNQ_SLCR_ARM_CLK_OFFSET) {
        return mock.arm_clock;
    }
    if (address == COSMOS_SLCR_BASE + COSMOS_ZYNQ_SLCR_DDR_CLK_OFFSET) {
        return mock.ddr_clock;
    }
    if (address == COSMOS_SLCR_BASE + COSMOS_ZYNQ_SLCR_PSS_RST_OFFSET) {
        return mock.pss_reset;
    }
    if (address == COSMOS_SLCR_BASE + COSMOS_ZYNQ_SLCR_A9_RST_OFFSET) {
        return mock.a9_reset;
    }
    if (mock_is_nfc(address)) {
        mock_require_configured_pl(address);
        mock.pl_reads++;
        return mock_nfc_read(address);
    }
    if (mock_is_pcie(address)) {
        unsigned int offset;

        mock_require_configured_pl(address);
        mock.pl_reads++;
        offset = address - COSMOS_PCIE_HOST_BASE;
        if (offset == COSMOS_PCIE_IRQ_STATUS_OFFSET) {
            return mock.pcie_irq_status;
        }
        if (offset == COSMOS_PCIE_STATUS_OFFSET) {
            mock.pcie_status_reads++;
            return mock.pcie_status;
        }
        if (offset == COSMOS_PCIE_FUNCTION_OFFSET) {
            return mock.pcie_function;
        }
        if (offset == COSMOS_PCIE_NVME_STATUS_OFFSET) {
            return mock.pcie_nvme;
        }
        if (offset == COSMOS_PCIE_ADMIN_QUEUE_OFFSET) {
            return mock.pcie_admin;
        }
        mock_fail("unknown PCIe read", address);
    }
    mock_fail("unknown read", address);
    return 0U;
}

void cosmos_mmio_test_write32(unsigned int address, unsigned int value) {
    if (mock_is_nfc(address)) {
        mock_require_configured_pl(address);
        mock.pl_writes++;
        mock_nfc_write(address, value);
        return;
    }
    if (mock_is_pcie(address)) {
        unsigned int offset = address - COSMOS_PCIE_HOST_BASE;

        mock_require_configured_pl(address);
        mock.pl_writes++;
        if (offset == COSMOS_PCIE_IRQ_MASK_OFFSET &&
            (value == 0U || value == COSMOS_PCIE_IRQ_DEFINED_MASK)) {
            mock.pcie_irq_mask = value;
            return;
        }
        if (offset == COSMOS_PCIE_IRQ_CLEAR_OFFSET &&
            (value & ~COSMOS_PCIE_IRQ_DEFINED_MASK) == 0U) {
            mock.pcie_irq_clear |= value;
            mock.pcie_irq_status &= ~value;
            return;
        }
        if (offset == COSMOS_PCIE_NVME_STATUS_OFFSET && value == 0U) {
            mock.pcie_nvme = 0U;
            return;
        }
        if (offset == COSMOS_PCIE_ADMIN_QUEUE_OFFSET && value == 0U) {
            mock.pcie_admin = 0U;
            return;
        }
        if (mock_is_pcie_queue_control(offset) && value == 0U) {
            mock.pcie_queue_clears++;
            return;
        }
        mock_fail("unknown PCIe write", address);
    }
    mock_fail("unknown write", address);
}

static struct cosmos_nfc_io test_nfc_io(unsigned int channel) {
    unsigned int slot = channel * COSMOS_NFC_WAY_COUNT + 2U;
    struct cosmos_nfc_io io = {
        channel,
        2U,
        0x00000100U,
        COSMOS_NFC_DATA_POOL_BASE +
            slot * COSMOS_NFC_PAGE_DATA_BYTES,
        COSMOS_NFC_SPARE_POOL_BASE +
            slot * COSMOS_NFC_PAGE_SPARE_BYTES,
        COSMOS_NFC_ERROR_POOL_BASE +
            slot * COSMOS_NFC_ERROR_INFO_BYTES,
        COSMOS_NFC_COMPLETION_POOL_BASE +
            slot * sizeof(unsigned int),
        COSMOS_NFC_STATUS_POOL_BASE +
            slot * sizeof(unsigned int)
    };
    return io;
}

static int test_fsbl_handoff(void) {
    mock_valid_fsbl(1);
    CHECK_STATUS(cosmos_fsbl_validate_handoff(), COSMOS_OK);
    mock.devcfg_status = 0U;
    CHECK_STATUS(cosmos_fsbl_validate_handoff(), COSMOS_HW_ERROR);
    mock_valid_fsbl(1);
    mock.slcr_lock = 0U;
    CHECK_STATUS(cosmos_fsbl_validate_handoff(), COSMOS_HW_ERROR);
    CHECK(mock.pl_reads == 0U && mock.pl_writes == 0U);
    return 0;
}

static int test_unconfigured_pl_is_not_touched(void) {
    CHECK_STATUS(cosmos_nfc_init(), COSMOS_UNAVAILABLE);
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_UNAVAILABLE);
    CHECK(mock.pl_reads == 0U && mock.pl_writes == 0U);
    return 0;
}

static int test_nfc_init_timeout_is_bounded(void) {
    mock_valid_fsbl(1);
    mock.force_busy_channel = 0U;
    CHECK_STATUS(cosmos_nfc_init(), COSMOS_TIMEOUT);
    CHECK(mock.nfc[0].busy_reads == COSMOS_NFC_POLL_LIMIT);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_RESET] == 1U);
    return 0;
}

static int test_nfc_io_and_ecc(void) {
    struct cosmos_nfc_io io;
    struct cosmos_nfc_io invalid;
    struct cosmos_nfc_ecc ecc;
    unsigned int nand_status;
    unsigned int reset_count =
        COSMOS_NFC_CHANNEL_COUNT * COSMOS_NFC_WAY_COUNT;
    unsigned int writes_after_init;

    mock_valid_fsbl(1);
    CHECK_STATUS(cosmos_nfc_init(), COSMOS_OK);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_RESET] == reset_count);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_SET_FEATURES] == reset_count);

    io = test_nfc_io(1U);
    writes_after_init = mock.nfc_writes;
    invalid = io;
    invalid.data_address = COSMOS_NFC_NVME_MANAGEMENT_BASE;
    CHECK_STATUS(cosmos_nfc_read_page(&invalid, &ecc), COSMOS_INVALID);
    invalid = io;
    invalid.data_address += sizeof(unsigned int);
    CHECK_STATUS(cosmos_nfc_program_page(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.spare_address += sizeof(unsigned int);
    CHECK_STATUS(cosmos_nfc_program_page(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.error_info_address += sizeof(unsigned int);
    CHECK_STATUS(cosmos_nfc_read_page(&invalid, &ecc), COSMOS_INVALID);
    invalid = io;
    invalid.completion_address += 2U;
    CHECK_STATUS(cosmos_nfc_read_page(&invalid, &ecc), COSMOS_INVALID);
    invalid = io;
    invalid.status_report_address += 2U;
    CHECK_STATUS(cosmos_nfc_program_page(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.data_address = COSMOS_NFC_SPARE_POOL_BASE;
    CHECK_STATUS(cosmos_nfc_program_page(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.spare_address = COSMOS_NFC_DATA_POOL_BASE;
    CHECK_STATUS(cosmos_nfc_program_page(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.error_info_address = COSMOS_NFC_COMPLETION_POOL_BASE;
    CHECK_STATUS(cosmos_nfc_read_page(&invalid, &ecc), COSMOS_INVALID);
    invalid = io;
    invalid.completion_address = COSMOS_NFC_STATUS_POOL_BASE;
    CHECK_STATUS(cosmos_nfc_read_page(&invalid, &ecc), COSMOS_INVALID);
    invalid = io;
    invalid.status_report_address = COSMOS_NFC_COMPLETION_POOL_BASE;
    CHECK_STATUS(cosmos_nfc_program_page(&invalid), COSMOS_INVALID);
    CHECK(mock.nfc_writes == writes_after_init);

    CHECK_STATUS(cosmos_nfc_read_page(&io, &ecc), COSMOS_OK);
    CHECK(ecc.crc_valid == 1U && ecc.spare_valid == 1U);
    CHECK(ecc.page_valid == 1U && ecc.worst_chunk_errors == 21U);
    CHECK(ecc.needs_refresh == 1U);
    CHECK(*(volatile unsigned char *)(uintptr_t)io.data_address == 0x5AU);
    CHECK(*(volatile unsigned char *)(uintptr_t)
        (io.data_address + COSMOS_NFC_PAGE_DATA_BYTES - 1U) == 0x5AU);
    CHECK(*(volatile unsigned char *)(uintptr_t)io.spare_address == 0xA5U);
    CHECK_STATUS(cosmos_nfc_program_page(&io), COSMOS_OK);
    CHECK_STATUS(cosmos_nfc_erase_block(
        io.channel, io.way, 0x00000100U,
        io.status_report_address), COSMOS_OK);
    CHECK_STATUS(cosmos_nfc_status(
        io.channel, io.way, io.status_report_address,
        &nand_status), COSMOS_OK);
    CHECK(nand_status == 0x60U);
    CHECK_STATUS(cosmos_nfc_erase_block(
        io.channel, io.way, 1U,
        io.status_report_address), COSMOS_INVALID);

    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_READ_PAGE_TRIGGER] == 1U);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_READ_PAGE_TRANSFER] == 1U);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_PROGRAM_PAGE] == 1U);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_BLOCK_ERASE] == 1U);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_STATUS_CHECK] == 4U);
    return 0;
}

static int test_nfc_timeout_quarantines_channel(void) {
    struct cosmos_nfc_io io;
    struct cosmos_nfc_io healthy_io;
    struct cosmos_nfc_io rejected_io;
    struct cosmos_nfc_ecc ecc;
    unsigned int writes_before_retry;

    mock_valid_fsbl(1);
    CHECK_STATUS(cosmos_nfc_init(), COSMOS_OK);
    io = test_nfc_io(3U);
    mock.suppress_transfer_channel = io.channel;
    CHECK_STATUS(cosmos_nfc_read_page(&io, &ecc), COSMOS_TIMEOUT);
    writes_before_retry = mock.nfc_writes;
    mock.suppress_transfer_channel = TEST_NO_CHANNEL;
    CHECK_STATUS(cosmos_nfc_program_page(&io), COSMOS_HW_ERROR);
    CHECK(mock.nfc_writes == writes_before_retry);

    healthy_io = test_nfc_io(4U);
    rejected_io = healthy_io;
    rejected_io.data_address = io.data_address;
    CHECK_STATUS(cosmos_nfc_program_page(&rejected_io), COSMOS_HW_ERROR);
    rejected_io = healthy_io;
    rejected_io.spare_address = io.spare_address;
    CHECK_STATUS(cosmos_nfc_program_page(&rejected_io), COSMOS_HW_ERROR);
    rejected_io = healthy_io;
    rejected_io.status_report_address = io.status_report_address;
    CHECK_STATUS(cosmos_nfc_program_page(&rejected_io), COSMOS_HW_ERROR);
    rejected_io = healthy_io;
    rejected_io.error_info_address = io.error_info_address;
    CHECK_STATUS(cosmos_nfc_read_page(&rejected_io, &ecc), COSMOS_HW_ERROR);
    rejected_io = healthy_io;
    rejected_io.completion_address = io.completion_address;
    CHECK_STATUS(cosmos_nfc_read_page(&rejected_io, &ecc), COSMOS_HW_ERROR);
    CHECK(mock.nfc_writes == writes_before_retry);

    CHECK_STATUS(cosmos_nfc_program_page(&healthy_io), COSMOS_OK);
    return 0;
}

static int test_nfc_raw_read(void) {
    struct cosmos_nfc_io io;
    struct cosmos_nfc_io invalid;
    struct cosmos_nfc_io overlapping;

    mock_valid_fsbl(1);
    CHECK_STATUS(cosmos_nfc_init(), COSMOS_OK);
    io = test_nfc_io(5U);

    invalid = io;
    invalid.channel = COSMOS_NFC_CHANNEL_COUNT;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.way = COSMOS_NFC_WAY_COUNT;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.row_address = COSMOS_NFC_LUN1_BASE_ROW +
        COSMOS_NFC_ROWS_PER_LUN;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.data_address = COSMOS_NFC_NVME_MANAGEMENT_BASE;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.completion_address += 2U;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.status_report_address += 2U;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_INVALID);
    invalid = io;
    invalid.error_info_address = COSMOS_NFC_NVME_MANAGEMENT_BASE;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&invalid), COSMOS_OK);
    CHECK(*(volatile unsigned char *)(uintptr_t)io.data_address == 0xB6U);
    CHECK(*(volatile unsigned char *)(uintptr_t)(
              io.data_address + COSMOS_NFC_PAGE_DATA_BYTES) == 0x4DU);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_READ_PAGE_TRIGGER] == 1U);
    CHECK(mock.nfc_commands[COSMOS_NFC_CMD_READ_PAGE_TRANSFER_RAW] == 1U);

    mock.raw_completion_error_channel = io.channel;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&io), COSMOS_HW_ERROR);
    mock.raw_completion_error_channel = TEST_NO_CHANNEL;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&io), COSMOS_OK);

    mock.suppress_transfer_channel = io.channel;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&io), COSMOS_TIMEOUT);
    mock.suppress_transfer_channel = TEST_NO_CHANNEL;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&io), COSMOS_HW_ERROR);

    overlapping = test_nfc_io(6U);
    overlapping.data_address = io.data_address;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&overlapping), COSMOS_HW_ERROR);
    overlapping = test_nfc_io(6U);
    overlapping.completion_address = io.completion_address;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&overlapping), COSMOS_HW_ERROR);
    overlapping = test_nfc_io(6U);
    overlapping.status_report_address = io.status_report_address;
    CHECK_STATUS(cosmos_nfc_read_page_raw(&overlapping), COSMOS_HW_ERROR);
    return 0;
}

static void mock_valid_pcie(void) {
    mock.pcie_status =
        COSMOS_PCIE_STATUS_LINK_UP | COSMOS_PCIE_LTSSM_L0;
    mock.pcie_function =
        COSMOS_PCIE_FUNCTION_BUS_MASTER |
        COSMOS_PCIE_FUNCTION_MSI_ENABLE |
        (COSMOS_PCIE_FUNCTION_MME_MAX <<
         COSMOS_PCIE_FUNCTION_MME_SHIFT);
    mock.pcie_nvme =
        COSMOS_PCIE_NVME_CC_ENABLE | COSMOS_PCIE_NVME_CSTS_READY;
    mock.pcie_admin =
        COSMOS_PCIE_ADMIN_CQ_VALID |
        COSMOS_PCIE_ADMIN_SQ_VALID |
        COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE;
}

static int test_pcie_states_are_bounded(void) {
    mock_valid_fsbl(1);
    mock_valid_pcie();
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_OK);

    mock.pcie_status = COSMOS_PCIE_LTSSM_L0;
    mock.pcie_status_reads = 0U;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_TIMEOUT);
    CHECK(mock.pcie_status_reads == COSMOS_POLL_LIMIT * 2U);

    mock_valid_pcie();
    mock.pcie_function &= ~COSMOS_PCIE_FUNCTION_BUS_MASTER;
    mock.pcie_status_reads = 0U;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_TIMEOUT);
    CHECK(mock.pcie_status_reads == COSMOS_POLL_LIMIT * 2U);

    mock_valid_pcie();
    mock.pcie_function &= ~COSMOS_PCIE_FUNCTION_MSI_ENABLE;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_TIMEOUT);

    mock_valid_pcie();
    mock.pcie_function |= COSMOS_PCIE_FUNCTION_MSIX_ENABLE;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_HW_ERROR);

    mock_valid_pcie();
    mock.pcie_admin = COSMOS_PCIE_ADMIN_SQ_VALID;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_HW_ERROR);

    mock_valid_pcie();
    mock.pcie_admin = 0U;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_HW_ERROR);

    mock_valid_pcie();
    mock.pcie_irq_status = 0U;
    CHECK_STATUS(cosmos_pcie_init(), COSMOS_OK);
    mock.pcie_status = COSMOS_PCIE_LTSSM_L0;
    mock.pcie_irq_status = COSMOS_PCIE_IRQ_LINK_CHANGE;
    CHECK_STATUS(cosmos_pcie_service_irq(), COSMOS_UNAVAILABLE);
    CHECK(!cosmos_pcie_is_available());
    CHECK(mock.pcie_irq_status == 0U);
    CHECK(mock.pcie_irq_clear == COSMOS_PCIE_IRQ_LINK_CHANGE);
    CHECK(mock.pcie_irq_mask == 0U);
    CHECK(mock.pcie_queue_clears ==
        2U * COSMOS_PCIE_IO_QUEUE_COUNT);
    return 0;
}

struct test_case {
    const char *name;
    int (*run)(void);
};

static int run_case(const struct test_case *test) {
    int status;
    pid_t child = fork();

    if (child < 0) {
        perror("fork");
        return 1;
    }
    if (child == 0) {
        mock_reset();
        _exit(test->run() == 0 ? 0 : 1);
    }
    if (waitpid(child, &status, 0) != child) {
        perror("waitpid");
        return 1;
    }
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        fprintf(stderr, "FAIL %s (status=%d)\n", test->name, status);
        return 1;
    }
    printf("PASS %s\n", test->name);
    return 0;
}

int main(void) {
    static const struct test_case tests[] = {
        {"FSBL handoff and PCFG_DONE", test_fsbl_handoff},
        {"unconfigured PL fail-closed", test_unconfigured_pl_is_not_touched},
        {"NFC bounded initialization", test_nfc_init_timeout_is_bounded},
        {"NFC read/program/erase/ECC", test_nfc_io_and_ecc},
        {"NFC raw marker read", test_nfc_raw_read},
        {"NFC timeout quarantine", test_nfc_timeout_quarantines_channel},
        {"PCIe link/function/MSI/admin", test_pcie_states_are_bounded}
    };
    void *buffers;
    void *control;
    size_t index;

    buffers = mmap((void *)(uintptr_t)TEST_BUFFER_MAP_BASE,
                   TEST_BUFFER_MAP_BYTES, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (buffers == MAP_FAILED) {
        perror("mmap test NFC buffers");
        return 1;
    }
    control = mmap((void *)(uintptr_t)TEST_CONTROL_MAP_BASE,
                   TEST_CONTROL_MAP_BYTES, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (control == MAP_FAILED) {
        perror("mmap test NFC control");
        (void)munmap(buffers, TEST_BUFFER_MAP_BYTES);
        return 1;
    }
    for (index = 0U; index < sizeof(tests) / sizeof(tests[0]); index++) {
        if (run_case(&tests[index]) != 0) {
            (void)munmap(control, TEST_CONTROL_MAP_BYTES);
            (void)munmap(buffers, TEST_BUFFER_MAP_BYTES);
            return 1;
        }
    }
    if (munmap(control, TEST_CONTROL_MAP_BYTES) != 0 ||
        munmap(buffers, TEST_BUFFER_MAP_BYTES) != 0) {
        perror("munmap test NFC DMA");
        return 1;
    }
    puts("STATUS: PASS cosmos host mock-MMIO integration");
    return 0;
}
