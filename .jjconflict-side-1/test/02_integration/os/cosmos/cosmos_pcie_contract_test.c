#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cosmos_hal.h"
#include "cosmos_pcie_regs.h"
#include "cosmos_zynq_regs.h"

int cosmos_platform_irq_handle(unsigned int interrupt_id);

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                     \
                    __FILE__, __LINE__, #condition);                          \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define TEST_LOG_CAPACITY 64U

enum snapshot_mode {
    SNAPSHOT_STABLE,
    SNAPSHOT_TORN_ONCE,
    SNAPSHOT_ALWAYS_TORN,
    SNAPSHOT_LINK_DOWN
};

struct mock_pcie {
    enum snapshot_mode mode;
    unsigned int snapshot;
    unsigned int field_reads[4];
    unsigned int irq_status;
    unsigned int irq_mask;
    unsigned int irq_clear;
    unsigned int queue_clears;
    unsigned int admin_clears;
    unsigned int nvme_clears;
    unsigned int require_unavailable_on_write;

    unsigned int command_word[4];
    unsigned int command_count;
    unsigned int command_read;
    unsigned int link_down_after_cmd_read;
    unsigned int sram[COSMOS_PCIE_NVME_CMD_SLOT_COUNT]
                     [COSMOS_PCIE_NVME_CMD_DWORDS];
    unsigned int sram_read_count;
    unsigned int sram_read_slot[TEST_LOG_CAPACITY];
    unsigned int sram_read_index[TEST_LOG_CAPACITY];

    unsigned int write_count;
    unsigned int write_offset[TEST_LOG_CAPACITY];
    unsigned int write_value[TEST_LOG_CAPACITY];
    unsigned int completion_write_count;
    unsigned int final_commit_writes;
    unsigned int link_down_after_completion_write;

    unsigned int dma_fifo_count;
    unsigned int dma_write_count;
    unsigned int dma_final_commit_writes;
    unsigned int link_down_after_dma_write;
};

static struct mock_pcie mock;

static void mock_reset(enum snapshot_mode mode) {
    memset(&mock, 0, sizeof(mock));
    mock.mode = mode;
}

static void mock_reset_transport_log(void) {
    mock.command_read = 0U;
    mock.sram_read_count = 0U;
    mock.write_count = 0U;
    mock.completion_write_count = 0U;
    mock.final_commit_writes = 0U;
    mock.link_down_after_cmd_read = 0U;
    mock.link_down_after_completion_write = 0U;
    mock.dma_write_count = 0U;
    mock.dma_final_commit_writes = 0U;
    mock.link_down_after_dma_write = 0U;
}

static void mock_fail(const char *message, unsigned int address) {
    fprintf(stderr, "mock PCIe MMIO failure: %s at 0x%08x\n",
            message, address);
    exit(2);
}

static unsigned int mock_stable_field(unsigned int field) {
    static const unsigned int stable[4] = {
        COSMOS_PCIE_STATUS_LINK_UP | COSMOS_PCIE_LTSSM_L0,
        COSMOS_PCIE_FUNCTION_BUS_MASTER |
            COSMOS_PCIE_FUNCTION_MSI_ENABLE |
            (COSMOS_PCIE_FUNCTION_MME_MAX <<
             COSMOS_PCIE_FUNCTION_MME_SHIFT),
        COSMOS_PCIE_NVME_CC_ENABLE | COSMOS_PCIE_NVME_CSTS_READY,
        COSMOS_PCIE_ADMIN_CQ_VALID |
            COSMOS_PCIE_ADMIN_SQ_VALID |
            COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE
    };

    return stable[field];
}

static unsigned int mock_snapshot_field(unsigned int field) {
    unsigned int value = mock_stable_field(field);

    if (mock.mode == SNAPSHOT_LINK_DOWN && field == 0U) {
        value = COSMOS_PCIE_LTSSM_L0 - 1U;
    } else if (field == 3U &&
               ((mock.mode == SNAPSHOT_TORN_ONCE && mock.snapshot == 1U) ||
                (mock.mode == SNAPSHOT_ALWAYS_TORN &&
                 (mock.snapshot & 1U) != 0U))) {
        value ^= COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE;
    }
    mock.field_reads[field]++;
    if (field == 3U) {
        mock.snapshot++;
    }
    return value;
}

static unsigned int mock_command_word(unsigned int queue_id,
                                      unsigned int slot_tag,
                                      unsigned int sequence) {
    return COSMOS_PCIE_NVME_CMD_VALID |
        (queue_id & COSMOS_PCIE_NVME_CMD_QUEUE_MASK) |
        ((slot_tag << COSMOS_PCIE_NVME_CMD_SLOT_SHIFT) &
         COSMOS_PCIE_NVME_CMD_SLOT_MASK) |
        ((sequence << COSMOS_PCIE_NVME_CMD_SEQ_SHIFT) &
         COSMOS_PCIE_NVME_CMD_SEQ_MASK);
}

static unsigned int mock_read_command_fifo(void) {
    unsigned int word;

    if (mock.command_read >= mock.command_count) {
        return 0U;
    }
    word = mock.command_word[mock.command_read++];
    if (mock.link_down_after_cmd_read != 0U &&
        mock.command_read == mock.link_down_after_cmd_read) {
        mock.mode = SNAPSHOT_LINK_DOWN;
    }
    return word;
}

static unsigned int mock_read_sram(unsigned int offset) {
    unsigned int slot = (offset - COSMOS_PCIE_NVME_CMD_SRAM_OFFSET) /
        COSMOS_PCIE_NVME_CMD_BYTES;
    unsigned int index = ((offset - COSMOS_PCIE_NVME_CMD_SRAM_OFFSET) %
        COSMOS_PCIE_NVME_CMD_BYTES) / 4U;

    if (slot >= COSMOS_PCIE_NVME_CMD_SLOT_COUNT ||
        index >= COSMOS_PCIE_NVME_CMD_DWORDS ||
        mock.sram_read_count >= TEST_LOG_CAPACITY) {
        mock_fail("invalid command SRAM read", COSMOS_PCIE_HOST_BASE + offset);
    }
    mock.sram_read_slot[mock.sram_read_count] = slot;
    mock.sram_read_index[mock.sram_read_count] = index;
    mock.sram_read_count++;
    return mock.sram[slot][index];
}

unsigned int cosmos_mmio_test_read32(unsigned int address) {
    unsigned int offset;

    if (address == COSMOS_ZYNQ_DEVCFG_BASE +
            COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET) {
        return COSMOS_ZYNQ_DEVCFG_PCFG_DONE;
    }
    if (address < COSMOS_PCIE_HOST_BASE ||
        address >= COSMOS_PCIE_HOST_BASE + COSMOS_PCIE_HOST_SPAN) {
        mock_fail("read outside controller", address);
        return 0U;
    }
    offset = address - COSMOS_PCIE_HOST_BASE;
    if (offset == COSMOS_PCIE_IRQ_STATUS_OFFSET) {
        return mock.irq_status;
    }
    if (offset == COSMOS_PCIE_STATUS_OFFSET) {
        return mock_snapshot_field(0U);
    }
    if (offset == COSMOS_PCIE_FUNCTION_OFFSET) {
        return mock_snapshot_field(1U);
    }
    if (offset == COSMOS_PCIE_NVME_STATUS_OFFSET) {
        return mock_snapshot_field(2U);
    }
    if (offset == COSMOS_PCIE_HOST_DMA_FIFO_COUNT_OFFSET) {
        return mock.dma_fifo_count;
    }
    if (offset == COSMOS_PCIE_ADMIN_QUEUE_OFFSET) {
        return mock_snapshot_field(3U);
    }
    if (offset == COSMOS_PCIE_NVME_CMD_FIFO_OFFSET) {
        return mock_read_command_fifo();
    }
    if (offset >= COSMOS_PCIE_NVME_CMD_SRAM_OFFSET &&
        offset < COSMOS_PCIE_NVME_CMD_SRAM_OFFSET +
            COSMOS_PCIE_NVME_CMD_SLOT_COUNT *
            COSMOS_PCIE_NVME_CMD_BYTES &&
        ((offset - COSMOS_PCIE_NVME_CMD_SRAM_OFFSET) & 3U) == 0U) {
        return mock_read_sram(offset);
    }
    mock_fail("unknown register read", address);
    return 0U;
}

static int mock_is_queue_control(unsigned int offset) {
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

static int mock_is_completion_write(unsigned int offset) {
    return offset == COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
            COSMOS_PCIE_NVME_CPL_WORD0_OFFSET ||
        offset == COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
            COSMOS_PCIE_NVME_CPL_WORD1_OFFSET ||
        offset == COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
            COSMOS_PCIE_NVME_CPL_WORD2_OFFSET;
}

static int mock_is_dma_write(unsigned int offset) {
    return offset == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
            COSMOS_PCIE_HOST_DMA_WORD0_OFFSET ||
        offset == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
            COSMOS_PCIE_HOST_DMA_WORD1_OFFSET ||
        offset == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
            COSMOS_PCIE_HOST_DMA_WORD2_OFFSET ||
        offset == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
            COSMOS_PCIE_HOST_DMA_WORD3_OFFSET;
}

static void mock_record_write(unsigned int offset, unsigned int value) {
    if (mock.write_count >= TEST_LOG_CAPACITY) {
        mock_fail("write log overflow", COSMOS_PCIE_HOST_BASE + offset);
    }
    mock.write_offset[mock.write_count] = offset;
    mock.write_value[mock.write_count] = value;
    mock.write_count++;
}

void cosmos_mmio_test_write32(unsigned int address, unsigned int value) {
    unsigned int offset;

    if (address < COSMOS_PCIE_HOST_BASE ||
        address >= COSMOS_PCIE_HOST_BASE + COSMOS_PCIE_HOST_SPAN) {
        mock_fail("write outside controller", address);
        return;
    }
    if (mock.require_unavailable_on_write &&
        cosmos_pcie_is_available()) {
        mock_fail("quiesce wrote while controller was available", address);
        return;
    }
    offset = address - COSMOS_PCIE_HOST_BASE;
    if (offset == COSMOS_PCIE_IRQ_MASK_OFFSET) {
        mock.irq_mask = value;
    } else if (offset == COSMOS_PCIE_IRQ_CLEAR_OFFSET) {
        mock.irq_clear |= value;
        mock.irq_status &= ~value;
    } else if (offset == COSMOS_PCIE_NVME_STATUS_OFFSET && value == 0U) {
        mock.nvme_clears++;
    } else if (offset == COSMOS_PCIE_ADMIN_QUEUE_OFFSET && value == 0U) {
        mock.admin_clears++;
    } else if (mock_is_queue_control(offset) && value == 0U) {
        mock.queue_clears++;
    } else if (mock_is_completion_write(offset)) {
        mock_record_write(offset, value);
        mock.completion_write_count++;
        if (offset == COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
                COSMOS_PCIE_NVME_CPL_WORD2_OFFSET) {
            mock.final_commit_writes++;
        }
        if (mock.link_down_after_completion_write != 0U &&
            mock.completion_write_count ==
                mock.link_down_after_completion_write) {
            mock.mode = SNAPSHOT_LINK_DOWN;
        }
    } else if (mock_is_dma_write(offset)) {
        mock_record_write(offset, value);
        mock.dma_write_count++;
        if (offset == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
                COSMOS_PCIE_HOST_DMA_WORD3_OFFSET) {
            mock.dma_final_commit_writes++;
        }
        if (mock.link_down_after_dma_write != 0U &&
            mock.dma_write_count == mock.link_down_after_dma_write) {
            mock.mode = SNAPSHOT_LINK_DOWN;
            mock.require_unavailable_on_write = 1U;
        }
    } else {
        mock_fail("unknown register write", address);
    }
}

static int init_stable(void) {
    mock_reset(SNAPSHOT_STABLE);
    CHECK(cosmos_pcie_init() == COSMOS_OK);
    CHECK(cosmos_pcie_is_available());
    CHECK(mock.irq_mask == COSMOS_PCIE_IRQ_DEFINED_MASK);
    CHECK(cosmos_platform_irq_handle(COSMOS_PCIE_PL_IRQ_ID) == COSMOS_OK);
    CHECK(cosmos_platform_irq_handle(COSMOS_PCIE_PL_IRQ_ID + 1U) ==
        COSMOS_UNAVAILABLE);
    return 0;
}

static int test_full_snapshot_stability(void) {
    unsigned int field;

    mock_reset(SNAPSHOT_TORN_ONCE);
    CHECK(cosmos_pcie_init() == COSMOS_OK);
    CHECK(cosmos_pcie_is_available());
    for (field = 0U; field < 4U; ++field) {
        CHECK(mock.field_reads[field] == 6U);
    }

    mock_reset(SNAPSHOT_ALWAYS_TORN);
    CHECK(cosmos_pcie_init() == COSMOS_TIMEOUT);
    CHECK(!cosmos_pcie_is_available());
    for (field = 0U; field < 4U; ++field) {
        CHECK(mock.field_reads[field] == 2U * COSMOS_POLL_LIMIT);
    }
    return 0;
}

static int test_link_loss_quiesces_before_clear(void) {
    CHECK(init_stable() == 0);
    mock.mode = SNAPSHOT_LINK_DOWN;
    mock.snapshot = 0U;
    memset(mock.field_reads, 0, sizeof(mock.field_reads));
    mock.irq_status = COSMOS_PCIE_IRQ_LINK_CHANGE;
    mock.irq_clear = 0U;
    mock.require_unavailable_on_write = 1U;

    CHECK(cosmos_platform_irq_handle(COSMOS_PCIE_PL_IRQ_ID) ==
        COSMOS_UNAVAILABLE);
    CHECK(!cosmos_pcie_is_available());
    CHECK(mock.irq_status == 0U);
    CHECK(mock.irq_clear == COSMOS_PCIE_IRQ_LINK_CHANGE);
    CHECK(mock.irq_mask == 0U);
    CHECK(mock.nvme_clears == 1U);
    CHECK(mock.admin_clears == 1U);
    CHECK(mock.queue_clears == 2U * COSMOS_PCIE_IO_QUEUE_COUNT);
    return 0;
}

static int test_fatal_and_unknown_irqs_fail_closed(void) {
    CHECK(init_stable() == 0);
    mock.irq_status =
        COSMOS_PCIE_IRQ_AXI_READ_ERROR | COSMOS_PCIE_IRQ_CPLD_ERROR;
    mock.irq_clear = 0U;
    mock.require_unavailable_on_write = 1U;
    CHECK(cosmos_pcie_service_irq() == COSMOS_HW_ERROR);
    CHECK(!cosmos_pcie_is_available());
    CHECK(mock.irq_status == 0U);
    CHECK(mock.irq_clear ==
        (COSMOS_PCIE_IRQ_AXI_READ_ERROR | COSMOS_PCIE_IRQ_CPLD_ERROR));
    CHECK(mock.queue_clears == 2U * COSMOS_PCIE_IO_QUEUE_COUNT);

    CHECK(init_stable() == 0);
    mock.irq_status = 1U << 31;
    mock.require_unavailable_on_write = 1U;
    CHECK(cosmos_pcie_service_irq() == COSMOS_HW_ERROR);
    CHECK(!cosmos_pcie_is_available());
    CHECK(mock.irq_mask == 0U);
    CHECK(mock.irq_clear == 0U);
    return 0;
}

static int test_command_fetch_empty_no_sram(void) {
    struct cosmos_pcie_nvme_command command;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_nvme_fetch_command(&command) == COSMOS_UNAVAILABLE);
    CHECK(mock.command_read == 0U);
    CHECK(mock.sram_read_count == 0U);
    CHECK(cosmos_pcie_is_available());
    return 0;
}

static int test_command_fetch_exact_metadata_and_sram(void) {
    struct cosmos_pcie_nvme_command command;
    unsigned int index;
    unsigned int slot = 0x2AU;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.command_word[0] = mock_command_word(3U, slot, 0x5CU);
    mock.command_count = 1U;
    for (index = 0U; index < COSMOS_PCIE_NVME_CMD_DWORDS; ++index) {
        mock.sram[slot][index] = 0xC0DE0000U | index;
    }

    CHECK(cosmos_pcie_nvme_fetch_command(&command) == COSMOS_OK);
    CHECK(command.queue_id == 3U);
    CHECK(command.slot_tag == slot);
    CHECK(command.sequence == 0x5CU);
    CHECK(mock.command_read == 1U);
    CHECK(mock.sram_read_count == COSMOS_PCIE_NVME_CMD_DWORDS);
    for (index = 0U; index < COSMOS_PCIE_NVME_CMD_DWORDS; ++index) {
        CHECK(command.raw_dword[index] == (0xC0DE0000U | index));
        CHECK(mock.sram_read_slot[index] == slot);
        CHECK(mock.sram_read_index[index] == index);
    }
    return 0;
}

static int test_command_fetch_rejects_malformed_before_sram(void) {
    struct cosmos_pcie_nvme_command command;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.command_word[0] = mock_command_word(9U, 0U, 0U);
    mock.command_count = 1U;
    mock.require_unavailable_on_write = 1U;
    CHECK(cosmos_pcie_nvme_fetch_command(&command) == COSMOS_HW_ERROR);
    CHECK(mock.sram_read_count == 0U);
    CHECK(!cosmos_pcie_is_available());

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.command_word[0] = mock_command_word(1U, 1U, 1U) | 0x10U;
    mock.command_count = 1U;
    mock.require_unavailable_on_write = 1U;
    CHECK(cosmos_pcie_nvme_fetch_command(&command) == COSMOS_HW_ERROR);
    CHECK(mock.sram_read_count == 0U);
    CHECK(!cosmos_pcie_is_available());
    return 0;
}

static int test_command_fetch_link_loss_cancels_before_sram(void) {
    struct cosmos_pcie_nvme_command command;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.command_word[0] = mock_command_word(1U, 7U, 2U);
    mock.command_count = 1U;
    mock.link_down_after_cmd_read = 1U;
    mock.require_unavailable_on_write = 1U;
    CHECK(cosmos_pcie_nvme_fetch_command(&command) == COSMOS_UNAVAILABLE);
    CHECK(mock.sram_read_count == 0U);
    CHECK(!cosmos_pcie_is_available());
    return 0;
}

static int test_completion_word_order_and_commit_boundary(void) {
    struct cosmos_pcie_nvme_completion completion;
    unsigned int status_word;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_nvme_status_word(2U, 0x81U, 1U, &status_word) ==
        COSMOS_OK);
    completion.queue_id = 3U;
    completion.slot_tag = 0x2AU;
    completion.sequence = 0x5CU;
    completion.cid = 0x1234U;
    completion.specific = 0xA5A50011U;
    completion.status_word = status_word;

    CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
        COSMOS_PCIE_NVME_COMPLETION_COMMITTED);
    CHECK(mock.write_count == 2U);
    CHECK(mock.write_offset[0] == COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
        COSMOS_PCIE_NVME_CPL_WORD1_OFFSET);
    CHECK(mock.write_offset[1] == COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
        COSMOS_PCIE_NVME_CPL_WORD2_OFFSET);
    CHECK(mock.write_value[0] == 0xA5A50011U);
    CHECK(mock.write_value[1] ==
          ((status_word << 16U) |
           (COSMOS_PCIE_NVME_CPL_TYPE_AUTO << 14U) | 0x2AU));
    CHECK(mock.final_commit_writes == 1U);
    return 0;
}

static int test_completion_rejects_malformed_without_writes(void) {
    struct cosmos_pcie_nvme_completion completion;
    unsigned int status_word;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_nvme_status_word(0U, 0U, 0U, &status_word) ==
        COSMOS_OK);
    completion.queue_id = COSMOS_PCIE_NVME_MAX_QUEUE_ID + 1U;
    completion.slot_tag = 1U;
    completion.sequence = 1U;
    completion.cid = 1U;
    completion.specific = 0U;
    completion.status_word = status_word;
    CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
        COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED);
    CHECK(mock.write_count == 0U);

    completion.queue_id = 1U;
    completion.slot_tag = COSMOS_PCIE_NVME_CMD_SLOT_COUNT;
    CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
        COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED);
    CHECK(mock.write_count == 0U);

    completion.slot_tag = 1U;
    completion.status_word = status_word | 1U;
    CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
        COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED);
    CHECK(mock.write_count == 0U);
    CHECK(cosmos_pcie_nvme_post_completion_fields(
        1U, 1U, 1U, 1U, 0U, 8U, 0U, 0U) ==
        COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED);
    CHECK(mock.write_count == 0U);
    return 0;
}

static int test_completion_publication_never_retries_after_word1(void) {
    struct cosmos_pcie_nvme_completion completion;
    unsigned int status_word;
    unsigned int changed_after;

    CHECK(cosmos_pcie_nvme_status_word(0U, 0U, 0U, &status_word) ==
        COSMOS_OK);
    completion.queue_id = 1U;
    completion.slot_tag = 2U;
    completion.sequence = 3U;
    completion.cid = 4U;
    completion.specific = 0U;
    completion.status_word = status_word;

    for (changed_after = 1U; changed_after <= 2U; ++changed_after) {
        CHECK(init_stable() == 0);
        mock_reset_transport_log();
        mock.link_down_after_completion_write = changed_after;

        CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
            COSMOS_PCIE_NVME_COMPLETION_COMMITTED);
        CHECK(mock.completion_write_count == 2U);
        CHECK(mock.final_commit_writes == 1U);
        CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
            COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED);
        CHECK(mock.completion_write_count == 2U);
        CHECK(mock.final_commit_writes == 1U);
    }
    return 0;
}

static int test_completion_readiness_failure_has_no_writes(void) {
    struct cosmos_pcie_nvme_completion completion;
    unsigned int status_word;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_nvme_status_word(0U, 0U, 0U, &status_word) ==
        COSMOS_OK);
    completion.queue_id = 1U;
    completion.slot_tag = 2U;
    completion.sequence = 3U;
    completion.cid = 4U;
    completion.specific = 0U;
    completion.status_word = status_word;
    mock.mode = SNAPSHOT_LINK_DOWN;

    CHECK(cosmos_pcie_nvme_post_completion(&completion) ==
        COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED);
    CHECK(mock.completion_write_count == 0U);
    CHECK(mock.final_commit_writes == 0U);
    return 0;
}

static int test_direct_dma_exact_order_completion_and_full_gate(void) {
    unsigned int device_address = COSMOS_NFC_DATA_POOL_BASE + 0x1000U;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        device_address, 0x5U, 0x23456000U, 0x1000U) == COSMOS_OK);
    CHECK(mock.dma_write_count == 4U);
    CHECK(mock.dma_final_commit_writes == 1U);
    CHECK(mock.write_offset[0] == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
        COSMOS_PCIE_HOST_DMA_WORD0_OFFSET);
    CHECK(mock.write_offset[1] == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
        COSMOS_PCIE_HOST_DMA_WORD1_OFFSET);
    CHECK(mock.write_offset[2] == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
        COSMOS_PCIE_HOST_DMA_WORD2_OFFSET);
    CHECK(mock.write_offset[3] == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
        COSMOS_PCIE_HOST_DMA_WORD3_OFFSET);
    CHECK(mock.write_value[0] == device_address);
    CHECK(mock.write_value[1] == 0x5U);
    CHECK(mock.write_value[2] == 0x23456000U);
    CHECK(mock.write_value[3] == 0x80001000U);

    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        device_address, 0x5U, 0x23457000U, 0x1000U) == COSMOS_UNAVAILABLE);
    CHECK(mock.dma_write_count == 4U);
    mock.dma_fifo_count = 1U;
    CHECK(cosmos_pcie_host_dma_poll_direct(COSMOS_PCIE_HOST_TO_DEVICE) ==
        COSMOS_OK);
    CHECK(cosmos_pcie_host_dma_poll_direct(COSMOS_PCIE_HOST_TO_DEVICE) ==
        COSMOS_INVALID);
    return 0;
}

static int test_direct_dma_device_to_host_and_64bit_range(void) {
    unsigned int device_address = COSMOS_NFC_DATA_POOL_BASE + 0x2000U;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.dma_fifo_count = 0x00000100U;
    CHECK(cosmos_pcie_host_dma_submit_device_to_host(
        device_address, 0xEU, 0xF0000000U, 0x0200U) == COSMOS_OK);
    CHECK(mock.dma_write_count == 4U);
    CHECK(mock.dma_final_commit_writes == 1U);
    CHECK(mock.write_value[0] == device_address);
    CHECK(mock.write_value[1] == 0xEU);
    CHECK(mock.write_value[2] == 0xF0000000U);
    CHECK(mock.write_value[3] == 0xC0000200U);
    mock.dma_fifo_count = 0x00000200U;
    CHECK(cosmos_pcie_host_dma_poll_direct(COSMOS_PCIE_DEVICE_TO_HOST) ==
        COSMOS_OK);
    return 0;
}

static int test_direct_dma_rejects_bad_span_without_writes(void) {
    unsigned int valid_device = COSMOS_NFC_DATA_POOL_BASE;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device + 2U, 0U, 0x1000U, 4U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device, 0U, 0x1004U, 4U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device, 0U, 0x1000U, 0U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device, 0U, 0x1000U, 2U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device, 0U, 0x1000U, 0x1004U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device, 0x10U, 0x1000U, 4U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        valid_device, 0xFU, 0xFFFFFFF0U, 0x20U) == COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        COSMOS_NFC_DATA_POOL_END - 3U, 0U, 0x1000U, 8U) == COSMOS_INVALID);
    CHECK(mock.dma_write_count == 0U);
    return 0;
}

static int test_auto_dma_exact_words_and_completion_count(void) {
    unsigned int device_address = COSMOS_NFC_DATA_POOL_BASE + 0x3000U;
    unsigned int expected_auto_rx_word3 = (0x2AU <<
        COSMOS_PCIE_HOST_DMA_SLOT_SHIFT) | (0x55U <<
        COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_SHIFT);
    unsigned int expected_auto_tx_word3 = 0x40000000U | (0x2BU <<
        COSMOS_PCIE_HOST_DMA_SLOT_SHIFT) | (0x56U <<
        COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_SHIFT);

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    CHECK(cosmos_pcie_host_dma_submit_auto_host_to_device(
        0x2AU, 0x55U, device_address) == COSMOS_OK);
    CHECK(mock.dma_write_count == 2U);
    CHECK(mock.dma_final_commit_writes == 1U);
    CHECK(mock.write_offset[0] == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
        COSMOS_PCIE_HOST_DMA_WORD0_OFFSET);
    CHECK(mock.write_offset[1] == COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
        COSMOS_PCIE_HOST_DMA_WORD3_OFFSET);
    CHECK(mock.write_value[0] == device_address);
    CHECK(mock.write_value[1] == expected_auto_rx_word3);
    mock.dma_fifo_count = 0x00010000U;
    CHECK(cosmos_pcie_host_dma_poll_auto(COSMOS_PCIE_HOST_TO_DEVICE) ==
        COSMOS_OK);

    mock_reset_transport_log();
    mock.dma_fifo_count = 0x05010000U;
    CHECK(cosmos_pcie_host_dma_submit_auto_device_to_host(
        0x2BU, 0x56U, device_address + 0x1000U) == COSMOS_OK);
    CHECK(mock.dma_write_count == 2U);
    CHECK(mock.dma_final_commit_writes == 1U);
    CHECK(mock.write_value[0] == device_address + 0x1000U);
    CHECK(mock.write_value[1] == expected_auto_tx_word3);
    mock.dma_fifo_count = 0x06010000U;
    CHECK(cosmos_pcie_host_dma_poll_auto(COSMOS_PCIE_DEVICE_TO_HOST) ==
        COSMOS_OK);
    CHECK(cosmos_pcie_host_dma_submit_auto_host_to_device(
        COSMOS_PCIE_HOST_DMA_SLOT_MASK + 1U, 0U, device_address) ==
        COSMOS_INVALID);
    CHECK(cosmos_pcie_host_dma_submit_auto_host_to_device(
        0U, COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX + 1U, device_address) ==
        COSMOS_INVALID);
    CHECK(mock.dma_write_count == 2U);
    return 0;
}

static int test_dma_link_loss_before_and_after_commit(void) {
    unsigned int device_address = COSMOS_NFC_DATA_POOL_BASE + 0x4000U;

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.link_down_after_dma_write = 1U;
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        device_address, 0U, 0x1000U, 0x1000U) == COSMOS_UNAVAILABLE);
    CHECK(mock.dma_write_count == 1U);
    CHECK(mock.dma_final_commit_writes == 0U);
    CHECK(!cosmos_pcie_is_available());

    CHECK(init_stable() == 0);
    mock_reset_transport_log();
    mock.link_down_after_dma_write = 4U;
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        device_address, 0U, 0x2000U, 0x1000U) == COSMOS_OK);
    CHECK(mock.dma_write_count == 4U);
    CHECK(mock.dma_final_commit_writes == 1U);
    CHECK(cosmos_pcie_host_dma_submit_host_to_device(
        device_address, 0U, 0x3000U, 0x1000U) == COSMOS_UNAVAILABLE);
    CHECK(mock.dma_write_count == 4U);
    CHECK(!cosmos_pcie_is_available());
    return 0;
}

int main(void) {
#ifdef COSMOS_PCIE_AUTO_COMPLETION_ONLY
    CHECK(test_completion_word_order_and_commit_boundary() == 0);
    CHECK(test_completion_publication_never_retries_after_word1() == 0);
    puts("cosmos PCIe AUTO completion contract: PASS");
#else
    CHECK(test_full_snapshot_stability() == 0);
    CHECK(test_link_loss_quiesces_before_clear() == 0);
    CHECK(test_fatal_and_unknown_irqs_fail_closed() == 0);
    CHECK(test_command_fetch_empty_no_sram() == 0);
    CHECK(test_command_fetch_exact_metadata_and_sram() == 0);
    CHECK(test_command_fetch_rejects_malformed_before_sram() == 0);
    CHECK(test_command_fetch_link_loss_cancels_before_sram() == 0);
    CHECK(test_completion_word_order_and_commit_boundary() == 0);
    CHECK(test_completion_rejects_malformed_without_writes() == 0);
    CHECK(test_completion_publication_never_retries_after_word1() == 0);
    CHECK(test_completion_readiness_failure_has_no_writes() == 0);
    CHECK(test_direct_dma_exact_order_completion_and_full_gate() == 0);
    CHECK(test_direct_dma_device_to_host_and_64bit_range() == 0);
    CHECK(test_direct_dma_rejects_bad_span_without_writes() == 0);
    CHECK(test_auto_dma_exact_words_and_completion_count() == 0);
    CHECK(test_dma_link_loss_before_and_after_commit() == 0);
    puts("cosmos PCIe contract: PASS");
#endif
    return 0;
}
