/* Cosmos+ OpenSSD NVMeHostController endpoint readiness gate. */
#include "cosmos_hal.h"
#include "cosmos_pcie_regs.h"
#include "cosmos_profile_openssd2_8ch8way_v300.h"
#include "cosmos_zynq_regs.h"

#if defined(COSMOS_PCIE_BITSTREAM_CONTRACT)
#if COSMOS_PCIE_BITSTREAM_CONTRACT != COSMOS_PCIE_CONTRACT_8CH8WAY_V300
#error "Unsupported Cosmos+ PCIe bitstream contract"
#endif
#define COSMOS_PCIE_CONTRACT_BOUND 1
#else
#define COSMOS_PCIE_CONTRACT_BOUND 0
#endif

_Static_assert(COSMOS_PCIE_HOST_BASE == COSMOS_PCIE_BASE,
               "PCIe MMU and controller apertures must match");

struct cosmos_pcie_snapshot {
    unsigned int status;
    unsigned int function;
    unsigned int nvme;
    unsigned int admin;
};

static volatile unsigned int cosmos_pcie_available;
static unsigned int cosmos_pcie_host_dma_expected[4];
static unsigned int cosmos_pcie_host_dma_pending;

__attribute__((weak))
int cosmos_gic_enable_pcie_irq(void) {
#if defined(COSMOS_MMIO_TEST)
    return COSMOS_OK;
#else
    return COSMOS_UNAVAILABLE;
#endif
}

int cosmos_platform_irq_handle(unsigned int interrupt_id) {
    return interrupt_id == COSMOS_PCIE_PL_IRQ_ID
        ? cosmos_pcie_service_irq()
        : COSMOS_UNAVAILABLE;
}

static int cosmos_pcie_snapshot_status(unsigned int status,
                                       unsigned int function,
                                       unsigned int nvme,
                                       unsigned int admin) {
    unsigned int admin_valid =
        admin & (COSMOS_PCIE_ADMIN_CQ_VALID | COSMOS_PCIE_ADMIN_SQ_VALID);

    if ((status & ~COSMOS_PCIE_STATUS_DEFINED_MASK) != 0U ||
        (function & ~COSMOS_PCIE_FUNCTION_DEFINED_MASK) != 0U ||
        (nvme & ~COSMOS_PCIE_NVME_STATUS_DEFINED_MASK) != 0U ||
        (admin & ~COSMOS_PCIE_ADMIN_DEFINED_MASK) != 0U) {
        return COSMOS_HW_ERROR;
    }
    if ((status & COSMOS_PCIE_STATUS_LINK_UP) == 0U ||
        (status & COSMOS_PCIE_STATUS_LTSSM_MASK) != COSMOS_PCIE_LTSSM_L0 ||
        (function & COSMOS_PCIE_FUNCTION_BUS_MASTER) == 0U ||
        (function & COSMOS_PCIE_FUNCTION_MSI_ENABLE) == 0U) {
        return COSMOS_UNAVAILABLE;
    }
    if ((function & COSMOS_PCIE_FUNCTION_MSIX_ENABLE) != 0U ||
        ((function & COSMOS_PCIE_FUNCTION_MME_MASK) >>
         COSMOS_PCIE_FUNCTION_MME_SHIFT) > COSMOS_PCIE_FUNCTION_MME_MAX) {
        return COSMOS_HW_ERROR;
    }
    if (admin_valid != 0U &&
        admin_valid !=
            (COSMOS_PCIE_ADMIN_CQ_VALID | COSMOS_PCIE_ADMIN_SQ_VALID)) {
        return COSMOS_HW_ERROR;
    }
    if ((admin & COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE) != 0U &&
        (admin & COSMOS_PCIE_ADMIN_CQ_VALID) == 0U) {
        return COSMOS_HW_ERROR;
    }
    if ((nvme & COSMOS_PCIE_NVME_CC_ENABLE) == 0U &&
        ((nvme & (COSMOS_PCIE_NVME_CC_SHN_MASK |
                  COSMOS_PCIE_NVME_CSTS_READY |
                  COSMOS_PCIE_NVME_CSTS_SHST_MASK)) != 0U ||
         admin != 0U)) {
        return COSMOS_HW_ERROR;
    }
    if ((nvme & COSMOS_PCIE_NVME_CSTS_READY) != 0U &&
        (admin & (COSMOS_PCIE_ADMIN_CQ_VALID |
                  COSMOS_PCIE_ADMIN_SQ_VALID |
                  COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE)) !=
            (COSMOS_PCIE_ADMIN_CQ_VALID |
             COSMOS_PCIE_ADMIN_SQ_VALID |
             COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE)) {
        return COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}

#if !COSMOS_IS_QEMU && COSMOS_PCIE_CONTRACT_BOUND
static unsigned int cosmos_pcie_read(unsigned int offset) {
    return cosmos_mmio_read32(COSMOS_PCIE_HOST_BASE + offset);
}

static void cosmos_pcie_write(unsigned int offset, unsigned int value) {
    cosmos_mmio_write32(COSMOS_PCIE_HOST_BASE + offset, value);
}

static void cosmos_pcie_read_snapshot(struct cosmos_pcie_snapshot *snapshot) {
    snapshot->status = cosmos_pcie_read(COSMOS_PCIE_STATUS_OFFSET);
    snapshot->function = cosmos_pcie_read(COSMOS_PCIE_FUNCTION_OFFSET);
    snapshot->nvme = cosmos_pcie_read(COSMOS_PCIE_NVME_STATUS_OFFSET);
    snapshot->admin = cosmos_pcie_read(COSMOS_PCIE_ADMIN_QUEUE_OFFSET);
}

static int cosmos_pcie_snapshots_equal(
    const struct cosmos_pcie_snapshot *left,
    const struct cosmos_pcie_snapshot *right) {
    return left->status == right->status &&
        left->function == right->function &&
        left->nvme == right->nvme &&
        left->admin == right->admin;
}

static int cosmos_pcie_poll_snapshot(struct cosmos_pcie_snapshot *snapshot,
                                      int wait_until_ready) {
    unsigned int poll;

    for (poll = 0U; poll < COSMOS_POLL_LIMIT; ++poll) {
        struct cosmos_pcie_snapshot first;
        struct cosmos_pcie_snapshot second;
        int result;

        cosmos_pcie_read_snapshot(&first);
        cosmos_data_sync_barrier();
        cosmos_pcie_read_snapshot(&second);
        if (!cosmos_pcie_snapshots_equal(&first, &second)) {
            continue;
        }
        result = cosmos_pcie_snapshot_status(
            second.status, second.function, second.nvme, second.admin);
        if (wait_until_ready && result == COSMOS_UNAVAILABLE) {
            continue;
        }
        *snapshot = second;
        return result;
    }
    return COSMOS_TIMEOUT;
}

static void cosmos_pcie_quiesce(void);

static int cosmos_pcie_require_transport_ready(void) {
    struct cosmos_pcie_snapshot snapshot;
    int result;

    if (!cosmos_pcie_is_available()) {
        return COSMOS_UNAVAILABLE;
    }
    result = cosmos_pcie_poll_snapshot(&snapshot, 0);
    if (result != COSMOS_OK) {
        cosmos_pcie_quiesce();
    }
    return result;
}

static int cosmos_pcie_nvme_cmd_word_valid(unsigned int word) {
    unsigned int queue_id;
    unsigned int slot_tag;

    if ((word & COSMOS_PCIE_NVME_CMD_VALID) == 0U) {
        return COSMOS_UNAVAILABLE;
    }
    if ((word & COSMOS_PCIE_NVME_CMD_RESERVED_MASK) != 0U) {
        return COSMOS_HW_ERROR;
    }
    queue_id = word & COSMOS_PCIE_NVME_CMD_QUEUE_MASK;
    slot_tag = (word & COSMOS_PCIE_NVME_CMD_SLOT_MASK) >>
        COSMOS_PCIE_NVME_CMD_SLOT_SHIFT;
    if (queue_id > COSMOS_PCIE_NVME_MAX_QUEUE_ID ||
        slot_tag >= COSMOS_PCIE_NVME_CMD_SLOT_COUNT) {
        return COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}

static int cosmos_pcie_nvme_completion_valid(
    const struct cosmos_pcie_nvme_completion *completion) {
    if (completion == 0 ||
        completion->queue_id > COSMOS_PCIE_NVME_MAX_QUEUE_ID ||
        completion->slot_tag >= COSMOS_PCIE_NVME_CMD_SLOT_COUNT ||
        completion->sequence > 0xFFU ||
        completion->cid > 0xFFFFU ||
        completion->status_word > 0xFFFFU ||
        (completion->status_word &
         COSMOS_PCIE_NVME_CPL_STATUS_RESERVED_MASK) != 0U) {
        return 0;
    }
    return 1;
}

static void cosmos_pcie_quiesce(void) {
    unsigned int queue;

    cosmos_pcie_available = 0U;
    cosmos_pcie_host_dma_pending = 0U;
    cosmos_data_sync_barrier();
    cosmos_pcie_write(COSMOS_PCIE_IRQ_MASK_OFFSET, 0U);
    cosmos_pcie_write(COSMOS_PCIE_NVME_STATUS_OFFSET, 0U);
    cosmos_pcie_write(COSMOS_PCIE_ADMIN_QUEUE_OFFSET, 0U);
    for (queue = 0U; queue < COSMOS_PCIE_IO_QUEUE_COUNT; ++queue) {
        unsigned int queue_offset =
            queue * COSMOS_PCIE_IO_QUEUE_STRIDE +
            COSMOS_PCIE_IO_QUEUE_CONTROL_WORD;

        cosmos_pcie_write(COSMOS_PCIE_IO_SQ_OFFSET + queue_offset, 0U);
        cosmos_pcie_write(COSMOS_PCIE_IO_CQ_OFFSET + queue_offset, 0U);
    }
    cosmos_data_sync_barrier();
}

static int cosmos_pcie_probe(void) {
    struct cosmos_pcie_snapshot snapshot;
    unsigned int devcfg_int_sts =
        cosmos_mmio_read32(COSMOS_ZYNQ_DEVCFG_BASE +
                           COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET);
    unsigned int pending;
    int result;

    if (!cosmos_zynq_pcfg_done(devcfg_int_sts)) {
        return COSMOS_UNAVAILABLE;
    }
    result = cosmos_pcie_poll_snapshot(&snapshot, 1);
    if (result != COSMOS_OK) {
        return result;
    }
    pending = cosmos_pcie_read(COSMOS_PCIE_IRQ_STATUS_OFFSET);
    if ((pending & ~COSMOS_PCIE_IRQ_DEFINED_MASK) != 0U ||
        (pending & COSMOS_PCIE_IRQ_FATAL_MASK) != 0U) {
        cosmos_pcie_quiesce();
        cosmos_pcie_write(COSMOS_PCIE_IRQ_CLEAR_OFFSET,
                          pending & COSMOS_PCIE_IRQ_DEFINED_MASK);
        return COSMOS_HW_ERROR;
    }
    cosmos_pcie_write(COSMOS_PCIE_IRQ_CLEAR_OFFSET, pending);
    cosmos_pcie_write(COSMOS_PCIE_IRQ_MASK_OFFSET,
                      COSMOS_PCIE_IRQ_DEFINED_MASK);
    cosmos_data_sync_barrier();
    cosmos_pcie_available = 1U;
    cosmos_data_sync_barrier();

    result = cosmos_pcie_poll_snapshot(&snapshot, 0);
    if (result != COSMOS_OK) {
        cosmos_pcie_quiesce();
        return result;
    }
    pending = cosmos_pcie_read(COSMOS_PCIE_IRQ_STATUS_OFFSET);
    if (pending != 0U) {
        result = cosmos_pcie_service_irq();
        if (result != COSMOS_OK) {
            return result;
        }
    }
    result = cosmos_gic_enable_pcie_irq();
    if (result != COSMOS_OK) {
        cosmos_pcie_quiesce();
    }
    return result;
}

static int cosmos_pcie_host_dma_device_buffer_valid(
    unsigned int device_address, unsigned int length) {
    if ((device_address & (COSMOS_PCIE_HOST_DMA_DEVICE_ALIGNMENT - 1U)) !=
            0U ||
        length == 0U || length > COSMOS_PCIE_HOST_DMA_MAX_BYTES ||
        (length & (COSMOS_PCIE_HOST_DMA_DEVICE_ALIGNMENT - 1U)) != 0U ||
        device_address < COSMOS_NFC_DATA_POOL_BASE ||
        device_address > COSMOS_NFC_DATA_POOL_END ||
        length - 1U > COSMOS_NFC_DATA_POOL_END - device_address) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}

static int cosmos_pcie_host_dma_direct_valid(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length) {
    unsigned int last_host_address_low;

    if (cosmos_pcie_host_dma_device_buffer_valid(device_address, length) !=
            COSMOS_OK ||
        (host_address_low & (COSMOS_PCIE_HOST_DMA_HOST_ALIGNMENT - 1U)) !=
            0U ||
        host_address_high > COSMOS_PCIE_HOST_DMA_HOST_HIGH_MASK) {
        return COSMOS_INVALID;
    }
    last_host_address_low = host_address_low + length - 1U;
    if (last_host_address_low < host_address_low &&
        host_address_high == COSMOS_PCIE_HOST_DMA_HOST_HIGH_MASK) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}

static unsigned int cosmos_pcie_host_dma_counter_shift(
    unsigned int direct, enum cosmos_pcie_host_dma_direction direction) {
    if (direct != 0U) {
        return direction == COSMOS_PCIE_HOST_TO_DEVICE
            ? COSMOS_PCIE_HOST_DMA_DIRECT_RX_COUNT_SHIFT
            : COSMOS_PCIE_HOST_DMA_DIRECT_TX_COUNT_SHIFT;
    }
    return direction == COSMOS_PCIE_HOST_TO_DEVICE
        ? COSMOS_PCIE_HOST_DMA_AUTO_RX_COUNT_SHIFT
        : COSMOS_PCIE_HOST_DMA_AUTO_TX_COUNT_SHIFT;
}

static unsigned int cosmos_pcie_host_dma_counter_index(
    unsigned int direct, enum cosmos_pcie_host_dma_direction direction) {
    return cosmos_pcie_host_dma_counter_shift(direct, direction) / 8U;
}

static unsigned int cosmos_pcie_host_dma_count(unsigned int counter_shift) {
    unsigned int count = cosmos_pcie_read(COSMOS_PCIE_HOST_DMA_FIFO_COUNT_OFFSET);

    cosmos_data_sync_barrier();
    return (count >> counter_shift) & COSMOS_PCIE_HOST_DMA_COUNT_MASK;
}

static int cosmos_pcie_host_dma_before_submit(unsigned int counter_shift,
                                               unsigned int *completed) {
    unsigned int index = counter_shift / 8U;
    unsigned int bit = 1U << index;
    unsigned int count = cosmos_pcie_host_dma_count(counter_shift);

    if ((cosmos_pcie_host_dma_pending & bit) != 0U) {
        if (count != cosmos_pcie_host_dma_expected[index]) {
            return COSMOS_UNAVAILABLE;
        }
        cosmos_pcie_host_dma_pending &= ~bit;
    }
    *completed = count;
    return COSMOS_OK;
}

static void cosmos_pcie_host_dma_commit(unsigned int counter_shift,
                                        unsigned int completed) {
    unsigned int index = counter_shift / 8U;

    cosmos_pcie_host_dma_expected[index] =
        (completed + 1U) & COSMOS_PCIE_HOST_DMA_COUNT_MASK;
    cosmos_pcie_host_dma_pending |= 1U << index;
    cosmos_data_sync_barrier();
}

static int cosmos_pcie_host_dma_write_word(unsigned int word_offset,
                                            unsigned int value) {
    int result;

    cosmos_pcie_write(COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET + word_offset,
                      value);
    cosmos_data_sync_barrier();
    result = cosmos_pcie_require_transport_ready();
    return result;
}

static int cosmos_pcie_host_dma_submit_direct(
    enum cosmos_pcie_host_dma_direction direction,
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length) {
    unsigned int counter_shift;
    unsigned int completed;
    unsigned int word3;
    int result;

    if (cosmos_pcie_host_dma_direct_valid(device_address, host_address_high,
                                          host_address_low, length) !=
        COSMOS_OK) {
        return COSMOS_INVALID;
    }
    result = cosmos_pcie_require_transport_ready();
    if (result != COSMOS_OK) {
        return result;
    }
    counter_shift = cosmos_pcie_host_dma_counter_shift(1U, direction);
    result = cosmos_pcie_host_dma_before_submit(counter_shift, &completed);
    if (result != COSMOS_OK) {
        return result;
    }

    word3 = (COSMOS_PCIE_HOST_DMA_TYPE_DIRECT <<
             COSMOS_PCIE_HOST_DMA_TYPE_SHIFT) |
        ((unsigned int)direction << COSMOS_PCIE_HOST_DMA_DIRECTION_SHIFT) |
        length;
    result = cosmos_pcie_host_dma_write_word(
        COSMOS_PCIE_HOST_DMA_WORD0_OFFSET, device_address);
    if (result != COSMOS_OK) {
        return result;
    }
    result = cosmos_pcie_host_dma_write_word(
        COSMOS_PCIE_HOST_DMA_WORD1_OFFSET, host_address_high);
    if (result != COSMOS_OK) {
        return result;
    }
    result = cosmos_pcie_host_dma_write_word(
        COSMOS_PCIE_HOST_DMA_WORD2_OFFSET, host_address_low);
    if (result != COSMOS_OK) {
        return result;
    }

    /* +12 is the RTL FIFO enqueue edge. Do not read status or retry after it. */
    cosmos_pcie_write(COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
                      COSMOS_PCIE_HOST_DMA_WORD3_OFFSET, word3);
    cosmos_data_sync_barrier();
    cosmos_pcie_host_dma_commit(counter_shift, completed);
    return COSMOS_OK;
}

static int cosmos_pcie_host_dma_submit_auto(
    enum cosmos_pcie_host_dma_direction direction,
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address) {
    unsigned int counter_shift;
    unsigned int completed;
    unsigned int word3;
    int result;

    if (command_slot_tag > COSMOS_PCIE_HOST_DMA_SLOT_MASK ||
        command_4k_offset > COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX ||
        cosmos_pcie_host_dma_device_buffer_valid(
            device_address, COSMOS_PCIE_HOST_DMA_MAX_BYTES) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    result = cosmos_pcie_require_transport_ready();
    if (result != COSMOS_OK) {
        return result;
    }
    counter_shift = cosmos_pcie_host_dma_counter_shift(0U, direction);
    result = cosmos_pcie_host_dma_before_submit(counter_shift, &completed);
    if (result != COSMOS_OK) {
        return result;
    }

    word3 = ((unsigned int)direction <<
             COSMOS_PCIE_HOST_DMA_DIRECTION_SHIFT) |
        (command_slot_tag << COSMOS_PCIE_HOST_DMA_SLOT_SHIFT) |
        (command_4k_offset << COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_SHIFT);
    result = cosmos_pcie_host_dma_write_word(
        COSMOS_PCIE_HOST_DMA_WORD0_OFFSET, device_address);
    if (result != COSMOS_OK) {
        return result;
    }

    /* host_lld.c writes only words 0 and 3 for AUTO; +12 commits it. */
    cosmos_pcie_write(COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET +
                      COSMOS_PCIE_HOST_DMA_WORD3_OFFSET, word3);
    cosmos_data_sync_barrier();
    cosmos_pcie_host_dma_commit(counter_shift, completed);
    return COSMOS_OK;
}

static int cosmos_pcie_host_dma_poll(unsigned int direct,
                                     enum cosmos_pcie_host_dma_direction direction) {
    unsigned int counter_shift;
    unsigned int index;
    unsigned int bit;
    unsigned int poll;

    counter_shift = cosmos_pcie_host_dma_counter_shift(direct, direction);
    index = cosmos_pcie_host_dma_counter_index(direct, direction);
    bit = 1U << index;
    if ((cosmos_pcie_host_dma_pending & bit) == 0U) {
        return COSMOS_INVALID;
    }
    for (poll = 0U; poll < COSMOS_POLL_LIMIT; ++poll) {
        int result = cosmos_pcie_require_transport_ready();

        if (result != COSMOS_OK) {
            return result;
        }
        if (cosmos_pcie_host_dma_count(counter_shift) ==
            cosmos_pcie_host_dma_expected[index]) {
            cosmos_pcie_host_dma_pending &= ~bit;
            cosmos_data_sync_barrier();
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}
#endif

int cosmos_pcie_nvme_status_word(unsigned int sct, unsigned int sc,
                                 unsigned int dnr,
                                 unsigned int *status_word) {
    if (status_word == 0 || sct > 7U || sc > 0xFFU || dnr > 1U) {
        return COSMOS_INVALID;
    }
    *status_word =
        (sc << COSMOS_PCIE_NVME_CPL_STATUS_SC_SHIFT) |
        (sct << COSMOS_PCIE_NVME_CPL_STATUS_SCT_SHIFT) |
        (dnr ? COSMOS_PCIE_NVME_CPL_STATUS_DNR : 0U);
    return COSMOS_OK;
}

int cosmos_pcie_host_dma_submit_host_to_device(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)device_address;
    (void)host_address_high;
    (void)host_address_low;
    (void)length;
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_pcie_host_dma_submit_direct(COSMOS_PCIE_HOST_TO_DEVICE,
        device_address, host_address_high, host_address_low, length);
#endif
}

int cosmos_pcie_host_dma_submit_device_to_host(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)device_address;
    (void)host_address_high;
    (void)host_address_low;
    (void)length;
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_pcie_host_dma_submit_direct(COSMOS_PCIE_DEVICE_TO_HOST,
        device_address, host_address_high, host_address_low, length);
#endif
}

int cosmos_pcie_host_dma_poll_direct(
    enum cosmos_pcie_host_dma_direction direction) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)direction;
    return COSMOS_UNAVAILABLE;
#else
    if (direction != COSMOS_PCIE_HOST_TO_DEVICE &&
        direction != COSMOS_PCIE_DEVICE_TO_HOST) {
        return COSMOS_INVALID;
    }
    return cosmos_pcie_host_dma_poll(1U, direction);
#endif
}

int cosmos_pcie_host_dma_submit_auto_host_to_device(
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)command_slot_tag;
    (void)command_4k_offset;
    (void)device_address;
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_pcie_host_dma_submit_auto(COSMOS_PCIE_HOST_TO_DEVICE,
        command_slot_tag, command_4k_offset, device_address);
#endif
}

int cosmos_pcie_host_dma_submit_auto_device_to_host(
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)command_slot_tag;
    (void)command_4k_offset;
    (void)device_address;
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_pcie_host_dma_submit_auto(COSMOS_PCIE_DEVICE_TO_HOST,
        command_slot_tag, command_4k_offset, device_address);
#endif
}

int cosmos_pcie_host_dma_poll_auto(
    enum cosmos_pcie_host_dma_direction direction) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)direction;
    return COSMOS_UNAVAILABLE;
#else
    if (direction != COSMOS_PCIE_HOST_TO_DEVICE &&
        direction != COSMOS_PCIE_DEVICE_TO_HOST) {
        return COSMOS_INVALID;
    }
    return cosmos_pcie_host_dma_poll(0U, direction);
#endif
}

int cosmos_pcie_nvme_fetch_command(struct cosmos_pcie_nvme_command *command) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)command;
    return COSMOS_UNAVAILABLE;
#else
    struct cosmos_pcie_nvme_command local;
    unsigned int word;
    unsigned int index;
    int result;

    if (command == 0) {
        return COSMOS_INVALID;
    }

    result = cosmos_pcie_require_transport_ready();
    if (result != COSMOS_OK) {
        return result;
    }

    word = cosmos_pcie_read(COSMOS_PCIE_NVME_CMD_FIFO_OFFSET);
    cosmos_data_sync_barrier();
    result = cosmos_pcie_nvme_cmd_word_valid(word);
    if (result != COSMOS_OK) {
        if (result == COSMOS_HW_ERROR) {
            cosmos_pcie_quiesce();
        }
        return result;
    }

    local.queue_id = word & COSMOS_PCIE_NVME_CMD_QUEUE_MASK;
    local.slot_tag = (word & COSMOS_PCIE_NVME_CMD_SLOT_MASK) >>
        COSMOS_PCIE_NVME_CMD_SLOT_SHIFT;
    local.sequence = (word & COSMOS_PCIE_NVME_CMD_SEQ_MASK) >>
        COSMOS_PCIE_NVME_CMD_SEQ_SHIFT;

    result = cosmos_pcie_require_transport_ready();
    if (result != COSMOS_OK) {
        return result;
    }
    for (index = 0U; index < COSMOS_PCIE_NVME_CMD_DWORDS; ++index) {
        unsigned int offset =
            COSMOS_PCIE_NVME_CMD_SRAM_OFFSET +
            local.slot_tag * COSMOS_PCIE_NVME_CMD_BYTES +
            index * 4U;

        local.raw_dword[index] = cosmos_pcie_read(offset);
    }
    cosmos_data_sync_barrier();

    result = cosmos_pcie_require_transport_ready();
    if (result != COSMOS_OK) {
        return result;
    }
    *command = local;
    return COSMOS_OK;
#endif
}

static int cosmos_pcie_nvme_queue_base_valid(
    unsigned int valid, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    if (valid > 1U) {
        return 0;
    }
    if (valid == 0U) {
        return entries == 0U && address_low == 0U && address_high == 0U;
    }
    return entries != 0U && entries <= 256U &&
        (address_low & 0xFFFU) == 0U && address_high <= 0xFU &&
        (address_low != 0U || address_high != 0U);
}

int cosmos_pcie_nvme_io_sq_words(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high,
    unsigned int *word0, unsigned int *word1) {
    if (word0 == 0 || word1 == 0 || queue_id == 0U ||
        queue_id > COSMOS_PCIE_IO_QUEUE_COUNT ||
        !cosmos_pcie_nvme_queue_base_valid(
            valid, entries, address_low, address_high) ||
        (valid != 0U &&
         (completion_queue_id == 0U ||
          completion_queue_id > COSMOS_PCIE_IO_QUEUE_COUNT)) ||
        (valid == 0U && completion_queue_id != 0U)) {
        return COSMOS_INVALID;
    }
    *word0 = address_low;
    *word1 = address_high | (valid << 15U) |
        (completion_queue_id << 16U) |
        ((entries == 0U ? 0U : entries - 1U) << 24U);
    return COSMOS_OK;
}

int cosmos_pcie_nvme_io_cq_words(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high, unsigned int *word0,
    unsigned int *word1) {
    if (word0 == 0 || word1 == 0 || queue_id == 0U ||
        queue_id > COSMOS_PCIE_IO_QUEUE_COUNT ||
        !cosmos_pcie_nvme_queue_base_valid(
            valid, entries, address_low, address_high) ||
        irq_enable > 1U || irq_vector > 7U ||
        (valid == 0U && (irq_enable != 0U || irq_vector != 0U))) {
        return COSMOS_INVALID;
    }
    *word0 = address_low;
    *word1 = address_high | (valid << 15U) |
        (irq_vector << 16U) | (irq_enable << 19U) |
        ((entries == 0U ? 0U : entries - 1U) << 24U);
    return COSMOS_OK;
}

int cosmos_pcie_nvme_configure_io_sq(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    unsigned int word0;
    unsigned int word1;
    int status = cosmos_pcie_nvme_io_sq_words(
        queue_id, valid, completion_queue_id, entries,
        address_low, address_high, &word0, &word1);

    if (status != COSMOS_OK) {
        return status;
    }
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)word0;
    (void)word1;
    return COSMOS_UNAVAILABLE;
#else
    unsigned int offset;

    if (cosmos_pcie_require_transport_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    offset = COSMOS_PCIE_IO_SQ_OFFSET +
        (queue_id - 1U) * COSMOS_PCIE_IO_QUEUE_STRIDE;
    cosmos_pcie_write(offset, word0);
    cosmos_data_sync_barrier();
    cosmos_pcie_write(offset + 4U, word1);
    cosmos_data_sync_barrier();
    return COSMOS_OK;
#endif
}

int cosmos_pcie_nvme_configure_io_cq(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high) {
    unsigned int word0;
    unsigned int word1;
    int status = cosmos_pcie_nvme_io_cq_words(
        queue_id, valid, irq_enable, irq_vector, entries,
        address_low, address_high, &word0, &word1);

    if (status != COSMOS_OK) {
        return status;
    }
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)word0;
    (void)word1;
    return COSMOS_UNAVAILABLE;
#else
    unsigned int offset;

    if (cosmos_pcie_require_transport_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    offset = COSMOS_PCIE_IO_CQ_OFFSET +
        (queue_id - 1U) * COSMOS_PCIE_IO_QUEUE_STRIDE;
    cosmos_pcie_write(offset, word0);
    cosmos_data_sync_barrier();
    cosmos_pcie_write(offset + 4U, word1);
    cosmos_data_sync_barrier();
    return COSMOS_OK;
#endif
}

enum cosmos_pcie_nvme_completion_result cosmos_pcie_nvme_post_completion(
    const struct cosmos_pcie_nvme_completion *completion) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    (void)completion;
    return COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
#else
    unsigned int word1;
    unsigned int word2;

    if (!cosmos_pcie_nvme_completion_valid(completion) ||
        cosmos_pcie_require_transport_ready() != COSMOS_OK) {
        return COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
    }

    word1 = completion->specific;
    word2 = ((completion->status_word & 0xFFFFU) << 16U) |
        (COSMOS_PCIE_NVME_CPL_TYPE_AUTO << 14U) |
        (completion->slot_tag & 0x7FU);

    /*
     * AUTO completion uses the captured slot's SQID/CID and releases that
     * slot. The preflight above is the last retryable point: after word1,
     * a retry could
     * duplicate a partially published completion.  MMIO writes have no
     * failure result, so preserve upstream set_auto_nvme_cpl()'s word1/word2
     * sequence without sampling link state in the middle.
     */
    cosmos_data_sync_barrier();
    cosmos_pcie_write(COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
                      COSMOS_PCIE_NVME_CPL_WORD1_OFFSET, word1);
    cosmos_data_sync_barrier();
    cosmos_pcie_write(COSMOS_PCIE_NVME_CPL_FIFO_OFFSET +
                      COSMOS_PCIE_NVME_CPL_WORD2_OFFSET, word2);
    cosmos_data_sync_barrier();
    return COSMOS_PCIE_NVME_COMPLETION_COMMITTED;
#endif
}

enum cosmos_pcie_nvme_completion_result cosmos_pcie_nvme_post_completion_fields(
    unsigned int queue_id, unsigned int slot_tag, unsigned int sequence,
    unsigned int cid, unsigned int specific, unsigned int sct,
    unsigned int sc, unsigned int dnr) {
    struct cosmos_pcie_nvme_completion completion;
    unsigned int status_word;

    if (cosmos_pcie_nvme_status_word(sct, sc, dnr, &status_word) !=
        COSMOS_OK) {
        return COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
    }
    completion.queue_id = queue_id;
    completion.slot_tag = slot_tag;
    completion.sequence = sequence;
    completion.cid = cid;
    completion.specific = specific;
    completion.status_word = status_word;
    return cosmos_pcie_nvme_post_completion(&completion);
}

int cosmos_pcie_is_available(void) {
    return cosmos_pcie_available == 1U;
}

int cosmos_pcie_service_irq(void) {
#if COSMOS_IS_QEMU || !COSMOS_PCIE_CONTRACT_BOUND
    cosmos_pcie_available = 0U;
    return COSMOS_UNAVAILABLE;
#else
    struct cosmos_pcie_snapshot snapshot;
    unsigned int devcfg_int_sts =
        cosmos_mmio_read32(COSMOS_ZYNQ_DEVCFG_BASE +
                           COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET);
    unsigned int pending;
    int result = COSMOS_OK;

    if (!cosmos_zynq_pcfg_done(devcfg_int_sts)) {
        cosmos_pcie_available = 0U;
        cosmos_data_sync_barrier();
        return COSMOS_UNAVAILABLE;
    }

    pending = cosmos_pcie_read(COSMOS_PCIE_IRQ_STATUS_OFFSET);
    if (pending == 0U) {
        return cosmos_pcie_is_available() ? COSMOS_OK : COSMOS_UNAVAILABLE;
    }
    if ((pending & ~COSMOS_PCIE_IRQ_DEFINED_MASK) != 0U ||
        (pending & COSMOS_PCIE_IRQ_FATAL_MASK) != 0U) {
        result = COSMOS_HW_ERROR;
    } else if ((pending & COSMOS_PCIE_IRQ_STATE_CHANGE_MASK) != 0U) {
        result = cosmos_pcie_poll_snapshot(&snapshot, 0);
    }
    if (result != COSMOS_OK) {
        cosmos_pcie_quiesce();
    }
    cosmos_pcie_write(COSMOS_PCIE_IRQ_CLEAR_OFFSET,
                      pending & COSMOS_PCIE_IRQ_DEFINED_MASK);
    cosmos_data_sync_barrier();
    return result;
#endif
}

int cosmos_pcie_init(void) {
    cosmos_pcie_available = 0U;
    cosmos_pcie_host_dma_pending = 0U;
    cosmos_pcie_host_dma_expected[0] = 0U;
    cosmos_pcie_host_dma_expected[1] = 0U;
    cosmos_pcie_host_dma_expected[2] = 0U;
    cosmos_pcie_host_dma_expected[3] = 0U;
    if (cosmos_pcie_selftest() != COSMOS_OK) {
        return COSMOS_INVALID;
    }
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#elif !COSMOS_PCIE_CONTRACT_BOUND
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_pcie_probe();
#endif
}

int cosmos_pcie_selftest(void) {
    const unsigned int link =
        COSMOS_PCIE_STATUS_LINK_UP | COSMOS_PCIE_LTSSM_L0;
    const unsigned int function =
        COSMOS_PCIE_FUNCTION_BUS_MASTER |
        COSMOS_PCIE_FUNCTION_MSI_ENABLE |
        (COSMOS_PCIE_FUNCTION_MME_MAX <<
         COSMOS_PCIE_FUNCTION_MME_SHIFT);
    const unsigned int ready_nvme =
        COSMOS_PCIE_NVME_CC_ENABLE | COSMOS_PCIE_NVME_CSTS_READY;
    const unsigned int ready_admin =
        COSMOS_PCIE_ADMIN_CQ_VALID |
        COSMOS_PCIE_ADMIN_SQ_VALID |
        COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE;
    unsigned int status_word;

    if (COSMOS_PCIE_HOST_BASE != 0x83C00000U ||
        COSMOS_PCIE_HOST_SPAN != 0x00010000U ||
        COSMOS_PCIE_PL_IRQ_ID != 61U ||
        COSMOS_PCIE_IRQ_DEFINED_MASK != 0x00000FFFU ||
        (COSMOS_PCIE_IRQ_STATE_CHANGE_MASK |
         COSMOS_PCIE_IRQ_FATAL_MASK) != COSMOS_PCIE_IRQ_DEFINED_MASK ||
        COSMOS_PCIE_STATUS_OFFSET != 0x0100U ||
        COSMOS_PCIE_FUNCTION_OFFSET != 0x0104U ||
        COSMOS_PCIE_NVME_STATUS_OFFSET != 0x0200U ||
        COSMOS_PCIE_HOST_DMA_FIFO_COUNT_OFFSET != 0x0204U ||
        COSMOS_PCIE_ADMIN_QUEUE_OFFSET != 0x021CU ||
        COSMOS_PCIE_NVME_CMD_FIFO_OFFSET != 0x0300U ||
        COSMOS_PCIE_NVME_CPL_FIFO_OFFSET != 0x0304U ||
        COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET != 0x0310U ||
        COSMOS_PCIE_HOST_DMA_MAX_BYTES != 0x00001000U ||
        COSMOS_PCIE_HOST_DMA_HOST_HIGH_MASK != 0x0000000FU ||
        COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX != 255U ||
        COSMOS_PCIE_NVME_CMD_SRAM_OFFSET != 0x2000U ||
        COSMOS_PCIE_NVME_CMD_SLOT_COUNT != 128U ||
        COSMOS_PCIE_NVME_CMD_DWORDS != 16U ||
        COSMOS_PCIE_NVME_CMD_RESERVED_MASK != 0x7F0080F0U ||
        COSMOS_PCIE_NVME_CPL_TYPE_ONLY != 0U ||
        COSMOS_PCIE_NVME_CPL_TYPE_AUTO != 1U ||
        COSMOS_PCIE_NVME_CPL_TYPE_RELEASE != 2U ||
        COSMOS_PCIE_NVME_CPL_STATUS_RESERVED_MASK != 0x3001U ||
        COSMOS_PCIE_BAR0_MASK != 0xFFFFE000U ||
        COSMOS_PCIE_BAR0_BYTES != 0x00002000U ||
        COSMOS_PCIE_VENDOR_ID != 0x10EEU ||
        COSMOS_PCIE_DEVICE_ID != 0x7028U ||
        COSMOS_PCIE_CLASS_CODE != 0x010802U) {
        return COSMOS_INVALID;
    }
    if (cosmos_pcie_snapshot_status(0U, function, 0U, 0U) !=
            COSMOS_UNAVAILABLE ||
        cosmos_pcie_snapshot_status(
            COSMOS_PCIE_STATUS_LINK_UP | (COSMOS_PCIE_LTSSM_L0 - 1U),
            function, 0U, 0U) != COSMOS_UNAVAILABLE ||
        cosmos_pcie_snapshot_status(
            link, function & ~COSMOS_PCIE_FUNCTION_BUS_MASTER, 0U, 0U) !=
            COSMOS_UNAVAILABLE ||
        cosmos_pcie_snapshot_status(
            link, function & ~COSMOS_PCIE_FUNCTION_MSI_ENABLE, 0U, 0U) !=
            COSMOS_UNAVAILABLE) {
        return COSMOS_INVALID;
    }
    if (cosmos_pcie_snapshot_status(link, function, 0U, 0U) != COSMOS_OK ||
        cosmos_pcie_snapshot_status(link,
            function | COSMOS_PCIE_FUNCTION_MSIX_ENABLE, 0U, 0U) !=
            COSMOS_HW_ERROR ||
        cosmos_pcie_snapshot_status(link,
            (function & ~COSMOS_PCIE_FUNCTION_MME_MASK) |
                ((COSMOS_PCIE_FUNCTION_MME_MAX + 1U) <<
                 COSMOS_PCIE_FUNCTION_MME_SHIFT),
            0U, 0U) != COSMOS_HW_ERROR ||
        cosmos_pcie_snapshot_status(link, function, 0U,
            COSMOS_PCIE_ADMIN_SQ_VALID) != COSMOS_HW_ERROR ||
        cosmos_pcie_snapshot_status(link, function, ready_nvme,
            ready_admin) != COSMOS_OK ||
        cosmos_pcie_snapshot_status(link, function, ready_nvme, 0U) !=
            COSMOS_HW_ERROR ||
        cosmos_pcie_snapshot_status(link | (1U << 31), function, 0U, 0U) !=
            COSMOS_HW_ERROR) {
        return COSMOS_INVALID;
    }
    if (cosmos_pcie_nvme_status_word(2U, 0x81U, 1U, &status_word) !=
            COSMOS_OK ||
        status_word != 0x8502U ||
        cosmos_pcie_nvme_status_word(8U, 0U, 0U, &status_word) !=
            COSMOS_INVALID) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}
