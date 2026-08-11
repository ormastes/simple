/* Bounded Cosmos+ Tiger4NSC/V2F NAND HAL. */
#include "cosmos_hal.h"
#include "cosmos_nfc_regs.h"
#include "cosmos_zynq_regs.h"

static unsigned int cosmos_nfc_initialized;
static unsigned int cosmos_nfc_init_failed;
static unsigned int cosmos_nfc_channel_locks[COSMOS_NFC_CHANNEL_COUNT];
static unsigned int cosmos_nfc_channel_faulted[COSMOS_NFC_CHANNEL_COUNT];

#define COSMOS_NFC_MAX_OWNED_RANGES 5U

struct cosmos_nfc_dma_range {
    unsigned int address;
    unsigned int size;
};

static unsigned int cosmos_nfc_ownership_lock;
/* A nonzero count survives timeout; no runtime path clears quarantine. */
static unsigned int
    cosmos_nfc_owned_count[COSMOS_NFC_CHANNEL_COUNT];
static struct cosmos_nfc_dma_range
    cosmos_nfc_owned[COSMOS_NFC_CHANNEL_COUNT]
                    [COSMOS_NFC_MAX_OWNED_RANGES];

static unsigned int cosmos_nfc_channel_base(unsigned int channel) {
    return COSMOS_NFC_CHANNEL0_BASE + channel * COSMOS_NFC_CHANNEL_STRIDE;
}

static int cosmos_nfc_row_valid(unsigned int row_address) {
    return row_address < COSMOS_NFC_LUN0_BASE_ROW +
            COSMOS_NFC_ROWS_PER_LUN ||
        (row_address >= COSMOS_NFC_LUN1_BASE_ROW &&
         row_address < COSMOS_NFC_LUN1_BASE_ROW +
            COSMOS_NFC_ROWS_PER_LUN);
}

static int cosmos_nfc_target_valid(unsigned int channel, unsigned int way,
                                   unsigned int row_address) {
    return channel < COSMOS_NFC_CHANNEL_COUNT &&
        way < COSMOS_NFC_WAY_COUNT && cosmos_nfc_row_valid(row_address);
}

static int cosmos_nfc_erase_row_valid(unsigned int row_address) {
    unsigned int lun_row;
    if (!cosmos_nfc_row_valid(row_address)) {
        return 0;
    }
    lun_row = row_address >= COSMOS_NFC_LUN1_BASE_ROW ?
        row_address - COSMOS_NFC_LUN1_BASE_ROW : row_address;
    return (lun_row % COSMOS_NFC_ROWS_PER_BLOCK) == 0U;
}

static int cosmos_nfc_dma_range_valid(unsigned int address,
                                      unsigned int size,
                                      unsigned int base,
                                      unsigned int end,
                                      unsigned int stride) {
    if (!COSMOS_NFC_IO_CONTRACT_BOUND || size == 0U || stride == 0U ||
        address < base || address > end ||
        ((address - base) % stride) != 0U) {
        return 0;
    }
    return size - 1U <= end - address;
}

static int cosmos_nfc_data_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, COSMOS_NFC_PAGE_DATA_BYTES,
        COSMOS_NFC_DATA_POOL_BASE, COSMOS_NFC_DATA_POOL_END,
        COSMOS_NFC_PAGE_DATA_BYTES);
}

static int cosmos_nfc_raw_data_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, COSMOS_NFC_RAW_ROW_BYTES,
        COSMOS_NFC_DATA_POOL_BASE, COSMOS_NFC_DATA_POOL_END,
        COSMOS_NFC_PAGE_DATA_BYTES);
}

static int cosmos_nfc_spare_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, COSMOS_NFC_PAGE_SPARE_BYTES,
        COSMOS_NFC_SPARE_POOL_BASE, COSMOS_NFC_SPARE_POOL_END,
        COSMOS_NFC_PAGE_SPARE_BYTES);
}

static int cosmos_nfc_completion_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, sizeof(unsigned int),
        COSMOS_NFC_COMPLETION_POOL_BASE, COSMOS_NFC_COMPLETION_POOL_END,
        sizeof(unsigned int));
}

static int cosmos_nfc_status_report_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, sizeof(unsigned int),
        COSMOS_NFC_STATUS_POOL_BASE, COSMOS_NFC_STATUS_POOL_END,
        sizeof(unsigned int));
}

static int cosmos_nfc_error_info_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, COSMOS_NFC_ERROR_INFO_BYTES,
        COSMOS_NFC_ERROR_POOL_BASE, COSMOS_NFC_ERROR_POOL_END,
        COSMOS_NFC_ERROR_INFO_BYTES);
}

static int cosmos_nfc_toggle_valid(unsigned int address) {
    return cosmos_nfc_dma_range_valid(
        address, 3U * sizeof(unsigned int),
        COSMOS_NFC_TOGGLE_POOL_BASE, COSMOS_NFC_TOGGLE_POOL_END,
        sizeof(unsigned int));
}

static int cosmos_nfc_ranges_overlap(unsigned int first, unsigned int first_size,
                                     unsigned int second,
                                     unsigned int second_size) {
    return first < second ? second - first < first_size :
        first - second < second_size;
}

static int cosmos_nfc_ownership_lock_acquire(void) {
    unsigned int remaining;
    for (remaining = COSMOS_NFC_POLL_LIMIT; remaining != 0U; remaining--) {
        if (__atomic_exchange_n(&cosmos_nfc_ownership_lock, 1U,
                                __ATOMIC_ACQUIRE) == 0U) {
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}

static void cosmos_nfc_ownership_lock_release(void) {
    __atomic_store_n(&cosmos_nfc_ownership_lock, 0U, __ATOMIC_RELEASE);
}

static int cosmos_nfc_dma_reserve(
        unsigned int channel,
        const struct cosmos_nfc_dma_range *ranges,
        unsigned int count) {
    unsigned int owner;
    unsigned int index;
    int status;

    if (channel >= COSMOS_NFC_CHANNEL_COUNT || ranges == 0 ||
        count == 0U || count > COSMOS_NFC_MAX_OWNED_RANGES) {
        return COSMOS_INVALID;
    }
    status = cosmos_nfc_ownership_lock_acquire();
    if (status != COSMOS_OK) {
        return status;
    }
    for (owner = 0U; owner < COSMOS_NFC_CHANNEL_COUNT; owner++) {
        unsigned int owned_index;
        for (owned_index = 0U;
             owned_index < cosmos_nfc_owned_count[owner];
             owned_index++) {
            for (index = 0U; index < count; index++) {
                if (cosmos_nfc_ranges_overlap(
                        ranges[index].address, ranges[index].size,
                        cosmos_nfc_owned[owner][owned_index].address,
                        cosmos_nfc_owned[owner][owned_index].size)) {
                    cosmos_nfc_ownership_lock_release();
                    return COSMOS_HW_ERROR;
                }
            }
        }
    }
    for (index = 0U; index < count; index++) {
        cosmos_nfc_owned[channel][index] = ranges[index];
    }
    cosmos_nfc_owned_count[channel] = count;
    cosmos_nfc_ownership_lock_release();
    return COSMOS_OK;
}

static int cosmos_nfc_dma_finish(unsigned int channel, int status) {
    int lock_status;
    if (status == COSMOS_TIMEOUT) {
        return status;
    }
    lock_status = cosmos_nfc_ownership_lock_acquire();
    if (lock_status != COSMOS_OK) {
        return lock_status;
    }
    cosmos_nfc_owned_count[channel] = 0U;
    cosmos_nfc_ownership_lock_release();
    return status;
}

static int cosmos_nfc_contract_ready(void) {
    unsigned int devcfg_status;
    if (!COSMOS_NFC_IO_CONTRACT_BOUND || COSMOS_IS_QEMU) {
        return COSMOS_UNAVAILABLE;
    }
    devcfg_status = cosmos_mmio_read32(
        COSMOS_ZYNQ_DEVCFG_BASE + COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET);
    return cosmos_zynq_pcfg_done(devcfg_status) ? COSMOS_OK :
        COSMOS_UNAVAILABLE;
}

static int cosmos_nfc_channel_lock(unsigned int channel) {
    unsigned int remaining;
    for (remaining = COSMOS_NFC_POLL_LIMIT; remaining != 0U; remaining--) {
        if (__atomic_exchange_n(&cosmos_nfc_channel_locks[channel], 1U,
                                __ATOMIC_ACQUIRE) == 0U) {
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}

static void cosmos_nfc_channel_unlock(unsigned int channel) {
    __atomic_store_n(&cosmos_nfc_channel_locks[channel], 0U,
                     __ATOMIC_RELEASE);
}

static int cosmos_nfc_channel_is_faulted(unsigned int channel) {
    return __atomic_load_n(&cosmos_nfc_channel_faulted[channel],
                           __ATOMIC_ACQUIRE) != 0U;
}

static int cosmos_nfc_channel_result(unsigned int channel, int status) {
    if (status == COSMOS_TIMEOUT) {
        __atomic_store_n(&cosmos_nfc_channel_faulted[channel], 1U,
                         __ATOMIC_RELEASE);
    }
    return status;
}

static int cosmos_nfc_wait_channel_accept(unsigned int base) {
    unsigned int remaining;
    for (remaining = COSMOS_NFC_POLL_LIMIT; remaining != 0U; remaining--) {
        if (cosmos_mmio_read32(base + COSMOS_NFC_CHANNEL_BUSY) == 0U) {
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}

static int cosmos_nfc_wait_way_ready(unsigned int base, unsigned int way) {
    unsigned int remaining;
    for (remaining = COSMOS_NFC_POLL_LIMIT; remaining != 0U; remaining--) {
        if ((cosmos_mmio_read32(base + COSMOS_NFC_READY_BUSY) &
             (1U << way)) != 0U) {
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}

static int cosmos_nfc_wait_controller_idle(unsigned int base) {
    unsigned int remaining;
    for (remaining = COSMOS_NFC_POLL_LIMIT; remaining != 0U; remaining--) {
        if (cosmos_mmio_read32(base + COSMOS_NFC_CONTROLLER_IDLE) != 0U) {
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}

static int cosmos_nfc_issue(unsigned int base, unsigned int way,
                            unsigned int command) {
    cosmos_mmio_write32(base + COSMOS_NFC_WAY_SELECTION, way);
    cosmos_data_sync_barrier();
    cosmos_mmio_write32(base + COSMOS_NFC_CMD_SELECT, command);
    cosmos_data_sync_barrier();
    return cosmos_nfc_wait_channel_accept(base);
}

static int cosmos_nfc_decode_status(unsigned int raw_report,
                                    unsigned int *nand_status) {
    unsigned int status;
    if ((raw_report & COSMOS_NFC_STATUS_REPORT_DONE) == 0U ||
        nand_status == 0) {
        return COSMOS_INVALID;
    }
    status = raw_report >> 1U;
    *nand_status = status;
    if ((status & COSMOS_NFC_STATUS_COMPLETE_MASK) !=
        COSMOS_NFC_STATUS_COMPLETE_MASK) {
        return COSMOS_UNAVAILABLE;
    }
    return (status & COSMOS_NFC_STATUS_FAIL_MASK) == 0U ?
        COSMOS_OK : COSMOS_HW_ERROR;
}

static int cosmos_nfc_status_locked(unsigned int channel, unsigned int way,
                                    unsigned int status_report_address,
                                    unsigned int *nand_status) {
    volatile unsigned int *report;
    unsigned int base;
    unsigned int remaining;
    int pending = 0;

    base = cosmos_nfc_channel_base(channel);
    report = (volatile unsigned int *)status_report_address;
    for (remaining = COSMOS_NFC_POLL_LIMIT; remaining != 0U; remaining--) {
        if (!pending) {
            if (cosmos_mmio_read32(base + COSMOS_NFC_CHANNEL_BUSY) != 0U ||
                (cosmos_mmio_read32(base + COSMOS_NFC_READY_BUSY) &
                 (1U << way)) == 0U) {
                continue;
            }
            *report = 0U;
            cosmos_data_sync_barrier();
            cosmos_mmio_write32(base + COSMOS_NFC_WAY_SELECTION, way);
            cosmos_mmio_write32(base + COSMOS_NFC_COMPLETION_ADDRESS,
                                status_report_address);
            cosmos_data_sync_barrier();
            cosmos_mmio_write32(base + COSMOS_NFC_CMD_SELECT,
                                COSMOS_NFC_CMD_STATUS_CHECK);
            cosmos_data_sync_barrier();
            pending = 1;
            continue;
        }
        {
            unsigned int raw_report = *report;
            int status;
            if ((raw_report & COSMOS_NFC_STATUS_REPORT_DONE) == 0U) {
                continue;
            }
            status = cosmos_nfc_decode_status(raw_report, nand_status);
            if (status != COSMOS_UNAVAILABLE) {
                int idle_status = cosmos_nfc_wait_controller_idle(base);
                return idle_status == COSMOS_OK ? status : idle_status;
            }
            pending = 0;
        }
    }
    return COSMOS_TIMEOUT;
}

int cosmos_nfc_status(unsigned int channel, unsigned int way,
                      unsigned int status_report_address,
                      unsigned int *nand_status) {
    const struct cosmos_nfc_dma_range ranges[] = {
        {status_report_address, sizeof(unsigned int)}
    };
    int status;
    if (__atomic_load_n(&cosmos_nfc_initialized, __ATOMIC_ACQUIRE) == 0U ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    if (!cosmos_nfc_target_valid(channel, way, 0U) ||
        !cosmos_nfc_status_report_valid(status_report_address) ||
        nand_status == 0) {
        return COSMOS_INVALID;
    }
    status = cosmos_nfc_channel_lock(channel);
    if (status != COSMOS_OK) {
        return status;
    }
    if (cosmos_nfc_channel_is_faulted(channel) ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        cosmos_nfc_channel_unlock(channel);
        return COSMOS_HW_ERROR;
    }
    status = cosmos_nfc_dma_reserve(channel, ranges, 1U);
    if (status != COSMOS_OK) {
        cosmos_nfc_channel_unlock(channel);
        return status;
    }
    status = cosmos_nfc_status_locked(channel, way, status_report_address,
                                      nand_status);
    status = cosmos_nfc_dma_finish(channel, status);
    status = cosmos_nfc_channel_result(channel, status);
    cosmos_nfc_channel_unlock(channel);
    return status;
}

int cosmos_nfc_decode_ecc(const volatile unsigned int *error_info,
                          struct cosmos_nfc_ecc *ecc) {
    unsigned int first;
    if (error_info == 0 || ecc == 0) {
        return COSMOS_INVALID;
    }
    first = error_info[0];
    ecc->crc_valid = (first & COSMOS_NFC_ECC_CRC_VALID) != 0U;
    ecc->spare_valid = (first & COSMOS_NFC_ECC_SPARE_VALID) != 0U;
    ecc->page_valid = error_info[1] == 0xFFFFFFFFU;
    ecc->worst_chunk_errors =
        (first & COSMOS_NFC_ECC_WORST_MASK) >> COSMOS_NFC_ECC_WORST_SHIFT;
    ecc->needs_refresh =
        ecc->worst_chunk_errors > COSMOS_NFC_ECC_WARNING_THRESHOLD;
    return ecc->crc_valid && ecc->spare_valid && ecc->page_valid ?
        COSMOS_OK : COSMOS_HW_ERROR;
}

static int cosmos_nfc_io_valid(const struct cosmos_nfc_io *io, int read) {
    if (io == 0 ||
        !cosmos_nfc_target_valid(io->channel, io->way, io->row_address) ||
        !cosmos_nfc_data_valid(io->data_address) ||
        !cosmos_nfc_spare_valid(io->spare_address) ||
        !cosmos_nfc_status_report_valid(io->status_report_address)) {
        return 0;
    }
    return !read ||
        (cosmos_nfc_error_info_valid(io->error_info_address) &&
         cosmos_nfc_completion_valid(io->completion_address));
}

int cosmos_nfc_read_page(const struct cosmos_nfc_io *io,
                         struct cosmos_nfc_ecc *ecc) {
    volatile unsigned int *completion;
    volatile unsigned int *error_info;
    struct cosmos_nfc_dma_range ranges[COSMOS_NFC_MAX_OWNED_RANGES];
    unsigned int base;
    unsigned int index;
    unsigned int nand_status;
    int status;

    if (__atomic_load_n(&cosmos_nfc_initialized, __ATOMIC_ACQUIRE) == 0U ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    if (!cosmos_nfc_io_valid(io, 1) || ecc == 0) {
        return COSMOS_INVALID;
    }
    ranges[0].address = io->data_address;
    ranges[0].size = COSMOS_NFC_PAGE_DATA_BYTES;
    ranges[1].address = io->spare_address;
    ranges[1].size = COSMOS_NFC_PAGE_SPARE_BYTES;
    ranges[2].address = io->error_info_address;
    ranges[2].size = COSMOS_NFC_ERROR_INFO_BYTES;
    ranges[3].address = io->completion_address;
    ranges[3].size = sizeof(unsigned int);
    ranges[4].address = io->status_report_address;
    ranges[4].size = sizeof(unsigned int);
    status = cosmos_nfc_channel_lock(io->channel);
    if (status != COSMOS_OK) {
        return status;
    }
    if (cosmos_nfc_channel_is_faulted(io->channel) ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        cosmos_nfc_channel_unlock(io->channel);
        return COSMOS_HW_ERROR;
    }
    status = cosmos_nfc_dma_reserve(
        io->channel, ranges, COSMOS_NFC_MAX_OWNED_RANGES);
    if (status != COSMOS_OK) {
        cosmos_nfc_channel_unlock(io->channel);
        return status;
    }

    base = cosmos_nfc_channel_base(io->channel);
    cosmos_mmio_write32(base + COSMOS_NFC_ROW_ADDRESS, io->row_address);
    status = cosmos_nfc_issue(base, io->way,
                              COSMOS_NFC_CMD_READ_PAGE_TRIGGER);
    if (status != COSMOS_OK) {
        goto done;
    }
    status = cosmos_nfc_status_locked(io->channel, io->way,
                                      io->status_report_address, &nand_status);
    if (status != COSMOS_OK) {
        goto done;
    }

    completion = (volatile unsigned int *)io->completion_address;
    error_info = (volatile unsigned int *)io->error_info_address;
    *completion = 0U;
    for (index = 0U; index < COSMOS_NFC_ERROR_INFO_WORDS; index++) {
        error_info[index] = 0U;
    }
    cosmos_mmio_write32(base + COSMOS_NFC_DATA_ADDRESS, io->data_address);
    cosmos_mmio_write32(base + COSMOS_NFC_SPARE_ADDRESS, io->spare_address);
    cosmos_mmio_write32(base + COSMOS_NFC_ERROR_COUNT_ADDRESS,
                        io->error_info_address);
    cosmos_mmio_write32(base + COSMOS_NFC_COMPLETION_ADDRESS,
                        io->completion_address);
    cosmos_mmio_write32(base + COSMOS_NFC_ROW_ADDRESS, io->row_address);
    status = cosmos_nfc_issue(base, io->way,
                              COSMOS_NFC_CMD_READ_PAGE_TRANSFER);
    if (status != COSMOS_OK) {
        goto done;
    }
    status = COSMOS_TIMEOUT;
    for (index = COSMOS_NFC_POLL_LIMIT; index != 0U; index--) {
        if (*completion == COSMOS_NFC_TRANSFER_COMPLETE) {
            cosmos_data_sync_barrier();
            status = cosmos_nfc_wait_controller_idle(base);
            if (status == COSMOS_OK) {
                status = cosmos_nfc_decode_ecc(error_info, ecc);
            }
            break;
        }
    }
done:
    status = cosmos_nfc_dma_finish(io->channel, status);
    status = cosmos_nfc_channel_result(io->channel, status);
    cosmos_nfc_channel_unlock(io->channel);
    return status;
}

static int cosmos_nfc_raw_io_valid(const struct cosmos_nfc_io *io) {
    return io != 0 &&
        cosmos_nfc_target_valid(io->channel, io->way, io->row_address) &&
        cosmos_nfc_raw_data_valid(io->data_address) &&
        cosmos_nfc_completion_valid(io->completion_address) &&
        cosmos_nfc_status_report_valid(io->status_report_address);
}

int cosmos_nfc_read_page_raw(const struct cosmos_nfc_io *io) {
    volatile unsigned int *completion;
    struct cosmos_nfc_dma_range ranges[3];
    unsigned int base;
    unsigned int index;
    unsigned int nand_status;
    unsigned int completion_word;
    int status;

    if (__atomic_load_n(&cosmos_nfc_initialized, __ATOMIC_ACQUIRE) == 0U ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    if (!cosmos_nfc_raw_io_valid(io)) {
        return COSMOS_INVALID;
    }
    ranges[0].address = io->data_address;
    ranges[0].size = COSMOS_NFC_RAW_ROW_BYTES;
    ranges[1].address = io->completion_address;
    ranges[1].size = sizeof(unsigned int);
    ranges[2].address = io->status_report_address;
    ranges[2].size = sizeof(unsigned int);
    status = cosmos_nfc_channel_lock(io->channel);
    if (status != COSMOS_OK) {
        return status;
    }
    if (cosmos_nfc_channel_is_faulted(io->channel) ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        cosmos_nfc_channel_unlock(io->channel);
        return COSMOS_HW_ERROR;
    }
    status = cosmos_nfc_dma_reserve(io->channel, ranges, 3U);
    if (status != COSMOS_OK) {
        cosmos_nfc_channel_unlock(io->channel);
        return status;
    }

    base = cosmos_nfc_channel_base(io->channel);
    cosmos_mmio_write32(base + COSMOS_NFC_ROW_ADDRESS, io->row_address);
    status = cosmos_nfc_issue(base, io->way,
                              COSMOS_NFC_CMD_READ_PAGE_TRIGGER);
    if (status == COSMOS_OK) {
        status = cosmos_nfc_status_locked(io->channel, io->way,
                                          io->status_report_address,
                                          &nand_status);
    }
    if (status != COSMOS_OK) {
        goto done;
    }

    completion = (volatile unsigned int *)io->completion_address;
    *completion = 0U;
    cosmos_data_sync_barrier();
    cosmos_mmio_write32(base + COSMOS_NFC_DATA_ADDRESS, io->data_address);
    cosmos_mmio_write32(base + COSMOS_NFC_COMPLETION_ADDRESS,
                        io->completion_address);
    cosmos_mmio_write32(base + COSMOS_NFC_ROW_ADDRESS, io->row_address);
    status = cosmos_nfc_issue(base, io->way,
                              COSMOS_NFC_CMD_READ_PAGE_TRANSFER_RAW);
    if (status != COSMOS_OK) {
        goto done;
    }
    status = COSMOS_TIMEOUT;
    for (index = COSMOS_NFC_POLL_LIMIT; index != 0U; index--) {
        completion_word = *completion;
        if (completion_word == COSMOS_NFC_TRANSFER_COMPLETE) {
            cosmos_data_sync_barrier();
            status = cosmos_nfc_wait_controller_idle(base);
            break;
        }
        if (completion_word != 0U) {
            cosmos_data_sync_barrier();
            status = COSMOS_HW_ERROR;
            break;
        }
    }
done:
    status = cosmos_nfc_dma_finish(io->channel, status);
    status = cosmos_nfc_channel_result(io->channel, status);
    cosmos_nfc_channel_unlock(io->channel);
    return status;
}

int cosmos_nfc_program_page(const struct cosmos_nfc_io *io) {
    struct cosmos_nfc_dma_range ranges[3];
    unsigned int base;
    unsigned int nand_status;
    int status;

    if (__atomic_load_n(&cosmos_nfc_initialized, __ATOMIC_ACQUIRE) == 0U ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    if (!cosmos_nfc_io_valid(io, 0)) {
        return COSMOS_INVALID;
    }
    ranges[0].address = io->data_address;
    ranges[0].size = COSMOS_NFC_PAGE_DATA_BYTES;
    ranges[1].address = io->spare_address;
    ranges[1].size = COSMOS_NFC_PAGE_SPARE_BYTES;
    ranges[2].address = io->status_report_address;
    ranges[2].size = sizeof(unsigned int);
    status = cosmos_nfc_channel_lock(io->channel);
    if (status != COSMOS_OK) {
        return status;
    }
    if (cosmos_nfc_channel_is_faulted(io->channel) ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        cosmos_nfc_channel_unlock(io->channel);
        return COSMOS_HW_ERROR;
    }
    status = cosmos_nfc_dma_reserve(io->channel, ranges, 3U);
    if (status != COSMOS_OK) {
        cosmos_nfc_channel_unlock(io->channel);
        return status;
    }

    base = cosmos_nfc_channel_base(io->channel);
    cosmos_mmio_write32(base + COSMOS_NFC_ROW_ADDRESS, io->row_address);
    cosmos_mmio_write32(base + COSMOS_NFC_DATA_ADDRESS, io->data_address);
    cosmos_mmio_write32(base + COSMOS_NFC_SPARE_ADDRESS, io->spare_address);
    status = cosmos_nfc_issue(base, io->way, COSMOS_NFC_CMD_PROGRAM_PAGE);
    if (status == COSMOS_OK) {
        status = cosmos_nfc_status_locked(io->channel, io->way,
                                          io->status_report_address,
                                          &nand_status);
    }
    status = cosmos_nfc_dma_finish(io->channel, status);
    status = cosmos_nfc_channel_result(io->channel, status);
    cosmos_nfc_channel_unlock(io->channel);
    return status;
}

int cosmos_nfc_erase_block(unsigned int channel, unsigned int way,
                           unsigned int row_address,
                           unsigned int status_report_address) {
    const struct cosmos_nfc_dma_range ranges[] = {
        {status_report_address, sizeof(unsigned int)}
    };
    unsigned int base;
    unsigned int nand_status;
    int status;

    if (__atomic_load_n(&cosmos_nfc_initialized, __ATOMIC_ACQUIRE) == 0U ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    if (!cosmos_nfc_target_valid(channel, way, row_address) ||
        !cosmos_nfc_erase_row_valid(row_address) ||
        !cosmos_nfc_status_report_valid(status_report_address)) {
        return COSMOS_INVALID;
    }
    status = cosmos_nfc_channel_lock(channel);
    if (status != COSMOS_OK) {
        return status;
    }
    if (cosmos_nfc_channel_is_faulted(channel) ||
        cosmos_nfc_contract_ready() != COSMOS_OK) {
        cosmos_nfc_channel_unlock(channel);
        return COSMOS_HW_ERROR;
    }
    status = cosmos_nfc_dma_reserve(channel, ranges, 1U);
    if (status != COSMOS_OK) {
        cosmos_nfc_channel_unlock(channel);
        return status;
    }

    base = cosmos_nfc_channel_base(channel);
    cosmos_mmio_write32(base + COSMOS_NFC_ROW_ADDRESS, row_address);
    status = cosmos_nfc_issue(base, way, COSMOS_NFC_CMD_BLOCK_ERASE);
    if (status == COSMOS_OK) {
        status = cosmos_nfc_status_locked(channel, way,
                                          status_report_address,
                                          &nand_status);
    }
    status = cosmos_nfc_dma_finish(channel, status);
    status = cosmos_nfc_channel_result(channel, status);
    cosmos_nfc_channel_unlock(channel);
    return status;
}

static int cosmos_nfc_reset_way(unsigned int base, unsigned int way,
                                unsigned int payload_address) {
    volatile unsigned int *payload =
        (volatile unsigned int *)payload_address;
    int status = cosmos_nfc_issue(base, way, COSMOS_NFC_CMD_RESET);
    if (status != COSMOS_OK) {
        return status;
    }
    status = cosmos_nfc_wait_controller_idle(base);
    if (status == COSMOS_OK) {
        status = cosmos_nfc_wait_way_ready(base, way);
    }
    if (status != COSMOS_OK) {
        return status;
    }

    /* GreedyFTL V2FEnterToggleMode payload: features 02h, 10h, then 01h. */
    payload[0] = 0x00000006U;
    payload[1] = 0x00000008U;
    payload[2] = 0x00000020U;
    cosmos_data_sync_barrier();
    cosmos_mmio_write32(base + COSMOS_NFC_USER_DATA, payload_address);
    status = cosmos_nfc_issue(base, way, COSMOS_NFC_CMD_SET_FEATURES);
    if (status == COSMOS_OK) {
        status = cosmos_nfc_wait_controller_idle(base);
    }
    return status == COSMOS_OK ? cosmos_nfc_wait_way_ready(base, way) : status;
}

int cosmos_nfc_init(void) {
    const struct cosmos_nfc_dma_range toggle_range[] = {
        {COSMOS_NFC_TOGGLE_POOL_BASE, 3U * sizeof(unsigned int)}
    };
    unsigned int channel;
    unsigned int way;
    int status;

    if (__atomic_load_n(&cosmos_nfc_initialized, __ATOMIC_ACQUIRE) != 0U) {
        return COSMOS_OK;
    }
    if (__atomic_load_n(&cosmos_nfc_init_failed, __ATOMIC_ACQUIRE) != 0U) {
        return COSMOS_HW_ERROR;
    }
    if (cosmos_nfc_selftest() != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    status = cosmos_nfc_contract_ready();
    if (status != COSMOS_OK) {
        return status;
    }
    if (!cosmos_nfc_toggle_valid(COSMOS_NFC_TOGGLE_POOL_BASE)) {
        return COSMOS_INVALID;
    }
    for (channel = 0U; channel < COSMOS_NFC_CHANNEL_COUNT; channel++) {
        unsigned int base = cosmos_nfc_channel_base(channel);
        status = cosmos_nfc_channel_lock(channel);
        if (status != COSMOS_OK) {
            __atomic_store_n(&cosmos_nfc_init_failed, 1U, __ATOMIC_RELEASE);
            return status;
        }
        if (cosmos_nfc_channel_is_faulted(channel)) {
            cosmos_nfc_channel_unlock(channel);
            __atomic_store_n(&cosmos_nfc_init_failed, 1U, __ATOMIC_RELEASE);
            return COSMOS_HW_ERROR;
        }
        status = cosmos_nfc_dma_reserve(channel, toggle_range, 1U);
        if (status != COSMOS_OK) {
            cosmos_nfc_channel_unlock(channel);
            __atomic_store_n(&cosmos_nfc_init_failed, 1U, __ATOMIC_RELEASE);
            return status;
        }
        for (way = 0U; way < COSMOS_NFC_WAY_COUNT; way++) {
            status = cosmos_nfc_reset_way(
                base, way, COSMOS_NFC_TOGGLE_POOL_BASE);
            if (status != COSMOS_OK) {
                status = cosmos_nfc_dma_finish(channel, status);
                cosmos_nfc_channel_result(channel, status);
                cosmos_nfc_channel_unlock(channel);
                __atomic_store_n(&cosmos_nfc_init_failed, 1U,
                                 __ATOMIC_RELEASE);
                return status;
            }
        }
        status = cosmos_nfc_dma_finish(channel, COSMOS_OK);
        if (status != COSMOS_OK) {
            cosmos_nfc_channel_result(channel, status);
            cosmos_nfc_channel_unlock(channel);
            __atomic_store_n(&cosmos_nfc_init_failed, 1U, __ATOMIC_RELEASE);
            return status;
        }
        cosmos_nfc_channel_unlock(channel);
    }
    __atomic_store_n(&cosmos_nfc_initialized, 1U, __ATOMIC_RELEASE);
    return COSMOS_OK;
}

int cosmos_nfc_selftest(void) {
    volatile unsigned int valid_error_info[COSMOS_NFC_ERROR_INFO_WORDS] = {
        COSMOS_NFC_ECC_CRC_VALID | COSMOS_NFC_ECC_SPARE_VALID |
        (5U << COSMOS_NFC_ECC_WORST_SHIFT),
        0xFFFFFFFFU
    };
    struct cosmos_nfc_ecc ecc;
    unsigned int status;

    if (COSMOS_NFC_CMD_SELECT != 0x00U ||
        COSMOS_NFC_READY_BUSY != 0x24U ||
        COSMOS_NFC_CONTROLLER_IDLE != 0x2CU ||
        COSMOS_NFC_CMD_READ_PAGE_TRIGGER != 13U ||
        COSMOS_NFC_CMD_READ_PAGE_TRANSFER != 18U ||
        COSMOS_NFC_CMD_READ_PAGE_TRANSFER_RAW != 55U ||
        COSMOS_NFC_CMD_PROGRAM_PAGE != 28U ||
        COSMOS_NFC_CMD_BLOCK_ERASE != 37U ||
        COSMOS_NFC_CMD_STATUS_CHECK != 41U ||
        COSMOS_NFC_TRANSFER_COMPLETE != 0xA5000001U ||
        COSMOS_NFC_CHANNEL_COUNT != 8U ||
        COSMOS_NFC_WAY_COUNT != 8U ||
        COSMOS_NFC_CHANNEL0_BASE != COSMOS_NFC_BASE ||
        cosmos_nfc_channel_base(7U) != 0x43C70000U ||
        !cosmos_nfc_row_valid(0x001057FFU) ||
        cosmos_nfc_row_valid(0x00105800U) ||
        cosmos_nfc_row_valid(0x001FFFFFU) ||
        !cosmos_nfc_row_valid(0x00200000U) ||
        !cosmos_nfc_row_valid(0x003057FFU) ||
        cosmos_nfc_row_valid(0x00305800U) ||
        !cosmos_nfc_erase_row_valid(0x00105700U) ||
        !cosmos_nfc_erase_row_valid(0x00200000U) ||
        cosmos_nfc_erase_row_valid(0x00200001U) ||
        cosmos_nfc_decode_status(0xC1U, &status) != COSMOS_OK ||
        status != 0x60U ||
        cosmos_nfc_decode_status(0xC3U, &status) != COSMOS_HW_ERROR ||
        cosmos_nfc_decode_ecc(valid_error_info, &ecc) != COSMOS_OK ||
        ecc.crc_valid != 1U || ecc.spare_valid != 1U ||
        ecc.page_valid != 1U || ecc.worst_chunk_errors != 5U ||
        ecc.needs_refresh != 0U) {
        return COSMOS_INVALID;
    }
    if (COSMOS_NFC_IO_CONTRACT_BOUND &&
        (COSMOS_NFC_NVME_MANAGEMENT_BASE != 0x00200000U ||
         COSMOS_NFC_NVME_MANAGEMENT_END != 0x002FFFFFU ||
         COSMOS_NFC_DATA_POOL_BASE != 0x10000000U ||
         COSMOS_NFC_DATA_POOL_END != 0x110FFFFFU ||
         COSMOS_NFC_SPARE_POOL_BASE != 0x11100000U ||
         COSMOS_NFC_SPARE_POOL_END != 0x11143FFFU ||
         COSMOS_NFC_COMPLETION_POOL_BASE != 0x17000000U ||
         COSMOS_NFC_COMPLETION_POOL_END != 0x170000FFU ||
         COSMOS_NFC_STATUS_POOL_BASE != 0x17000100U ||
         COSMOS_NFC_STATUS_POOL_END != 0x170001FFU ||
         COSMOS_NFC_ERROR_POOL_BASE != 0x17000200U ||
         COSMOS_NFC_ERROR_POOL_END != 0x17000CFFU ||
         COSMOS_NFC_TOGGLE_POOL_BASE != 0x17000D00U ||
         COSMOS_NFC_TOGGLE_POOL_END != 0x17001CFFU ||
         !cosmos_nfc_data_valid(COSMOS_NFC_DATA_POOL_BASE) ||
         !cosmos_nfc_data_valid(
             COSMOS_NFC_DATA_POOL_END - COSMOS_NFC_PAGE_DATA_BYTES + 1U) ||
         !cosmos_nfc_spare_valid(COSMOS_NFC_SPARE_POOL_BASE) ||
         !cosmos_nfc_spare_valid(
             COSMOS_NFC_SPARE_POOL_END -
             COSMOS_NFC_PAGE_SPARE_BYTES + 1U) ||
         !cosmos_nfc_completion_valid(COSMOS_NFC_COMPLETION_POOL_END - 3U) ||
         !cosmos_nfc_status_report_valid(COSMOS_NFC_STATUS_POOL_END - 3U) ||
         !cosmos_nfc_error_info_valid(
             COSMOS_NFC_ERROR_POOL_END - COSMOS_NFC_ERROR_INFO_BYTES + 1U) ||
         !cosmos_nfc_toggle_valid(COSMOS_NFC_TOGGLE_POOL_BASE) ||
         cosmos_nfc_data_valid(COSMOS_NFC_NVME_MANAGEMENT_BASE) ||
         cosmos_nfc_data_valid(COSMOS_NFC_DATA_POOL_BASE + 4U) ||
         cosmos_nfc_spare_valid(COSMOS_NFC_SPARE_POOL_BASE + 4U) ||
         cosmos_nfc_error_info_valid(COSMOS_NFC_ERROR_POOL_BASE + 4U))) {
        return COSMOS_INVALID;
    }
    if (cosmos_nfc_channel_lock(0U) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    cosmos_nfc_channel_unlock(0U);
    valid_error_info[0] &= ~COSMOS_NFC_ECC_CRC_VALID;
    return cosmos_nfc_decode_ecc(valid_error_info, &ecc) == COSMOS_HW_ERROR ?
        COSMOS_OK : COSMOS_INVALID;
}
