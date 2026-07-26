#include <stdint.h>

#include "cosmos_nvme_ftl_media.h"

#ifndef COSMOS_NVME_FTL_MEDIA_DMA_H2D
#define COSMOS_NVME_FTL_MEDIA_DMA_H2D \
    cosmos_pcie_host_dma_submit_auto_host_to_device
#endif
#ifndef COSMOS_NVME_FTL_MEDIA_DMA_D2H
#define COSMOS_NVME_FTL_MEDIA_DMA_D2H \
    cosmos_pcie_host_dma_submit_auto_device_to_host
#endif
#ifndef COSMOS_NVME_FTL_MEDIA_DMA_POLL
#define COSMOS_NVME_FTL_MEDIA_DMA_POLL cosmos_pcie_host_dma_poll_auto
#endif
#ifndef COSMOS_NVME_FTL_MEDIA_NFC_READ
#define COSMOS_NVME_FTL_MEDIA_NFC_READ cosmos_nfc_read_page
#endif
#ifndef COSMOS_NVME_FTL_MEDIA_NFC_PROGRAM
#define COSMOS_NVME_FTL_MEDIA_NFC_PROGRAM cosmos_nfc_program_page
#endif

#define COSMOS_NVME_FTL_MEDIA_PAGE_LBAS \
    COSMOS_FTL_NVME_BLOCKS_PER_PAGE
#define COSMOS_NVME_FTL_MEDIA_MAX_LBAS \
    (COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX + 1U)
#define COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES 3U

struct cosmos_nvme_ftl_media_dsm_range {
    unsigned int attributes;
    unsigned int length;
    unsigned long long starting_lba;
};

static unsigned long long media_u64(unsigned int low, unsigned int high) {
    return ((unsigned long long)high << 32U) | (unsigned long long)low;
}

static unsigned int media_u32_le(const unsigned char *bytes) {
    return (unsigned int)bytes[0] |
        ((unsigned int)bytes[1] << 8U) |
        ((unsigned int)bytes[2] << 16U) |
        ((unsigned int)bytes[3] << 24U);
}

static unsigned long long media_u64_le(const unsigned char *bytes) {
    unsigned int index;
    unsigned long long value = 0ULL;

    for (index = 0U; index < 8U; ++index) {
        value |= (unsigned long long)bytes[index] << (index * 8U);
    }
    return value;
}

static void media_zero(unsigned int address, unsigned int bytes) {
    volatile unsigned char *target =
        (volatile unsigned char *)(uintptr_t)address;
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        target[index] = 0U;
    }
}

static void media_copy_from_dma(void *destination, unsigned int address,
                                unsigned int bytes) {
    volatile const unsigned char *source =
        (volatile const unsigned char *)(uintptr_t)address;
    unsigned char *target = destination;
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        target[index] = source[index];
    }
}

static int media_address_set_valid(
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address) {
    return data_address != 0U &&
        (data_address & (COSMOS_NFC_PAGE_DATA_BYTES - 1U)) == 0U &&
        spare_address != 0U &&
        (spare_address & (COSMOS_NFC_PAGE_SPARE_BYTES - 1U)) == 0U &&
        completion_address != 0U &&
        (completion_address & (sizeof(unsigned int) - 1U)) == 0U &&
        status_report_address != 0U &&
        (status_report_address & (sizeof(unsigned int) - 1U)) == 0U &&
        error_info_address != 0U &&
        (error_info_address & (sizeof(unsigned int) - 1U)) == 0U;
}

static int media_command_span(const struct cosmos_nvme_ftl_media *media,
                              const struct cosmos_nvme_command *command,
                              unsigned long long *lba,
                              unsigned int *lba_count) {
    unsigned long long end;
    unsigned int count;

    if (media == 0 || command == 0 || command->namespace_id !=
            COSMOS_NVME_NAMESPACE_ID || command->data_bytes == 0U ||
        (command->data_bytes % COSMOS_FTL_NVME_BLOCK_BYTES) != 0U) {
        return COSMOS_INVALID;
    }
    count = command->data_bytes / COSMOS_FTL_NVME_BLOCK_BYTES;
    if (count == 0U || count > COSMOS_NVME_FTL_MEDIA_MAX_LBAS ||
        command->slot_tag > COSMOS_PCIE_HOST_DMA_SLOT_MASK) {
        return COSMOS_INVALID;
    }
    *lba = media_u64(command->lba_low, command->lba_high);
    end = *lba + (unsigned long long)count;
    if (end < *lba || end > media_u64(media->namespace_lba_low,
                                      media->namespace_lba_high)) {
        return COSMOS_INVALID;
    }
    *lba_count = count;
    return COSMOS_OK;
}

static int media_page_row(unsigned int ppa, unsigned int *channel,
                          unsigned int *way, unsigned int *row) {
    if (cosmos_ftl_ppa_row(ppa, channel, way, row) != COSMOS_OK) {
        return COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}

static int media_nfc_read(struct cosmos_nvme_ftl_media *media,
                          unsigned int ppa,
                          unsigned int *needs_refresh) {
    struct cosmos_nfc_io io;
    struct cosmos_nfc_ecc ecc;
    unsigned int attempt;
    unsigned int limit = media->nfc_retry_limit == 0U
        ? COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES : media->nfc_retry_limit;
    int status;

    if (needs_refresh != 0) {
        *needs_refresh = 0U;
    }
    if (media_page_row(ppa, &io.channel, &io.way, &io.row_address) !=
            COSMOS_OK) {
        return COSMOS_HW_ERROR;
    }
    io.data_address = media->data_address;
    io.spare_address = media->spare_address;
    io.error_info_address = media->error_info_address;
    io.completion_address = media->completion_address;
    io.status_report_address = media->status_report_address;
    for (attempt = 0U; attempt < limit; ++attempt) {
        status = COSMOS_NVME_FTL_MEDIA_NFC_READ(&io, &ecc);
        if (status != COSMOS_RETRY || attempt + 1U == limit) {
            if (status == COSMOS_OK && needs_refresh != 0) {
                *needs_refresh = ecc.needs_refresh != 0U ? 1U : 0U;
            }
            return status;
        }
    }
    return COSMOS_RETRY;
}

static int media_read_mapped_page(struct cosmos_nvme_ftl_media *media,
                                  unsigned int ppa, unsigned int lpn,
                                  unsigned int *needs_refresh) {
    unsigned int actual_lpn;
    unsigned int attempt;
    unsigned int limit = media->nfc_retry_limit == 0U
        ? COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES : media->nfc_retry_limit;
    unsigned long long generation;
    int status;

    if (needs_refresh != 0) {
        *needs_refresh = 0U;
    }
    if (media->ftl->backend.read_page_tag == 0) {
        return media_nfc_read(media, ppa, needs_refresh);
    }
    for (attempt = 0U; attempt < limit; ++attempt) {
        status = media->ftl->backend.read_page_tag(
            media->ftl->backend.context, ppa, &actual_lpn, &generation,
            needs_refresh);
        if (status != COSMOS_RETRY || attempt + 1U == limit) {
            return status == COSMOS_OK && actual_lpn != lpn
                ? COSMOS_HW_ERROR : status;
        }
    }
    return COSMOS_RETRY;
}

static int media_nfc_program(struct cosmos_nvme_ftl_media *media,
                             unsigned int ppa) {
    struct cosmos_nfc_io io;
    unsigned int attempt;
    unsigned int limit = media->nfc_retry_limit == 0U
        ? COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES : media->nfc_retry_limit;
    int status;

    if (media_page_row(ppa, &io.channel, &io.way, &io.row_address) !=
            COSMOS_OK) {
        return COSMOS_HW_ERROR;
    }
    io.data_address = media->data_address;
    io.spare_address = media->spare_address;
    io.error_info_address = 0U;
    io.completion_address = 0U;
    io.status_report_address = media->status_report_address;
    for (attempt = 0U; attempt < limit; ++attempt) {
        status = COSMOS_NVME_FTL_MEDIA_NFC_PROGRAM(&io);
        if (status != COSMOS_RETRY || attempt + 1U == limit) {
            return status;
        }
    }
    return COSMOS_RETRY;
}

static int media_dma(struct cosmos_nvme_ftl_media *media,
                     const struct cosmos_nvme_command *command,
                     unsigned int command_offset, unsigned int device_offset,
                     unsigned int to_device) {
    int status;

    if (command_offset > COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX ||
        device_offset > COSMOS_NVME_FTL_MEDIA_PAGE_LBAS - 1U) {
        return COSMOS_INVALID;
    }
    status = to_device
        ? COSMOS_NVME_FTL_MEDIA_DMA_H2D(
            command->slot_tag, command_offset,
            media->data_address + device_offset * COSMOS_FTL_NVME_BLOCK_BYTES)
        : COSMOS_NVME_FTL_MEDIA_DMA_D2H(
            command->slot_tag, command_offset,
            media->data_address + device_offset * COSMOS_FTL_NVME_BLOCK_BYTES);
    if (status != COSMOS_OK) {
        return status;
    }
    return COSMOS_NVME_FTL_MEDIA_DMA_POLL(
        to_device ? COSMOS_PCIE_HOST_TO_DEVICE : COSMOS_PCIE_DEVICE_TO_HOST);
}

static int media_page_prepare(struct cosmos_nvme_ftl_media *media,
                              unsigned int lpn, unsigned int page_offset,
                              unsigned int page_count, int write,
                              unsigned int *refresh_ppa) {
    unsigned int ppa;
    int status;
    int mapped = 0;

    if (refresh_ppa != 0) {
        *refresh_ppa = COSMOS_FTL_PPA_NONE;
    }
    status = cosmos_ftl_lookup(media->ftl, lpn, &ppa);
    if (status == COSMOS_OK) {
        mapped = 1;
    } else if (status != COSMOS_UNAVAILABLE) {
        return status;
    }
    if (write && page_offset == 0U && page_count ==
            COSMOS_NVME_FTL_MEDIA_PAGE_LBAS) {
        media_zero(media->spare_address, COSMOS_NFC_PAGE_SPARE_BYTES);
        return COSMOS_OK;
    }
    if (mapped) {
        unsigned int needs_refresh;

        status = media_read_mapped_page(
            media, ppa, lpn, &needs_refresh);
        if (status == COSMOS_OK && needs_refresh != 0U &&
            refresh_ppa != 0) {
            *refresh_ppa = ppa;
        }
        return status;
    }
    media_zero(media->data_address, COSMOS_NFC_PAGE_DATA_BYTES);
    media_zero(media->spare_address, COSMOS_NFC_PAGE_SPARE_BYTES);
    return COSMOS_OK;
}

static int media_commit(struct cosmos_nvme_ftl_media *media,
                        unsigned int lpn) {
    unsigned int ppa;

    cosmos_data_sync_barrier();
    return cosmos_ftl_commit_page(media->ftl, lpn, &ppa);
}

static int media_begin(struct cosmos_nvme_ftl_media *media,
                       unsigned int retry_limit) {
    if (media == 0 || media->ftl == 0 ||
        __atomic_exchange_n(&media->busy, 1U, __ATOMIC_ACQUIRE) != 0U) {
        return COSMOS_RETRY;
    }
    media->nfc_retry_limit = retry_limit;
    return COSMOS_OK;
}

static void media_end(struct cosmos_nvme_ftl_media *media) {
    __atomic_store_n(&media->busy, 0U, __ATOMIC_RELEASE);
}

static int media_rw(struct cosmos_nvme_ftl_media *media,
                    const struct cosmos_nvme_command *command,
                    int write) {
    unsigned long long lba;
    unsigned int count;
    unsigned int remaining;
    unsigned int command_offset = 0U;
    int status;

    status = media_command_span(media, command, &lba, &count);
    if (status != COSMOS_OK) {
        return status;
    }
    status = media_begin(media,
        (command->control & COSMOS_NVME_RW_LR) != 0U ? 1U :
            COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES);
    if (status != COSMOS_OK) {
        return status;
    }
    remaining = count;
    while (remaining != 0U) {
        unsigned int lpn = (unsigned int)(lba /
            COSMOS_NVME_FTL_MEDIA_PAGE_LBAS);
        unsigned int page_offset = (unsigned int)(lba %
            COSMOS_NVME_FTL_MEDIA_PAGE_LBAS);
        unsigned int page_count = COSMOS_NVME_FTL_MEDIA_PAGE_LBAS -
            page_offset;
        unsigned int refresh_ppa = COSMOS_FTL_PPA_NONE;
        unsigned int index;

        if (page_count > remaining) {
            page_count = remaining;
        }
        status = media_page_prepare(media, lpn, page_offset, page_count,
                                    write, write ? 0 : &refresh_ppa);
        if (status != COSMOS_OK) {
            break;
        }
        if (!write) {
            for (index = 0U; index < page_count; ++index) {
                status = media_dma(media, command,
                    command_offset + index, page_offset + index, 0);
                if (status != COSMOS_OK) {
                    break;
                }
            }
            if (status == COSMOS_OK &&
                refresh_ppa != COSMOS_FTL_PPA_NONE) {
                unsigned int destination;

                status = cosmos_ftl_refresh_page(
                    media->ftl, lpn, refresh_ppa, &destination);
            }
        } else {
            for (index = 0U; index < page_count; ++index) {
                status = media_dma(media, command,
                    command_offset + index, page_offset + index, 1);
                if (status != COSMOS_OK) {
                    break;
                }
            }
            if (status == COSMOS_OK) {
                status = media_commit(media, lpn);
            }
        }
        if (status != COSMOS_OK) {
            break;
        }
        lba += page_count;
        remaining -= page_count;
        command_offset += page_count;
    }
    media_end(media);
    return status;
}

static int media_zeroes(struct cosmos_nvme_ftl_media *media,
                        const struct cosmos_nvme_command *command) {
    unsigned long long lba;
    unsigned int count;
    unsigned int remaining;
    int status;

    if (media == 0 || command == 0 || command->namespace_id !=
            COSMOS_NVME_NAMESPACE_ID || command->data_bytes != 0U) {
        return COSMOS_INVALID;
    }
    count = command->nlb + 1U;
    if (count == 0U || count > COSMOS_NVME_FTL_MEDIA_MAX_LBAS ||
        command->slot_tag > COSMOS_PCIE_HOST_DMA_SLOT_MASK) {
        return COSMOS_INVALID;
    }
    lba = media_u64(command->lba_low, command->lba_high);
    if (lba + count < lba || lba + count >
            media_u64(media->namespace_lba_low,
                      media->namespace_lba_high)) {
        return COSMOS_INVALID;
    }
    status = media_begin(media,
        (command->control & COSMOS_NVME_WRITE_ZEROES_LR) != 0U ? 1U :
            COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES);
    if (status != COSMOS_OK) {
        return status;
    }
    remaining = count;
    while (remaining != 0U) {
        unsigned int lpn = (unsigned int)(lba /
            COSMOS_NVME_FTL_MEDIA_PAGE_LBAS);
        unsigned int page_offset = (unsigned int)(lba %
            COSMOS_NVME_FTL_MEDIA_PAGE_LBAS);
        unsigned int page_count = COSMOS_NVME_FTL_MEDIA_PAGE_LBAS -
            page_offset;
        unsigned int index;

        if (page_count > remaining) {
            page_count = remaining;
        }
        if ((command->control & COSMOS_NVME_WRITE_ZEROES_DEAC) != 0U &&
            page_offset == 0U && page_count ==
                COSMOS_NVME_FTL_MEDIA_PAGE_LBAS) {
            status = cosmos_ftl_discard_page(media->ftl, lpn);
        } else {
            status = media_page_prepare(media, lpn, page_offset, page_count,
                                        1, 0);
            if (status == COSMOS_OK) {
                for (index = 0U; index < page_count; ++index) {
                    media_zero(media->data_address +
                        (page_offset + index) * COSMOS_FTL_NVME_BLOCK_BYTES,
                        COSMOS_FTL_NVME_BLOCK_BYTES);
                }
                status = media_commit(media, lpn);
            }
        }
        if (status != COSMOS_OK) {
            break;
        }
        lba += page_count;
        remaining -= page_count;
    }
    media_end(media);
    return status;
}

static int media_dsm_range_valid(
    const struct cosmos_nvme_ftl_media *media,
    const struct cosmos_nvme_ftl_media_dsm_range *range) {
    unsigned long long end;

    if (range->attributes != 0U || range->length == 0U) {
        return 0;
    }
    end = range->starting_lba + (unsigned long long)range->length;
    return end >= range->starting_lba && end <=
        media_u64(media->namespace_lba_low,
                  media->namespace_lba_high);
}

int cosmos_nvme_ftl_media_init(
    struct cosmos_nvme_ftl_media *media, struct cosmos_ftl *ftl,
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address) {
    if (media == 0 || ftl == 0 || !media_address_set_valid(
            data_address, spare_address, completion_address,
            status_report_address, error_info_address)) {
        return COSMOS_INVALID;
    }
    media->ftl = ftl;
    media->namespace_lba_low = COSMOS_FTL_NAMESPACE_BLOCK_COUNT;
    media->namespace_lba_high = 0U;
    media->data_address = data_address;
    media->spare_address = spare_address;
    media->completion_address = completion_address;
    media->status_report_address = status_report_address;
    media->error_info_address = error_info_address;
    media->nfc_retry_limit = COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES;
    media->busy = 0U;
    media->media_read = cosmos_nvme_ftl_media_read;
    media->media_program = cosmos_nvme_ftl_media_program;
    media->media_flush = cosmos_nvme_ftl_media_flush;
    media->media_write_zeroes = cosmos_nvme_ftl_media_write_zeroes;
    media->media_deallocate = cosmos_nvme_ftl_media_deallocate;
    return COSMOS_OK;
}

int cosmos_nvme_ftl_media_read(
    void *context, const struct cosmos_nvme_command *command) {
    return media_rw(context, command, 0);
}

int cosmos_nvme_ftl_media_program(
    void *context, const struct cosmos_nvme_command *command) {
    return media_rw(context, command, 1);
}

int cosmos_nvme_ftl_media_flush(void *context) {
    struct cosmos_nvme_ftl_media *media = context;
    int status;

    status = media_begin(media, COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES);
    if (status != COSMOS_OK) {
        return status;
    }
    status = cosmos_ftl_flush(media->ftl);
    media_end(media);
    return status;
}

int cosmos_nvme_ftl_media_write_zeroes(
    void *context, const struct cosmos_nvme_command *command) {
    return media_zeroes(context, command);
}

int cosmos_nvme_ftl_media_deallocate(
    void *context, const struct cosmos_nvme_command *command) {
    struct cosmos_nvme_ftl_media *media = context;
    unsigned char raw[COSMOS_NVME_FTL_MEDIA_DSM_BYTES];
    unsigned int range_count;
    unsigned int bytes;
    unsigned int offset;
    int status;

    if (media == 0 || command == 0 || command->namespace_id !=
            COSMOS_NVME_NAMESPACE_ID ||
        (command->dataset_attributes & COSMOS_NVME_DSM_ATTRIBUTE_DEALLOCATE)
            == 0U ||
        (command->dataset_attributes & ~COSMOS_NVME_DSM_ATTRIBUTE_MASK) != 0U
            || command->dataset_range_count == 0U ||
        command->dataset_range_count > COSMOS_NVME_MAX_DSM_RANGES ||
        command->data_bytes != command->dataset_range_count *
            COSMOS_NVME_DSM_RANGE_BYTES ||
        command->slot_tag > COSMOS_PCIE_HOST_DMA_SLOT_MASK) {
        return COSMOS_INVALID;
    }
    range_count = command->dataset_range_count;
    bytes = command->data_bytes;
    status = media_begin(media, COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES);
    if (status != COSMOS_OK) {
        return status;
    }
    for (offset = 0U; offset < bytes; offset += COSMOS_NFC_PAGE_DATA_BYTES) {
        unsigned int chunk = bytes - offset;
        unsigned int chunk_index = offset / COSMOS_FTL_NVME_BLOCK_BYTES;

        if (chunk > COSMOS_NFC_PAGE_DATA_BYTES) {
            chunk = COSMOS_NFC_PAGE_DATA_BYTES;
        }
        status = media_dma(media, command, chunk_index, 0U, 1);
        if (status != COSMOS_OK) {
            break;
        }
        media_copy_from_dma(raw + offset, media->data_address, chunk);
    }
    if (status == COSMOS_OK) {
        unsigned int index;
        for (index = 0U; index < range_count; ++index) {
            const unsigned char *encoded = raw +
                index * COSMOS_NVME_DSM_RANGE_BYTES;
            struct cosmos_nvme_ftl_media_dsm_range range;

            range.attributes = media_u32_le(encoded);
            range.length = media_u32_le(encoded + 4U);
            range.starting_lba = media_u64_le(encoded + 8U);
            if (!media_dsm_range_valid(media, &range)) {
                status = COSMOS_INVALID;
                break;
            }
            while (range.length != 0U && status == COSMOS_OK) {
                unsigned int lpn = (unsigned int)(range.starting_lba /
                    COSMOS_NVME_FTL_MEDIA_PAGE_LBAS);
                unsigned int page_offset = (unsigned int)(
                    range.starting_lba % COSMOS_NVME_FTL_MEDIA_PAGE_LBAS);
                unsigned int page_count =
                    COSMOS_NVME_FTL_MEDIA_PAGE_LBAS - page_offset;

                if (page_count > range.length) {
                    page_count = range.length;
                }
                if (page_offset == 0U && page_count ==
                        COSMOS_NVME_FTL_MEDIA_PAGE_LBAS) {
                    status = cosmos_ftl_discard_page(media->ftl, lpn);
                } else {
                    status = media_page_prepare(media, lpn, page_offset,
                                                page_count, 1, 0);
                    if (status == COSMOS_OK) {
                        unsigned int lane;
                        for (lane = 0U; lane < page_count; ++lane) {
                            media_zero(media->data_address +
                                (page_offset + lane) *
                                    COSMOS_FTL_NVME_BLOCK_BYTES,
                                COSMOS_FTL_NVME_BLOCK_BYTES);
                        }
                        status = media_commit(media, lpn);
                    }
                }
                range.starting_lba += page_count;
                range.length -= page_count;
            }
            if (status != COSMOS_OK) {
                break;
            }
        }
    }
    media_end(media);
    return status;
}

int cosmos_nvme_ftl_media_program_data(
    void *context, unsigned int ppa, unsigned int lpn,
    unsigned long long generation) {
    (void)lpn;
    (void)generation;
    return media_nfc_program(context, ppa);
}

int cosmos_nvme_ftl_media_copy_data(
    void *context, unsigned int source_ppa, unsigned int destination_ppa,
    unsigned int lpn, unsigned long long generation) {
    struct cosmos_nvme_ftl_media *media = context;
    int status;

    (void)lpn;
    (void)generation;
    status = media_begin(media, COSMOS_NVME_FTL_MEDIA_DEFAULT_RETRIES);
    if (status != COSMOS_OK) {
        return status;
    }
    status = media_nfc_read(media, source_ppa, 0);
    if (status == COSMOS_OK) {
        cosmos_data_sync_barrier();
        status = media_nfc_program(media, destination_ppa);
    }
    media_end(media);
    return status;
}
