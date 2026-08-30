#include "cosmos_ftl_nfc_backend.h"

#if defined(COSMOS_FTL_NFC_BACKEND_PURE_POLICY)
#include "cosmos_ftl_nfc_backend_policy.h"
#endif

#include <stdint.h>

#define COSMOS_FTL_NFC_MAGIC 0x43464E31U
#define COSMOS_FTL_NFC_HEADER_CRC_BYTES 32U
#define COSMOS_FTL_NFC_SUPERBLOCK_BYTES 40U
#define COSMOS_FTL_NFC_DATA_TAG_BYTES COSMOS_FTL_NFC_HEADER_BYTES

#ifndef COSMOS_FTL_NFC_METADATA_PAGE_LIMIT
#define COSMOS_FTL_NFC_METADATA_PAGE_LIMIT \
    COSMOS_FTL_NFC_METADATA_PAGE_COUNT
#endif

enum metadata_page_state {
    METADATA_PAGE_BLANK = 0,
    METADATA_PAGE_VALID = 1,
    METADATA_PAGE_TORN = 2,
    METADATA_PAGE_RETRY = 3,
    METADATA_PAGE_IO_ERROR = 4
};

struct media_header {
    unsigned int magic;
    unsigned int version;
    unsigned int type;
    unsigned long long logical_index;
    unsigned long long generation;
    unsigned int payload_length;
    unsigned int payload_crc;
};

struct checkpoint_location {
    unsigned int segment;
    struct cosmos_ftl_checkpoint checkpoint;
};

/* The default path preserves the pre-migration C behavior for existing
 * standalone firmware/test links.  The isolated wiring patch enables the
 * pure-Simple scalar owner without moving any hardware operation out of C. */
#if defined(COSMOS_FTL_NFC_BACKEND_PURE_POLICY)
#define backend_policy_checkpoint_total_bytes \
    cosmos_ftl_nfc_backend_policy_checkpoint_total_bytes
#define backend_policy_header_prefix_status \
    cosmos_ftl_nfc_backend_policy_header_prefix_status
#define backend_policy_payload_length_status \
    cosmos_ftl_nfc_backend_policy_payload_length_status
#define backend_policy_read_io_state \
    cosmos_ftl_nfc_backend_policy_read_io_state
#define backend_policy_read_content_state \
    cosmos_ftl_nfc_backend_policy_read_content_state
#define backend_policy_write_faults \
    cosmos_ftl_nfc_backend_policy_write_faults
#define backend_policy_superblock_status \
    cosmos_ftl_nfc_backend_policy_superblock_status
#define backend_policy_mounted_status \
    cosmos_ftl_nfc_backend_policy_mounted_status
#define backend_policy_checkpoint_candidate_better \
    cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better
#define backend_policy_page_blank_status \
    cosmos_ftl_nfc_backend_policy_page_blank_status
#define backend_policy_recycle_status \
    cosmos_ftl_nfc_backend_policy_recycle_status
#define backend_policy_next_journal_index \
    cosmos_ftl_nfc_backend_policy_next_journal_index
#define backend_policy_first_journal_index \
    cosmos_ftl_nfc_backend_policy_first_journal_index
#define backend_policy_journal_pages_normalized \
    cosmos_ftl_nfc_backend_policy_journal_pages_normalized
#define backend_policy_journal_pages_valid \
    cosmos_ftl_nfc_backend_policy_journal_pages_valid
#define backend_policy_checkpoint_data_pages \
    cosmos_ftl_nfc_backend_policy_checkpoint_data_pages
#define backend_policy_checkpoint_slot_pages \
    cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages
#define backend_policy_journal_start_page \
    cosmos_ftl_nfc_backend_policy_journal_start_page
#define backend_policy_layout_valid \
    cosmos_ftl_nfc_backend_policy_layout_valid
#define backend_policy_journal_page \
    cosmos_ftl_nfc_backend_policy_journal_page
#define backend_policy_journal_append_admit \
    cosmos_ftl_nfc_backend_policy_journal_append_admit
#define backend_policy_journal_append_result \
    cosmos_ftl_nfc_backend_policy_journal_append_result
#define backend_policy_journal_read_admit \
    cosmos_ftl_nfc_backend_policy_journal_read_admit
#define backend_policy_journal_next_after_read \
    cosmos_ftl_nfc_backend_policy_journal_next_after_read
#define backend_policy_journal_record_valid \
    cosmos_ftl_nfc_backend_policy_journal_record_valid
#define backend_policy_journal_block_fully_dead \
    cosmos_ftl_nfc_backend_policy_journal_block_fully_dead
#define backend_policy_journal_trim_status \
    cosmos_ftl_nfc_backend_policy_journal_trim_status
#else
static unsigned int backend_policy_checkpoint_total_bytes(
    unsigned int l2p_count, unsigned int block_count) {
    unsigned long long total = (unsigned long long)l2p_count * 4ULL +
        (unsigned long long)block_count * 8ULL;
    return total > 0xFFFFFFFFULL ? 0U : (unsigned int)total;
}

static int backend_policy_header_prefix_status(
    unsigned int magic, unsigned int version, unsigned int header_crc,
    unsigned int expected_header_crc) {
    return magic == COSMOS_FTL_NFC_MAGIC &&
        version == COSMOS_FTL_NFC_FORMAT_VERSION &&
        header_crc == expected_header_crc ? COSMOS_OK : COSMOS_INVALID;
}

static int backend_policy_payload_length_status(unsigned int payload_length) {
    return payload_length <= COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES ?
        COSMOS_OK : COSMOS_INVALID;
}

static int backend_policy_read_io_state(int status) {
    if (status == COSMOS_RETRY) {
        return METADATA_PAGE_RETRY;
    }
    return status == COSMOS_OK ? METADATA_PAGE_VALID : METADATA_PAGE_IO_ERROR;
}

static int backend_policy_read_content_state(
    unsigned int all_ff, int header_status, unsigned int spare_header,
    int payload_status) {
    if (all_ff != 0U) {
        return METADATA_PAGE_BLANK;
    }
    if (header_status != COSMOS_OK ||
        (spare_header == 0U && payload_status != COSMOS_OK)) {
        return METADATA_PAGE_TORN;
    }
    return METADATA_PAGE_VALID;
}

static unsigned int backend_policy_write_faults(int status) {
    return status == COSMOS_TIMEOUT || status == COSMOS_COMPLETION_UNCERTAIN;
}

static int backend_policy_superblock_status(
    int page_state, unsigned int page_type, unsigned long long logical_index,
    unsigned int payload_length, unsigned int payload_valid) {
    if (page_state == METADATA_PAGE_RETRY) {
        return COSMOS_RETRY;
    }
    if (page_state != METADATA_PAGE_VALID ||
        page_type != COSMOS_FTL_NFC_PAGE_SUPERBLOCK || logical_index != 0ULL ||
        payload_length != COSMOS_FTL_NFC_SUPERBLOCK_BYTES ||
        payload_valid == 0U) {
        return page_state == METADATA_PAGE_BLANK ? COSMOS_UNAVAILABLE :
            COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}

static int backend_policy_mounted_status(
    unsigned int backend_present, unsigned int mounted,
    unsigned int faulted) {
    return backend_present != 0U && mounted != 0U && faulted == 0U ?
        COSMOS_OK : COSMOS_UNAVAILABLE;
}

static unsigned int backend_policy_checkpoint_candidate_better(
    unsigned int have_latest, unsigned long long candidate_generation,
    unsigned long long latest_generation, unsigned int candidate_segment,
    unsigned int latest_segment) {
    return have_latest == 0U || candidate_generation > latest_generation ||
        (candidate_generation == latest_generation &&
         candidate_segment > latest_segment);
}

static int backend_policy_page_blank_status(int page_state) {
    if (page_state == METADATA_PAGE_BLANK) {
        return COSMOS_OK;
    }
    if (page_state == METADATA_PAGE_RETRY) {
        return COSMOS_RETRY;
    }
    return page_state == METADATA_PAGE_IO_ERROR ? COSMOS_HW_ERROR :
        COSMOS_INVALID;
}

static int backend_policy_recycle_status(
    unsigned int slot, unsigned int checkpoint_valid_mask) {
    if (slot >= 2U ||
        (checkpoint_valid_mask & (1U << (slot ^ 1U))) == 0U) {
        return COSMOS_UNAVAILABLE;
    }
    return COSMOS_OK;
}

static unsigned long long backend_policy_next_journal_index(
    unsigned long long current, unsigned long long checkpoint_index) {
    return checkpoint_index > current ? checkpoint_index : current;
}

static unsigned long long backend_policy_first_journal_index(
    unsigned int checkpoint_valid_mask, unsigned long long current,
    unsigned long long checkpoint_index_0,
    unsigned long long checkpoint_index_1) {
    unsigned long long first;
    if (checkpoint_valid_mask != 3U) {
        return current;
    }
    first = checkpoint_index_0 < checkpoint_index_1 ? checkpoint_index_0 :
        checkpoint_index_1;
    return first > current ? first : current;
}

static unsigned long long backend_policy_journal_pages_normalized(
    unsigned long long journal_pages) {
    return journal_pages == 0ULL ? COSMOS_FTL_NFC_DEFAULT_JOURNAL_PAGES :
        journal_pages;
}

static unsigned int backend_policy_journal_capacity_valid(
    unsigned long long capacity) {
    if (capacity == 0ULL) {
        return 0U;
    }
    return (capacity & (capacity - 1ULL)) == 0ULL;
}

static unsigned int backend_policy_journal_pages_valid(
    unsigned long long journal_pages) {
    return journal_pages - 1ULL < COSMOS_FTL_NFC_MAX_JOURNAL_PAGES &&
        (journal_pages & (journal_pages - 1ULL)) == 0ULL &&
        journal_pages % COSMOS_FTL_PAGES_PER_BLOCK == 0ULL;
}

static unsigned int backend_policy_checkpoint_data_pages(
    unsigned int total_bytes) {
    return (unsigned int)(((unsigned long long)total_bytes +
        COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES - 1ULL) /
        COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES);
}

static unsigned int backend_policy_checkpoint_slot_pages(
    unsigned long long journal_pages, unsigned int metadata_page_limit) {
    unsigned int available;
    if (metadata_page_limit < COSMOS_FTL_PAGES_PER_BLOCK ||
        journal_pages > metadata_page_limit - COSMOS_FTL_PAGES_PER_BLOCK) {
        return 0U;
    }
    available = metadata_page_limit - COSMOS_FTL_PAGES_PER_BLOCK;
    available -= (unsigned int)journal_pages;
    return (available / 2U / COSMOS_FTL_PAGES_PER_BLOCK) *
        COSMOS_FTL_PAGES_PER_BLOCK;
}

static unsigned int backend_policy_journal_start_page(
    unsigned int checkpoint_slot_pages) {
    return COSMOS_FTL_PAGES_PER_BLOCK + 2U * checkpoint_slot_pages;
}

static unsigned int backend_policy_layout_valid(
    unsigned int journal_start_page, unsigned long long journal_pages,
    unsigned int checkpoint_slot_pages,
    unsigned int checkpoint_record_pages, unsigned int metadata_page_limit) {
    return journal_start_page < metadata_page_limit &&
        metadata_page_limit - journal_start_page >=
            journal_pages &&
        checkpoint_slot_pages >= checkpoint_record_pages;
}

static unsigned int backend_policy_journal_page(
    unsigned int journal_start_page, unsigned long long journal_capacity,
    unsigned long long index) {
    if (backend_policy_journal_capacity_valid(journal_capacity) == 0U) {
        return 0U;
    }
    return journal_start_page +
        (unsigned int)(index & (journal_capacity - 1ULL));
}

static unsigned int backend_policy_journal_append_admit(
    int mounted_status, unsigned long long index,
    unsigned long long first_index, unsigned long long capacity,
    unsigned long long next_index) {
    return backend_policy_journal_capacity_valid(capacity) != 0U &&
        mounted_status == COSMOS_OK && index >= first_index &&
        index - first_index < capacity &&
        (next_index == 0ULL || index == next_index);
}

static unsigned int backend_policy_journal_append_result(int status) {
    if (status == COSMOS_OK) {
        return COSMOS_FTL_APPEND_COMMITTED;
    }
    if (status == COSMOS_TIMEOUT || status == COSMOS_COMPLETION_UNCERTAIN) {
        return COSMOS_FTL_APPEND_AMBIGUOUS;
    }
    return status == COSMOS_UNAVAILABLE || status == COSMOS_RETRY ?
        COSMOS_FTL_APPEND_NOT_COMMITTED : COSMOS_FTL_APPEND_HARD_FAILED;
}

static unsigned int backend_policy_journal_read_admit(
    int mounted_status, unsigned long long index,
    unsigned long long first_index, unsigned long long capacity) {
    return backend_policy_journal_capacity_valid(capacity) != 0U &&
        mounted_status == COSMOS_OK && index >= first_index &&
        index - first_index < capacity;
}

static unsigned long long backend_policy_journal_next_after_read(
    unsigned long long index, unsigned long long current) {
    if (index != ~0ULL && index + 1ULL > current) {
        return index + 1ULL;
    }
    return current;
}

static unsigned int backend_policy_journal_record_valid(
    unsigned long long sequence, unsigned long long expected_sequence,
    unsigned int magic, unsigned int crc, unsigned int expected_crc) {
    return sequence == expected_sequence && magic == COSMOS_FTL_MAGIC &&
        crc == expected_crc;
}

static unsigned int backend_policy_journal_block_fully_dead(
    unsigned long long capacity, unsigned long long next_index,
    unsigned int block, unsigned long long first_live) {
    unsigned long long candidate;
    if (backend_policy_journal_capacity_valid(capacity) == 0U) {
        return 0U;
    }
    candidate = (next_index & ~(capacity - 1ULL)) +
        (unsigned long long)block * COSMOS_FTL_PAGES_PER_BLOCK;
    if (candidate >= next_index) {
        if (candidate < capacity) {
            return 0U;
        }
        candidate -= capacity;
    }
    return candidate <= ~0ULL - COSMOS_FTL_PAGES_PER_BLOCK &&
        candidate + COSMOS_FTL_PAGES_PER_BLOCK <= first_live;
}

static int backend_policy_journal_trim_status(
    int mounted_status, unsigned int checkpoint_valid_mask,
    unsigned long long first_live, unsigned long long first_index,
    unsigned long long capacity, unsigned long long checkpoint_index_0,
    unsigned long long checkpoint_index_1) {
    unsigned long long watermark;
    if (backend_policy_journal_capacity_valid(capacity) == 0U ||
        mounted_status != COSMOS_OK ||
        (checkpoint_valid_mask & 3U) != 3U || first_live < first_index ||
        first_live - first_index > capacity) {
        return COSMOS_UNAVAILABLE;
    }
    watermark = checkpoint_index_0 < checkpoint_index_1 ?
        checkpoint_index_0 : checkpoint_index_1;
    return first_live > watermark ? COSMOS_INVALID : COSMOS_OK;
}
#endif

static void *nfc_memset(void *destination, unsigned char value,
                        unsigned int bytes) {
    unsigned char *out = destination;
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        out[index] = value;
    }
    return destination;
}

static void *nfc_memcpy(void *destination, const void *source,
                        unsigned int bytes) {
    unsigned char *out = destination;
    const unsigned char *in = source;
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        out[index] = in[index];
    }
    return destination;
}

static void put_u16(unsigned char *out, unsigned int value) {
    out[0] = (unsigned char)value;
    out[1] = (unsigned char)(value >> 8U);
}

static void put_u32(unsigned char *out, unsigned int value) {
    unsigned int byte;

    for (byte = 0U; byte < 4U; ++byte) {
        out[byte] = (unsigned char)(value >> (byte * 8U));
    }
}

static void put_u64(unsigned char *out, unsigned long long value) {
    unsigned int byte;

    for (byte = 0U; byte < 8U; ++byte) {
        out[byte] = (unsigned char)(value >> (byte * 8U));
    }
}

static unsigned int get_u16(const unsigned char *in) {
    return (unsigned int)in[0] | ((unsigned int)in[1] << 8U);
}

static unsigned int get_u32(const unsigned char *in) {
    unsigned int value = 0U;
    unsigned int byte;

    for (byte = 0U; byte < 4U; ++byte) {
        value |= (unsigned int)in[byte] << (byte * 8U);
    }
    return value;
}

static unsigned long long get_u64(const unsigned char *in) {
    unsigned long long value = 0ULL;
    unsigned int byte;

    for (byte = 0U; byte < 8U; ++byte) {
        value |= (unsigned long long)in[byte] << (byte * 8U);
    }
    return value;
}

static unsigned char *data_buffer(
    const struct cosmos_ftl_nfc_backend *backend) {
    return (unsigned char *)(uintptr_t)backend->dma.metadata_address;
}

static unsigned char *payload_buffer(
    const struct cosmos_ftl_nfc_backend *backend) {
    return (unsigned char *)(uintptr_t)backend->dma.payload_address;
}

static unsigned char *spare_buffer(
    const struct cosmos_ftl_nfc_backend *backend) {
    return (unsigned char *)(uintptr_t)backend->dma.spare_address;
}

static int dma_valid(const struct cosmos_ftl_nfc_dma *dma) {
    return dma != 0 && dma->metadata_address != 0U &&
        dma->payload_address != 0U &&
        dma->metadata_address != dma->payload_address &&
        dma->spare_address != 0U && dma->error_info_address != 0U &&
        dma->completion_address != 0U && dma->status_report_address != 0U &&
        (dma->metadata_address & (COSMOS_NFC_PAGE_DATA_BYTES - 1U)) == 0U &&
        (dma->payload_address & (COSMOS_NFC_PAGE_DATA_BYTES - 1U)) == 0U &&
        (dma->spare_address & 3U) == 0U &&
        (dma->error_info_address & 3U) == 0U &&
        (dma->completion_address & 3U) == 0U &&
        (dma->status_report_address & 3U) == 0U;
}

static int default_read_page(void *context, const struct cosmos_nfc_io *io,
                             struct cosmos_nfc_ecc *ecc) {
    (void)context;
    return cosmos_nfc_read_page(io, ecc);
}

static int default_program_page(void *context,
                                const struct cosmos_nfc_io *io) {
    (void)context;
    return cosmos_nfc_program_page(io);
}

static int default_erase_block(void *context, unsigned int channel,
                               unsigned int way, unsigned int row,
                               unsigned int status_report_address) {
    (void)context;
    return cosmos_nfc_erase_block(
        channel, way, row, status_report_address);
}

static int ppa_io(const struct cosmos_ftl_nfc_backend *backend,
                  unsigned int ppa, struct cosmos_nfc_io *io) {
    unsigned int channel;
    unsigned int way;
    unsigned int row;

    if (backend == 0 || io == 0 ||
        cosmos_ftl_ppa_row(ppa, &channel, &way, &row) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    io->channel = channel;
    io->way = way;
    io->row_address = row;
    io->data_address = backend->dma.metadata_address;
    io->spare_address = backend->dma.spare_address;
    io->error_info_address = backend->dma.error_info_address;
    io->completion_address = backend->dma.completion_address;
    io->status_report_address = backend->dma.status_report_address;
    return COSMOS_OK;
}

static int data_ppa_io(const struct cosmos_ftl_nfc_backend *backend,
                       unsigned int ppa, struct cosmos_nfc_io *io) {
    int status = ppa_io(backend, ppa, io);

    if (status == COSMOS_OK) {
        io->data_address = backend->dma.payload_address;
    }
    return status;
}

static int metadata_ppa(unsigned int page, unsigned int *ppa) {
    unsigned int lane;
    unsigned int block;
    unsigned int die;
    unsigned int lun;
    unsigned int in_lane;

    if (ppa == 0 || page >= COSMOS_FTL_NFC_METADATA_PAGE_LIMIT) {
        return COSMOS_INVALID;
    }
    lane = page / COSMOS_FTL_NFC_METADATA_PAGES_PER_LANE;
    in_lane = page % COSMOS_FTL_NFC_METADATA_PAGES_PER_LANE;
    block = in_lane / COSMOS_FTL_PAGES_PER_BLOCK;
    die = lane / COSMOS_FTL_LUN_COUNT;
    lun = lane % COSMOS_FTL_LUN_COUNT;
    return cosmos_ftl_ppa_encode(
        die, lun, block, in_lane % COSMOS_FTL_PAGES_PER_BLOCK, ppa);
}

static void encode_header(unsigned char *out, unsigned int type,
                          unsigned long long logical_index,
                          unsigned long long generation,
                          const unsigned char *payload,
                          unsigned int payload_length) {
    unsigned int header_crc;

    nfc_memset(out, 0U, COSMOS_FTL_NFC_HEADER_BYTES);
    put_u32(out + 0U, COSMOS_FTL_NFC_MAGIC);
    put_u16(out + 4U, COSMOS_FTL_NFC_FORMAT_VERSION);
    put_u16(out + 6U, type);
    put_u64(out + 8U, logical_index);
    put_u64(out + 16U, generation);
    put_u32(out + 24U, payload_length);
    put_u32(out + 28U, cosmos_ftl_crc32(payload, payload_length));
    header_crc = cosmos_ftl_crc32(out, COSMOS_FTL_NFC_HEADER_CRC_BYTES);
    put_u32(out + 32U, header_crc);
}

static int decode_header(const unsigned char *in, struct media_header *header) {
    if (in == 0 || header == 0) {
        return COSMOS_INVALID;
    }
    if (backend_policy_header_prefix_status(
            get_u32(in + 0U), get_u16(in + 4U), get_u32(in + 32U),
            cosmos_ftl_crc32(in, COSMOS_FTL_NFC_HEADER_CRC_BYTES)) !=
            COSMOS_OK) {
        return COSMOS_INVALID;
    }
    header->magic = get_u32(in + 0U);
    header->version = get_u16(in + 4U);
    header->type = get_u16(in + 6U);
    header->logical_index = get_u64(in + 8U);
    header->generation = get_u64(in + 16U);
    header->payload_length = get_u32(in + 24U);
    header->payload_crc = get_u32(in + 28U);
    if (backend_policy_payload_length_status(header->payload_length) !=
            COSMOS_OK) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}

static int header_payload_valid(const unsigned char *page,
                                const struct media_header *header) {
    return cosmos_ftl_crc32(
        page + COSMOS_FTL_NFC_HEADER_BYTES,
        header->payload_length) == header->payload_crc ? COSMOS_OK :
        COSMOS_INVALID;
}

static int read_page_state(struct cosmos_ftl_nfc_backend *backend,
                           unsigned int ppa, unsigned int spare_header,
                           struct media_header *header,
                           unsigned int *needs_refresh) {
    struct cosmos_nfc_io io;
    struct cosmos_nfc_ecc ecc;
    unsigned char *data;
    unsigned char *spare;
    int status;
    unsigned int index;
    int io_state;
    int payload_status = COSMOS_OK;
    int all_ff = 1;

    if (needs_refresh != 0) {
        *needs_refresh = 0U;
    }
    if ((spare_header != 0U
            ? data_ppa_io(backend, ppa, &io)
            : ppa_io(backend, ppa, &io)) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    data = spare_header != 0U
        ? payload_buffer(backend) : data_buffer(backend);
    spare = spare_buffer(backend);
    nfc_memset(data, 0xFFU, COSMOS_NFC_PAGE_DATA_BYTES);
    nfc_memset(spare, 0xFFU, COSMOS_NFC_PAGE_SPARE_BYTES);
    status = backend->nfc.read_page(
        backend->nfc.context, &io, &ecc);
    io_state = backend_policy_read_io_state(status);
    if (io_state != METADATA_PAGE_VALID) {
        return io_state;
    }
    if (needs_refresh != 0) {
        *needs_refresh = ecc.needs_refresh != 0U ? 1U : 0U;
    }
    for (index = 0U; index < COSMOS_NFC_PAGE_DATA_BYTES; ++index) {
        if (data[index] != 0xFFU) {
            all_ff = 0;
            break;
        }
    }
    if (all_ff) {
        for (index = 0U; index < COSMOS_NFC_PAGE_SPARE_BYTES; ++index) {
            if (spare[index] != 0xFFU) {
                all_ff = 0;
                break;
            }
        }
    }
    if (all_ff) {
        return backend_policy_read_content_state(
            1U, COSMOS_INVALID, spare_header, COSMOS_INVALID);
    }
    status = decode_header(
        spare_header != 0U ? spare : data, header);
    if (status == COSMOS_OK && spare_header == 0U) {
        payload_status = header_payload_valid(data, header);
    }
    return backend_policy_read_content_state(
        0U, status, spare_header, payload_status);
}

static int write_page(struct cosmos_ftl_nfc_backend *backend,
                      unsigned int ppa, unsigned int type,
                      unsigned long long logical_index,
                      unsigned long long generation,
                      const unsigned char *payload,
                      unsigned int payload_length, unsigned int spare_header) {
    struct cosmos_nfc_io io;
    unsigned char *data;
    unsigned char *spare;
    int status;

    if (payload_length > COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES ||
        (spare_header != 0U
            ? data_ppa_io(backend, ppa, &io)
            : ppa_io(backend, ppa, &io)) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    data = data_buffer(backend);
    spare = spare_buffer(backend);
    if (spare_header != 0U) {
        nfc_memset(spare, 0xFFU, COSMOS_NFC_PAGE_SPARE_BYTES);
        encode_header(spare, type, logical_index, generation,
                      payload, payload_length);
    } else {
        if (payload != data + COSMOS_FTL_NFC_HEADER_BYTES) {
            nfc_memset(data, 0xFFU, COSMOS_NFC_PAGE_DATA_BYTES);
            encode_header(data, type, logical_index, generation,
                          payload, payload_length);
            nfc_memcpy(data + COSMOS_FTL_NFC_HEADER_BYTES,
                       payload, payload_length);
        } else {
            encode_header(data, type, logical_index, generation,
                          payload, payload_length);
        }
        nfc_memset(spare, 0xFFU, COSMOS_NFC_PAGE_SPARE_BYTES);
    }
    status = backend->nfc.program_page(
        backend->nfc.context, &io);
    if (backend_policy_write_faults(status) != 0U) {
        backend->faulted = 1U;
    }
    return status;
}

static int read_metadata_page(struct cosmos_ftl_nfc_backend *backend,
                              unsigned int page, struct media_header *header) {
    unsigned int ppa;

    if (metadata_ppa(page, &ppa) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    return read_page_state(backend, ppa, 0U, header, 0);
}

static unsigned int checkpoint_total_bytes(
    unsigned int l2p_count, unsigned int block_count) {
    return backend_policy_checkpoint_total_bytes(l2p_count, block_count);
}

static unsigned char checkpoint_byte(
    const unsigned int *l2p, const struct cosmos_ftl_block *blocks,
    unsigned int l2p_count, unsigned int offset) {
    unsigned int l2p_bytes = l2p_count * 4U;
    unsigned int block_offset;
    unsigned int block;

    if (offset < l2p_bytes) {
        return (unsigned char)(l2p[offset / 4U] >> ((offset % 4U) * 8U));
    }
    block_offset = offset - l2p_bytes;
    block = block_offset / 8U;
    block_offset %= 8U;
    if (block_offset == 0U) {
        return (unsigned char)blocks[block].valid_pages;
    }
    if (block_offset == 1U) {
        return (unsigned char)(blocks[block].valid_pages >> 8U);
    }
    if (block_offset == 2U) {
        return (unsigned char)blocks[block].erase_count;
    }
    if (block_offset == 3U) {
        return (unsigned char)(blocks[block].erase_count >> 8U);
    }
    if (block_offset == 4U) {
        return blocks[block].bad;
    }
    if (block_offset == 5U) {
        return blocks[block].state;
    }
    if (block_offset == 6U) {
        return blocks[block].next_page;
    }
    return blocks[block].reserved;
}

static void checkpoint_put_chunk(
    unsigned char *out, const unsigned int *l2p,
    const struct cosmos_ftl_block *blocks, unsigned int l2p_count,
    unsigned int offset, unsigned int bytes) {
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        out[index] = checkpoint_byte(
            l2p, blocks, l2p_count, offset + index);
    }
}

static void checkpoint_get_chunk(
    const unsigned char *in, unsigned int *l2p,
    struct cosmos_ftl_block *blocks, unsigned int l2p_count,
    unsigned int offset, unsigned int bytes) {
    unsigned int index;
    unsigned int l2p_bytes = l2p_count * 4U;

    for (index = 0U; index < bytes; ++index) {
        unsigned int position = offset + index;
        unsigned int value = in[index];
        unsigned int member;
        unsigned int block;

        if (position < l2p_bytes) {
            member = position % 4U;
            l2p[position / 4U] =
                (l2p[position / 4U] & ~(0xFFU << (member * 8U))) |
                (value << (member * 8U));
            continue;
        }
        position -= l2p_bytes;
        block = position / 8U;
        member = position % 8U;
        if (member < 2U) {
            unsigned short old = blocks[block].valid_pages;
            old = (unsigned short)((old & ~(0xFFU << (member * 8U))) |
                                   (value << (member * 8U)));
            blocks[block].valid_pages = old;
        } else if (member < 4U) {
            unsigned short old = blocks[block].erase_count;
            member -= 2U;
            old = (unsigned short)((old & ~(0xFFU << (member * 8U))) |
                                   (value << (member * 8U)));
            blocks[block].erase_count = old;
        } else if (member == 4U) {
            blocks[block].bad = (unsigned char)value;
        } else if (member == 5U) {
            blocks[block].state = (unsigned char)value;
        } else if (member == 6U) {
            blocks[block].next_page = (unsigned char)value;
        } else {
            blocks[block].reserved = (unsigned char)value;
        }
    }
}

static void encode_ftl_checkpoint(
    unsigned char *out, const struct cosmos_ftl_checkpoint *checkpoint) {
    put_u32(out + 0U, checkpoint->magic);
    put_u32(out + 4U, checkpoint->version);
    put_u64(out + 8U, checkpoint->generation);
    put_u64(out + 16U, checkpoint->journal_index);
    put_u32(out + 24U, checkpoint->l2p_count);
    put_u32(out + 28U, checkpoint->block_count);
    put_u32(out + 32U, checkpoint->allocation_lane);
    put_u32(out + 36U, checkpoint->journal_crc);
    put_u32(out + 40U, checkpoint->l2p_crc);
    put_u32(out + 44U, checkpoint->block_crc);
    put_u32(out + 48U, checkpoint->header_crc);
    nfc_memset(out + 52U, 0U, 4U);
}

static void decode_ftl_checkpoint(
    const unsigned char *in, struct cosmos_ftl_checkpoint *checkpoint) {
    checkpoint->magic = get_u32(in + 0U);
    checkpoint->version = get_u32(in + 4U);
    checkpoint->generation = get_u64(in + 8U);
    checkpoint->journal_index = get_u64(in + 16U);
    checkpoint->l2p_count = get_u32(in + 24U);
    checkpoint->block_count = get_u32(in + 28U);
    checkpoint->allocation_lane = get_u32(in + 32U);
    checkpoint->journal_crc = get_u32(in + 36U);
    checkpoint->l2p_crc = get_u32(in + 40U);
    checkpoint->block_crc = get_u32(in + 44U);
    checkpoint->header_crc = get_u32(in + 48U);
}

static void encode_journal(
    unsigned char *out, const struct cosmos_ftl_journal_record *record) {
    put_u32(out + 0U, record->magic);
    put_u32(out + 4U, record->type);
    put_u64(out + 8U, record->sequence);
    put_u64(out + 16U, record->generation);
    put_u32(out + 24U, record->lpn);
    put_u32(out + 28U, record->new_ppa);
    put_u32(out + 32U, record->old_ppa);
    put_u32(out + 36U, record->block_index);
    put_u32(out + 40U, record->previous_crc);
    put_u32(out + 44U, record->crc);
}

static void decode_journal(
    const unsigned char *in, struct cosmos_ftl_journal_record *record) {
    record->magic = get_u32(in + 0U);
    record->type = get_u32(in + 4U);
    record->sequence = get_u64(in + 8U);
    record->generation = get_u64(in + 16U);
    record->lpn = get_u32(in + 24U);
    record->new_ppa = get_u32(in + 28U);
    record->old_ppa = get_u32(in + 32U);
    record->block_index = get_u32(in + 36U);
    record->previous_crc = get_u32(in + 40U);
    record->crc = get_u32(in + 44U);
}

static int superblock_payload(const struct cosmos_ftl_nfc_backend *backend,
                              unsigned char *payload) {
    put_u32(payload + 0U, COSMOS_FTL_NFC_FORMAT_VERSION);
    put_u32(payload + 4U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN);
    put_u32(payload + 8U, COSMOS_FTL_PAGES_PER_BLOCK);
    put_u32(payload + 12U, COSMOS_NFC_PAGE_DATA_BYTES);
    put_u32(payload + 16U, COSMOS_NFC_PAGE_SPARE_BYTES);
    put_u32(payload + 20U, COSMOS_FTL_NFC_METADATA_PAGE_LIMIT);
    put_u32(payload + 24U, backend->checkpoint_slot_pages);
    put_u32(payload + 28U, backend->checkpoint_record_pages);
    put_u32(payload + 32U, backend->journal_start_page);
    put_u32(payload + 36U, (unsigned int)backend->journal_capacity);
    return COSMOS_OK;
}

static int superblock_valid(const struct cosmos_ftl_nfc_backend *backend,
                            const unsigned char *payload) {
    return get_u32(payload + 0U) == COSMOS_FTL_NFC_FORMAT_VERSION &&
        get_u32(payload + 4U) == COSMOS_FTL_METADATA_BLOCKS_PER_LUN &&
        get_u32(payload + 8U) == COSMOS_FTL_PAGES_PER_BLOCK &&
        get_u32(payload + 12U) == COSMOS_NFC_PAGE_DATA_BYTES &&
        get_u32(payload + 16U) == COSMOS_NFC_PAGE_SPARE_BYTES &&
        get_u32(payload + 20U) == COSMOS_FTL_NFC_METADATA_PAGE_LIMIT &&
        get_u32(payload + 24U) == backend->checkpoint_slot_pages &&
        get_u32(payload + 28U) == backend->checkpoint_record_pages &&
        get_u32(payload + 32U) == backend->journal_start_page &&
        get_u32(payload + 36U) == (unsigned int)backend->journal_capacity;
}

static int read_superblock(struct cosmos_ftl_nfc_backend *backend) {
    struct media_header header;
    unsigned int ppa;
    unsigned int payload_valid = 0U;
    int state;

    if (metadata_ppa(0U, &ppa) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    state = read_page_state(backend, ppa, 0U, &header, 0);
    if (state == METADATA_PAGE_VALID) {
        payload_valid = superblock_valid(
            backend, data_buffer(backend) + COSMOS_FTL_NFC_HEADER_BYTES) ?
            1U : 0U;
        return backend_policy_superblock_status(
            state, header.type, header.logical_index,
            header.payload_length, payload_valid);
    }
    return backend_policy_superblock_status(state, 0U, 0ULL, 0U, 0U);
}

static int require_mounted(struct cosmos_ftl_nfc_backend *backend) {
    return backend_policy_mounted_status(
        backend != 0 ? 1U : 0U,
        backend != 0 ? backend->mounted : 0U,
        backend != 0 ? backend->faulted : 0U);
}

static unsigned int checkpoint_segments(
    const struct cosmos_ftl_nfc_backend *backend) {
    return backend->checkpoint_slot_pages /
        backend->checkpoint_record_pages;
}

static unsigned int checkpoint_start_page(
    const struct cosmos_ftl_nfc_backend *backend, unsigned int slot) {
    return COSMOS_FTL_PAGES_PER_BLOCK + slot * backend->checkpoint_slot_pages;
}

static int find_checkpoint(
    struct cosmos_ftl_nfc_backend *backend, unsigned int slot,
    struct checkpoint_location *latest, unsigned int *free_segment) {
    unsigned int segments;
    unsigned int segment;
    unsigned int have_latest = 0U;

    if (slot >= 2U || latest == 0 || free_segment == 0) {
        return COSMOS_INVALID;
    }
    segments = checkpoint_segments(backend);
    *free_segment = segments;
    for (segment = 0U; segment < segments; ++segment) {
        struct media_header header;
        unsigned int page = checkpoint_start_page(backend, slot) +
            segment * backend->checkpoint_record_pages;
        int state = read_metadata_page(backend, page, &header);

        if (state == METADATA_PAGE_RETRY) {
            return COSMOS_RETRY;
        }
        if (state == METADATA_PAGE_IO_ERROR) {
            return COSMOS_HW_ERROR;
        }
        if (state == METADATA_PAGE_BLANK) {
            if (*free_segment == segments) {
                *free_segment = segment;
            }
            continue;
        }
        if (state != METADATA_PAGE_VALID ||
            header.type != COSMOS_FTL_NFC_PAGE_CHECKPOINT ||
            header.logical_index != slot ||
            header.payload_length != COSMOS_FTL_NFC_CHECKPOINT_BYTES) {
            continue;
        }
        {
            struct cosmos_ftl_checkpoint checkpoint;
            decode_ftl_checkpoint(
                data_buffer(backend) + COSMOS_FTL_NFC_HEADER_BYTES,
                &checkpoint);
            if (backend_policy_checkpoint_candidate_better(
                    have_latest, checkpoint.generation,
                    have_latest != 0U ? latest->checkpoint.generation : 0ULL,
                    segment, have_latest != 0U ? latest->segment : 0U) != 0U) {
                latest->segment = segment;
                latest->checkpoint = checkpoint;
                have_latest = 1U;
            }
        }
    }
    return have_latest != 0U ? COSMOS_OK : COSMOS_UNAVAILABLE;
}

static int page_blank(struct cosmos_ftl_nfc_backend *backend,
                      unsigned int page) {
    struct media_header header;
    int state = read_metadata_page(backend, page, &header);

    return backend_policy_page_blank_status(state);
}

static int checkpoint_header_payload(
    const struct cosmos_ftl_checkpoint *checkpoint, unsigned char *payload) {
    encode_ftl_checkpoint(payload, checkpoint);
    return COSMOS_OK;
}

static void update_checkpoint_watermark(
    struct cosmos_ftl_nfc_backend *backend, unsigned int slot,
    const struct cosmos_ftl_checkpoint *checkpoint) {
    backend->checkpoint_valid_mask |= 1U << slot;
    backend->checkpoint_generation[slot] = checkpoint->generation;
    backend->checkpoint_journal_index[slot] = checkpoint->journal_index;
    backend->journal_next_index = backend_policy_next_journal_index(
        backend->journal_next_index, checkpoint->journal_index);
    backend->journal_first_index = backend_policy_first_journal_index(
        backend->checkpoint_valid_mask, backend->journal_first_index,
        backend->checkpoint_journal_index[0],
        backend->checkpoint_journal_index[1]);
}

static int checkpoint_header_read(
    struct cosmos_ftl_nfc_backend *backend, unsigned int slot,
    struct checkpoint_location *location) {
    unsigned int free_segment;
    int status = find_checkpoint(
        backend, slot, location, &free_segment);

    if (status == COSMOS_OK) {
        update_checkpoint_watermark(backend, slot, &location->checkpoint);
    }
    return status;
}

static int ftl_read_checkpoint_header(
    void *context, unsigned int slot,
    struct cosmos_ftl_checkpoint *checkpoint) {
    struct cosmos_ftl_nfc_backend *backend = context;
    struct checkpoint_location location;
    int status;

    if (checkpoint == 0 || require_mounted(backend) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    status = checkpoint_header_read(backend, slot, &location);
    if (status == COSMOS_OK) {
        *checkpoint = location.checkpoint;
    }
    return status;
}

static int ftl_read_checkpoint_data(
    void *context, unsigned int slot, unsigned int *l2p,
    unsigned int l2p_count, struct cosmos_ftl_block *blocks,
    unsigned int block_count) {
    struct cosmos_ftl_nfc_backend *backend = context;
    struct checkpoint_location location;
    unsigned int page;
    unsigned int total;
    int status;

    if (backend == 0 || l2p == 0 || blocks == 0 ||
        l2p_count != backend->l2p_count ||
        block_count != backend->block_count ||
        require_mounted(backend) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    status = checkpoint_header_read(backend, slot, &location);
    if (status != COSMOS_OK) {
        return status;
    }
    total = checkpoint_total_bytes(l2p_count, block_count);
    nfc_memset(l2p, 0U, l2p_count * sizeof(*l2p));
    nfc_memset(blocks, 0U, block_count * sizeof(*blocks));
    for (page = 0U; page < backend->checkpoint_data_pages; ++page) {
        struct media_header header;
        unsigned int physical = checkpoint_start_page(backend, slot) +
            location.segment * backend->checkpoint_record_pages + page + 1U;
        unsigned int offset = page * COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES;
        unsigned int length = total - offset;
        int state;

        if (length > COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES) {
            length = COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES;
        }
        state = read_metadata_page(backend, physical, &header);
        if (state == METADATA_PAGE_RETRY) {
            return COSMOS_RETRY;
        }
        if (state != METADATA_PAGE_VALID ||
            header.type != COSMOS_FTL_NFC_PAGE_CHECKPOINT_DATA ||
            header.logical_index != page ||
            header.generation != location.checkpoint.generation ||
            header.payload_length != length) {
            return COSMOS_HW_ERROR;
        }
        checkpoint_get_chunk(
            data_buffer(backend) + COSMOS_FTL_NFC_HEADER_BYTES,
            l2p, blocks, l2p_count, offset, length);
    }
    return COSMOS_OK;
}

static int recycle_checkpoint_slot(
    struct cosmos_ftl_nfc_backend *backend, unsigned int slot) {
    unsigned int page;

    if (backend_policy_recycle_status(
            slot, backend->checkpoint_valid_mask) != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    for (page = 0U; page < backend->checkpoint_slot_pages;
         page += COSMOS_FTL_PAGES_PER_BLOCK) {
        unsigned int ppa;
        struct cosmos_nfc_io io;
        int status;

        if (metadata_ppa(checkpoint_start_page(backend, slot) + page, &ppa) !=
                COSMOS_OK || ppa_io(backend, ppa, &io) != COSMOS_OK) {
            return COSMOS_INVALID;
        }
        status = backend->nfc.erase_block(
            backend->nfc.context, io.channel, io.way, io.row_address,
            backend->dma.status_report_address);
        if (status != COSMOS_OK) {
            backend->faulted = 1U;
            return status;
        }
    }
    backend->checkpoint_valid_mask &= ~(1U << slot);
    backend->checkpoint_generation[slot] = 0ULL;
    backend->checkpoint_journal_index[slot] = 0ULL;
    backend->next_checkpoint_segment[slot] = 0U;
    return COSMOS_OK;
}

static int ftl_write_checkpoint(
    void *context, unsigned int slot, const unsigned int *l2p,
    unsigned int l2p_count, const struct cosmos_ftl_block *blocks,
    unsigned int block_count, const struct cosmos_ftl_checkpoint *checkpoint) {
    struct cosmos_ftl_nfc_backend *backend = context;
    unsigned char checkpoint_payload[COSMOS_FTL_NFC_CHECKPOINT_BYTES];
    struct checkpoint_location latest;
    unsigned int free_segment;
    unsigned int page;
    unsigned int total;
    unsigned int ppa;
    int status;

    if (backend == 0 || l2p == 0 || blocks == 0 || checkpoint == 0 ||
        slot >= 2U ||
        l2p_count != backend->l2p_count || block_count != backend->block_count ||
        require_mounted(backend) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    status = find_checkpoint(backend, slot, &latest, &free_segment);
    if (status != COSMOS_OK && status != COSMOS_UNAVAILABLE) {
        return status;
    }
    if (free_segment >= checkpoint_segments(backend)) {
        status = recycle_checkpoint_slot(backend, slot);
        if (status != COSMOS_OK) {
            return status;
        }
        free_segment = 0U;
    }
    total = checkpoint_total_bytes(l2p_count, block_count);
    for (page = 0U; page < backend->checkpoint_record_pages; ++page) {
        unsigned int physical = checkpoint_start_page(backend, slot) +
            free_segment * backend->checkpoint_record_pages + page;
        status = page_blank(backend, physical);
        if (status != COSMOS_OK) {
            return status == COSMOS_RETRY ? COSMOS_RETRY :
                COSMOS_UNAVAILABLE;
        }
    }
    for (page = 0U; page < backend->checkpoint_data_pages; ++page) {
        unsigned char *data = data_buffer(backend);
        unsigned int offset = page * COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES;
        unsigned int length = total - offset;
        unsigned int physical = checkpoint_start_page(backend, slot) +
            free_segment * backend->checkpoint_record_pages + page + 1U;

        if (length > COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES) {
            length = COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES;
        }
        checkpoint_put_chunk(
            data + COSMOS_FTL_NFC_HEADER_BYTES,
            l2p, blocks, l2p_count, offset, length);
        if (metadata_ppa(physical, &ppa) != COSMOS_OK) {
            return COSMOS_INVALID;
        }
        status = write_page(
            backend, ppa, COSMOS_FTL_NFC_PAGE_CHECKPOINT_DATA, page,
            checkpoint->generation, data + COSMOS_FTL_NFC_HEADER_BYTES,
            length, 0U);
        if (status != COSMOS_OK) {
            return status;
        }
    }
    checkpoint_header_payload(checkpoint, checkpoint_payload);
    if (metadata_ppa(
            checkpoint_start_page(backend, slot) +
            free_segment * backend->checkpoint_record_pages, &ppa) !=
            COSMOS_OK) {
        return COSMOS_INVALID;
    }
    status = write_page(backend, ppa, COSMOS_FTL_NFC_PAGE_CHECKPOINT,
        slot, checkpoint->generation, checkpoint_payload,
        COSMOS_FTL_NFC_CHECKPOINT_BYTES, 0U);
    if (status == COSMOS_OK) {
        update_checkpoint_watermark(backend, slot, checkpoint);
        backend->next_checkpoint_segment[slot] = free_segment + 1U;
    }
    return status;
}

static int data_page_blank(struct cosmos_ftl_nfc_backend *backend,
                           unsigned int ppa) {
    struct media_header header;
    int state = read_page_state(backend, ppa, 1U, &header, 0);

    return state == METADATA_PAGE_BLANK ? COSMOS_OK : COSMOS_INVALID;
}

static int ftl_program_data(void *context, unsigned int ppa,
                            unsigned int lpn,
                            unsigned long long generation) {
    struct cosmos_ftl_nfc_backend *backend = context;
    unsigned char payload[1] = {0U};

    if (backend == 0 || lpn >= backend->l2p_count ||
        require_mounted(backend) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    /* The caller owns data_address; pre-reading it would destroy its payload. */
    return write_page(backend, ppa, COSMOS_FTL_NFC_PAGE_DATA_TAG,
                      lpn, generation, payload, 0U, 1U);
}

static int read_data_page(struct cosmos_ftl_nfc_backend *backend,
                          unsigned int ppa, unsigned int *lpn,
                          unsigned long long *generation,
                          unsigned int *needs_refresh) {
    struct media_header header;
    int state;

    if (lpn == 0 || generation == 0) {
        return COSMOS_INVALID;
    }
    state = read_page_state(
        backend, ppa, 1U, &header, needs_refresh);
    if (state == METADATA_PAGE_RETRY) {
        return COSMOS_RETRY;
    }
    if (state == METADATA_PAGE_BLANK) {
        return COSMOS_UNAVAILABLE;
    }
    if (state != METADATA_PAGE_VALID ||
        header.type != COSMOS_FTL_NFC_PAGE_DATA_TAG ||
        header.payload_length != 0U || header.logical_index >= backend->l2p_count) {
        return COSMOS_HW_ERROR;
    }
    *lpn = (unsigned int)header.logical_index;
    *generation = header.generation;
    return COSMOS_OK;
}

static int ftl_read_page_tag(void *context, unsigned int ppa,
                             unsigned int *lpn,
                             unsigned long long *generation,
                             unsigned int *needs_refresh) {
    struct cosmos_ftl_nfc_backend *backend = context;

    if (require_mounted(backend) != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    return read_data_page(
        backend, ppa, lpn, generation, needs_refresh);
}

static int ftl_copy_data(void *context, unsigned int source_ppa,
                         unsigned int destination_ppa, unsigned int lpn,
                         unsigned long long generation) {
    struct cosmos_ftl_nfc_backend *backend = context;
    unsigned int needs_refresh;
    unsigned int source_lpn;
    unsigned long long source_generation;
    int status;

    if (backend == 0 || require_mounted(backend) != COSMOS_OK ||
        lpn >= backend->l2p_count) {
        return COSMOS_INVALID;
    }
    status = data_page_blank(backend, destination_ppa);
    if (status != COSMOS_OK) {
        return status;
    }
    status = read_data_page(
        backend, source_ppa, &source_lpn, &source_generation,
        &needs_refresh);
    if (status != COSMOS_OK || source_lpn != lpn) {
        return status == COSMOS_OK ? COSMOS_HW_ERROR : status;
    }
    (void)needs_refresh;
    (void)source_generation;
    return write_page(backend, destination_ppa,
                      COSMOS_FTL_NFC_PAGE_DATA_TAG, lpn, generation,
                      (const unsigned char *)"", 0U, 1U);
}

static int ftl_erase_block(void *context, unsigned int block_index) {
    struct cosmos_ftl_nfc_backend *backend = context;
    unsigned int ppa;
    struct cosmos_nfc_io io;

    if (backend == 0 || require_mounted(backend) != COSMOS_OK ||
        block_index >= COSMOS_FTL_BLOCK_COUNT ||
        cosmos_ftl_ppa_encode(
            block_index / (COSMOS_FTL_LUN_COUNT * COSMOS_FTL_BLOCKS_PER_LUN),
            (block_index / COSMOS_FTL_BLOCKS_PER_LUN) % COSMOS_FTL_LUN_COUNT,
            block_index % COSMOS_FTL_BLOCKS_PER_LUN, 0U, &ppa) != COSMOS_OK ||
        ppa_io(backend, ppa, &io) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    return backend->nfc.erase_block(
        backend->nfc.context, io.channel, io.way, io.row_address,
        backend->dma.status_report_address);
}

static unsigned int journal_page(
    const struct cosmos_ftl_nfc_backend *backend,
    unsigned long long index) {
    return backend_policy_journal_page(
        backend->journal_start_page, backend->journal_capacity, index);
}

static int journal_page_ppa(const struct cosmos_ftl_nfc_backend *backend,
                            unsigned long long index, unsigned int *ppa) {
    return metadata_ppa(journal_page(backend, index), ppa);
}

static enum cosmos_ftl_append_result ftl_append_journal(
    void *context, unsigned long long index,
    const struct cosmos_ftl_journal_record *record) {
    struct cosmos_ftl_nfc_backend *backend = context;
    unsigned char payload[COSMOS_FTL_NFC_JOURNAL_PAGE_BYTES];
    unsigned int ppa;
    unsigned int block;
    int page_state;
    int status;

    if (backend == 0 || record == 0 ||
        backend_policy_journal_append_admit(
            require_mounted(backend), index, backend->journal_first_index,
            backend->journal_capacity, backend->journal_next_index) == 0U ||
        journal_page_ppa(backend, index, &ppa) != COSMOS_OK) {
        return COSMOS_FTL_APPEND_HARD_FAILED;
    }
    page_state = read_page_state(
        backend, ppa, 0U, &(struct media_header){0}, 0);
    if (page_state != METADATA_PAGE_BLANK) {
        if (page_state == METADATA_PAGE_RETRY) {
            return COSMOS_FTL_APPEND_NOT_COMMITTED;
        }
        return COSMOS_FTL_APPEND_HARD_FAILED;
    }
    encode_journal(payload, record);
    status = write_page(backend, ppa, COSMOS_FTL_NFC_PAGE_JOURNAL,
                        index, record->generation, payload,
                        COSMOS_FTL_NFC_JOURNAL_PAGE_BYTES, 0U);
    if (backend_policy_journal_append_result(status) ==
            COSMOS_FTL_APPEND_COMMITTED) {
        block = (unsigned int)(
            (index & (backend->journal_capacity - 1ULL)) /
            COSMOS_FTL_PAGES_PER_BLOCK);
        backend->journal_block_erased[block] = 0U;
        backend->journal_next_index = index + 1ULL;
        return COSMOS_FTL_APPEND_COMMITTED;
    }
    return (enum cosmos_ftl_append_result)
        backend_policy_journal_append_result(status);
}

static int ftl_read_journal(
    void *context, unsigned long long index,
    struct cosmos_ftl_journal_record *record) {
    struct cosmos_ftl_nfc_backend *backend = context;
    struct media_header header;
    unsigned int ppa;
    int state;

    if (backend == 0 || record == 0 ||
        backend_policy_journal_read_admit(
            require_mounted(backend), index, backend->journal_first_index,
            backend->journal_capacity) == 0U ||
        journal_page_ppa(backend, index, &ppa) != COSMOS_OK) {
        return COSMOS_UNAVAILABLE;
    }
    state = read_page_state(backend, ppa, 0U, &header, 0);
    if (state == METADATA_PAGE_RETRY) {
        return COSMOS_RETRY;
    }
    if (state == METADATA_PAGE_IO_ERROR) {
        return COSMOS_HW_ERROR;
    }
    if (state == METADATA_PAGE_BLANK) {
        return COSMOS_UNAVAILABLE;
    }
    backend->journal_next_index = backend_policy_journal_next_after_read(
        index, backend->journal_next_index);
    if (state != METADATA_PAGE_VALID ||
        header.type != COSMOS_FTL_NFC_PAGE_JOURNAL ||
        header.logical_index != index ||
        header.payload_length != COSMOS_FTL_NFC_JOURNAL_PAGE_BYTES) {
        return COSMOS_INVALID;
    }
    decode_journal(
        data_buffer(backend) + COSMOS_FTL_NFC_HEADER_BYTES, record);
    if (backend_policy_journal_record_valid(
            record->sequence, index, record->magic, record->crc,
            cosmos_ftl_journal_record_crc(record)) == 0U) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}

static int journal_block_fully_dead(
    const struct cosmos_ftl_nfc_backend *backend, unsigned int block,
    unsigned long long first_live) {
    return (int)backend_policy_journal_block_fully_dead(
        backend->journal_capacity, backend->journal_next_index,
        block, first_live);
}

static int ftl_trim_journal(void *context, unsigned long long first_live) {
    struct cosmos_ftl_nfc_backend *backend = context;
    unsigned int block;
    int status;

    if (backend == 0) {
        return COSMOS_UNAVAILABLE;
    }
    status = backend_policy_journal_trim_status(
        require_mounted(backend), backend->checkpoint_valid_mask,
        first_live, backend->journal_first_index,
        backend->journal_capacity, backend->checkpoint_journal_index[0],
        backend->checkpoint_journal_index[1]);
    if (status != COSMOS_OK) {
        return status;
    }
    for (block = 0U; block < backend->journal_blocks; ++block) {
        unsigned int ppa;
        struct cosmos_nfc_io io;

        if (backend->journal_block_erased[block] != 0U ||
            !journal_block_fully_dead(
                backend, block, first_live)) {
            continue;
        }
        if (metadata_ppa(
                backend->journal_start_page +
                block * COSMOS_FTL_PAGES_PER_BLOCK, &ppa) != COSMOS_OK ||
            ppa_io(backend, ppa, &io) != COSMOS_OK) {
            return COSMOS_INVALID;
        }
        status = backend->nfc.erase_block(
            backend->nfc.context, io.channel, io.way, io.row_address,
            backend->dma.status_report_address);
        if (status != COSMOS_OK) {
            backend->faulted = 1U;
            return status;
        }
        backend->journal_block_erased[block] = 1U;
    }
    backend->journal_first_index = first_live;
    return COSMOS_OK;
}

int cosmos_ftl_nfc_backend_init(
    struct cosmos_ftl_nfc_backend *backend,
    const struct cosmos_ftl_nfc_dma *dma,
    const struct cosmos_ftl_nfc_ops *ops,
    unsigned int l2p_count, unsigned int block_count,
    unsigned long long journal_pages) {
    unsigned int slot_pages;
    unsigned int data_pages;
    unsigned int record_pages;
    unsigned int journal_start;
    unsigned int block;

    if (backend == 0 || !dma_valid(dma) || l2p_count == 0U ||
        block_count == 0U ||
        checkpoint_total_bytes(l2p_count, block_count) == 0U) {
        return COSMOS_INVALID;
    }
    if (ops != 0 && (ops->read_page == 0 || ops->program_page == 0 ||
                     ops->erase_block == 0)) {
        return COSMOS_INVALID;
    }
    journal_pages = backend_policy_journal_pages_normalized(journal_pages);
    if (backend_policy_journal_pages_valid(journal_pages) == 0U) {
        return COSMOS_INVALID;
    }
    data_pages = backend_policy_checkpoint_data_pages(
        checkpoint_total_bytes(l2p_count, block_count));
    record_pages = data_pages + 1U;
    slot_pages = backend_policy_checkpoint_slot_pages(
        journal_pages, COSMOS_FTL_NFC_METADATA_PAGE_LIMIT);
    journal_start = backend_policy_journal_start_page(slot_pages);
    if (backend_policy_layout_valid(
            journal_start, journal_pages, slot_pages, record_pages,
            COSMOS_FTL_NFC_METADATA_PAGE_LIMIT) == 0U) {
        return COSMOS_INVALID;
    }
    nfc_memset(backend, 0U, sizeof(*backend));
    backend->nfc.context = ops == 0 ? 0 : ops->context;
    backend->nfc.read_page = ops == 0 ? default_read_page : ops->read_page;
    backend->nfc.program_page = ops == 0 ? default_program_page :
        ops->program_page;
    backend->nfc.erase_block = ops == 0 ? default_erase_block :
        ops->erase_block;
    backend->dma = *dma;
    backend->l2p_count = l2p_count;
    backend->block_count = block_count;
    backend->checkpoint_data_pages = data_pages;
    backend->checkpoint_record_pages = record_pages;
    backend->checkpoint_slot_pages = slot_pages;
    backend->journal_start_page = journal_start;
    backend->journal_capacity = journal_pages;
    backend->journal_blocks = (unsigned int)(backend->journal_capacity /
                                             COSMOS_FTL_PAGES_PER_BLOCK);
    backend->checkpoint_payload_bytes =
        checkpoint_total_bytes(l2p_count, block_count);
    for (block = 0U; block < backend->journal_blocks; ++block) {
        backend->journal_block_erased[block] = 0U;
    }
    backend->ftl.context = backend;
    backend->ftl.program_data = ftl_program_data;
    backend->ftl.copy_data = ftl_copy_data;
    backend->ftl.read_page_tag = ftl_read_page_tag;
    backend->ftl.erase_block = ftl_erase_block;
    backend->ftl.append_journal = ftl_append_journal;
    backend->ftl.read_journal = ftl_read_journal;
    backend->ftl.trim_journal = ftl_trim_journal;
    backend->ftl.journal_capacity = backend->journal_capacity;
    backend->ftl.read_checkpoint_header = ftl_read_checkpoint_header;
    backend->ftl.read_checkpoint_data = ftl_read_checkpoint_data;
    backend->ftl.write_checkpoint = ftl_write_checkpoint;
    return COSMOS_OK;
}

int cosmos_ftl_nfc_backend_format(struct cosmos_ftl_nfc_backend *backend) {
    unsigned int lane;
    unsigned int block;
    unsigned char payload[COSMOS_FTL_NFC_SUPERBLOCK_BYTES];
    unsigned int ppa;
    int status;

    if (backend == 0 || backend->faulted != 0U) {
        return COSMOS_INVALID;
    }
    for (lane = 0U; lane < COSMOS_FTL_LANE_COUNT; ++lane) {
        for (block = 0U; block < COSMOS_FTL_METADATA_BLOCKS_PER_LUN;
             ++block) {
            unsigned int die = lane / COSMOS_FTL_LUN_COUNT;
            unsigned int lun = lane % COSMOS_FTL_LUN_COUNT;
            struct cosmos_nfc_io io;

            if (cosmos_ftl_ppa_encode(die, lun, block, 0U, &ppa) !=
                    COSMOS_OK || ppa_io(backend, ppa, &io) != COSMOS_OK) {
                return COSMOS_INVALID;
            }
            status = backend->nfc.erase_block(
                backend->nfc.context, io.channel, io.way, io.row_address,
                backend->dma.status_report_address);
            if (status != COSMOS_OK) {
                backend->faulted = 1U;
                return status;
            }
        }
    }
    superblock_payload(backend, payload);
    status = metadata_ppa(0U, &ppa);
    if (status == COSMOS_OK) {
        status = write_page(backend, ppa, COSMOS_FTL_NFC_PAGE_SUPERBLOCK,
                            0ULL, 1ULL, payload,
                            COSMOS_FTL_NFC_SUPERBLOCK_BYTES, 0U);
    }
    if (status != COSMOS_OK) {
        backend->faulted = 1U;
        return status;
    }
    backend->mounted = 1U;
    backend->checkpoint_valid_mask = 0U;
    backend->journal_first_index = 0ULL;
    backend->journal_next_index = 0ULL;
    nfc_memset(backend->next_checkpoint_segment, 0U,
               sizeof(backend->next_checkpoint_segment));
    for (block = 0U; block < backend->journal_blocks; ++block) {
        backend->journal_block_erased[block] = 1U;
    }
    return COSMOS_OK;
}

int cosmos_ftl_nfc_backend_mount(struct cosmos_ftl_nfc_backend *backend) {
    int status;

    if (backend == 0 || backend->faulted != 0U) {
        return COSMOS_INVALID;
    }
    status = read_superblock(backend);
    if (status != COSMOS_OK) {
        backend->mounted = 0U;
        return status;
    }
    backend->mounted = 1U;
    backend->checkpoint_valid_mask = 0U;
    backend->journal_first_index = 0ULL;
    backend->journal_next_index = 0ULL;
    return COSMOS_OK;
}
