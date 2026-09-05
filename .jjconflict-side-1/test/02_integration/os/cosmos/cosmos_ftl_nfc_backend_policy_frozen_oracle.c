/* Independent frozen pre-migration C oracle for backend-local scalar policy.
 * It deliberately has no dependency on the Simple implementation or bridge. */
#include "cosmos_ftl_nfc_backend_policy_oracle.h"

#include <stdint.h>

#define O_OK 0
#define O_UNAVAILABLE 1
#define O_INVALID 2
#define O_TIMEOUT 3
#define O_HW_ERROR 4
#define O_RETRY 5
#define O_COMPLETION_UNCERTAIN 6

#define O_PAGE_BLANK 0
#define O_PAGE_VALID 1
#define O_PAGE_TORN 2
#define O_PAGE_RETRY 3
#define O_PAGE_IO_ERROR 4

#define O_APPEND_COMMITTED 0U
#define O_APPEND_NOT_COMMITTED 1U
#define O_APPEND_AMBIGUOUS 2U
#define O_APPEND_HARD_FAILED 3U

#define O_NFC_MAGIC 0x43464E31U
#define O_FTL_MAGIC 0x46544C31U
#define O_FORMAT_VERSION 1U
#define O_PAYLOAD_BYTES 16348U
#define O_PAGES_PER_BLOCK 128U
#define O_DEFAULT_JOURNAL_PAGES 65536ULL
#define O_MAX_JOURNAL_PAGES 262144ULL

static unsigned int oracle_journal_capacity_valid(
    unsigned long long capacity) {
    if (capacity == 0ULL || (capacity & (capacity - 1ULL)) != 0ULL) {
        return 0U;
    }
    return 1U;
}

unsigned int cosmos_ftl_nfc_backend_oracle_checkpoint_total_bytes(
    unsigned int l2p_count, unsigned int block_count) {
    unsigned long long total = (unsigned long long)l2p_count * 4ULL +
        (unsigned long long)block_count * 8ULL;
    if (total > UINT32_MAX) {
        return 0U;
    }
    return (unsigned int)total;
}

int cosmos_ftl_nfc_backend_oracle_header_prefix_status(
    unsigned int magic, unsigned int version, unsigned int header_crc,
    unsigned int expected_header_crc) {
    if (magic != O_NFC_MAGIC || version != O_FORMAT_VERSION ||
        header_crc != expected_header_crc) {
        return O_INVALID;
    }
    return O_OK;
}

int cosmos_ftl_nfc_backend_oracle_payload_length_status(
    unsigned int payload_length) {
    if (payload_length > O_PAYLOAD_BYTES) {
        return O_INVALID;
    }
    return O_OK;
}

int cosmos_ftl_nfc_backend_oracle_read_io_state(int status) {
    if (status == O_RETRY) {
        return O_PAGE_RETRY;
    }
    if (status != O_OK) {
        return O_PAGE_IO_ERROR;
    }
    return O_PAGE_VALID;
}

int cosmos_ftl_nfc_backend_oracle_read_content_state(
    unsigned int all_ff, int header_status, unsigned int spare_header,
    int payload_status) {
    if (all_ff != 0U) {
        return O_PAGE_BLANK;
    }
    if (header_status != O_OK) {
        return O_PAGE_TORN;
    }
    if (spare_header == 0U) {
        if (payload_status != O_OK) {
            return O_PAGE_TORN;
        }
    }
    return O_PAGE_VALID;
}

unsigned int cosmos_ftl_nfc_backend_oracle_write_faults(int status) {
    if (status == O_TIMEOUT || status == O_COMPLETION_UNCERTAIN) {
        return 1U;
    }
    return 0U;
}

int cosmos_ftl_nfc_backend_oracle_superblock_status(
    int page_state, unsigned int page_type, unsigned long long logical_index,
    unsigned int payload_length, unsigned int payload_valid) {
    if (page_state == O_PAGE_RETRY) {
        return O_RETRY;
    }
    if (page_state != O_PAGE_VALID) {
        if (page_state == O_PAGE_BLANK) {
            return O_UNAVAILABLE;
        }
        return O_HW_ERROR;
    }
    if (page_type != 1U) {
        return O_HW_ERROR;
    }
    if (logical_index != 0ULL) {
        return O_HW_ERROR;
    }
    if (payload_length != 40U) {
        return O_HW_ERROR;
    }
    if (payload_valid == 0U) {
        return O_HW_ERROR;
    }
    return O_OK;
}

int cosmos_ftl_nfc_backend_oracle_mounted_status(
    unsigned int backend_present, unsigned int mounted,
    unsigned int faulted) {
    if (backend_present == 0U || mounted == 0U || faulted != 0U) {
        return O_UNAVAILABLE;
    }
    return O_OK;
}

unsigned int cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better(
    unsigned int have_latest, unsigned long long candidate_generation,
    unsigned long long latest_generation, unsigned int candidate_segment,
    unsigned int latest_segment) {
    if (have_latest == 0U) {
        return 1U;
    }
    if (candidate_generation > latest_generation) {
        return 1U;
    }
    if (candidate_generation != latest_generation) {
        return 0U;
    }
    if (candidate_segment > latest_segment) {
        return 1U;
    }
    return 0U;
}

int cosmos_ftl_nfc_backend_oracle_page_blank_status(int page_state) {
    if (page_state == O_PAGE_BLANK) {
        return O_OK;
    }
    if (page_state == O_PAGE_RETRY) {
        return O_RETRY;
    }
    if (page_state == O_PAGE_IO_ERROR) {
        return O_HW_ERROR;
    }
    return O_INVALID;
}

int cosmos_ftl_nfc_backend_oracle_recycle_status(
    unsigned int slot, unsigned int checkpoint_valid_mask) {
    unsigned int other_slot_mask;
    if (slot >= 2U) {
        return O_UNAVAILABLE;
    }
    other_slot_mask = 1U << (slot ^ 1U);
    if ((checkpoint_valid_mask & other_slot_mask) == 0U) {
        return O_UNAVAILABLE;
    }
    return O_OK;
}

unsigned long long cosmos_ftl_nfc_backend_oracle_next_journal_index(
    unsigned long long current, unsigned long long checkpoint_index) {
    if (checkpoint_index > current) {
        return checkpoint_index;
    }
    return current;
}

unsigned long long cosmos_ftl_nfc_backend_oracle_first_journal_index(
    unsigned int checkpoint_valid_mask, unsigned long long current,
    unsigned long long checkpoint_index_0,
    unsigned long long checkpoint_index_1) {
    unsigned long long first;
    if (checkpoint_valid_mask != 3U) {
        return current;
    }
    first = checkpoint_index_0;
    if (checkpoint_index_1 < first) {
        first = checkpoint_index_1;
    }
    if (first > current) {
        return first;
    }
    return current;
}

unsigned long long cosmos_ftl_nfc_backend_oracle_journal_pages_normalized(
    unsigned long long journal_pages) {
    if (journal_pages == 0ULL) {
        return O_DEFAULT_JOURNAL_PAGES;
    }
    return journal_pages;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_pages_valid(
    unsigned long long journal_pages) {
    if (journal_pages - 1ULL >= O_MAX_JOURNAL_PAGES) {
        return 0U;
    }
    if ((journal_pages & (journal_pages - 1ULL)) != 0ULL) {
        return 0U;
    }
    if (journal_pages % O_PAGES_PER_BLOCK != 0ULL) {
        return 0U;
    }
    return 1U;
}

unsigned int cosmos_ftl_nfc_backend_oracle_checkpoint_data_pages(
    unsigned int total_bytes) {
    return (unsigned int)(((unsigned long long)total_bytes +
        O_PAYLOAD_BYTES - 1ULL) / O_PAYLOAD_BYTES);
}

unsigned int cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages(
    unsigned long long journal_pages, unsigned int metadata_page_limit) {
    unsigned int available;
    if (metadata_page_limit < O_PAGES_PER_BLOCK ||
        journal_pages > metadata_page_limit - O_PAGES_PER_BLOCK) {
        return 0U;
    }
    available = metadata_page_limit - O_PAGES_PER_BLOCK;
    available -= (unsigned int)journal_pages;
    return (available / 2U / O_PAGES_PER_BLOCK) * O_PAGES_PER_BLOCK;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_start_page(
    unsigned int checkpoint_slot_pages) {
    return O_PAGES_PER_BLOCK + 2U * checkpoint_slot_pages;
}

unsigned int cosmos_ftl_nfc_backend_oracle_layout_valid(
    unsigned int journal_start_page, unsigned long long journal_pages,
    unsigned int checkpoint_slot_pages,
    unsigned int checkpoint_record_pages, unsigned int metadata_page_limit) {
    if (journal_start_page >= metadata_page_limit) {
        return 0U;
    }
    if ((unsigned long long)(metadata_page_limit - journal_start_page) <
            journal_pages) {
        return 0U;
    }
    if (checkpoint_slot_pages < checkpoint_record_pages) {
        return 0U;
    }
    return 1U;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_page(
    unsigned int journal_start_page, unsigned long long journal_capacity,
    unsigned long long index) {
    if (oracle_journal_capacity_valid(journal_capacity) == 0U) {
        return 0U;
    }
    return journal_start_page +
        (unsigned int)(index & (journal_capacity - 1ULL));
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_append_admit(
    int mounted_status, unsigned long long index,
    unsigned long long first_index, unsigned long long capacity,
    unsigned long long next_index) {
    if (oracle_journal_capacity_valid(capacity) == 0U) {
        return 0U;
    }
    if (mounted_status != O_OK) {
        return 0U;
    }
    if (index < first_index) {
        return 0U;
    }
    if (index - first_index >= capacity) {
        return 0U;
    }
    if (next_index != 0ULL) {
        if (index != next_index) {
            return 0U;
        }
    }
    return 1U;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_append_result(int status) {
    if (status == O_OK) {
        return O_APPEND_COMMITTED;
    }
    if (status == O_TIMEOUT || status == O_COMPLETION_UNCERTAIN) {
        return O_APPEND_AMBIGUOUS;
    }
    if (status == O_UNAVAILABLE) {
        return O_APPEND_NOT_COMMITTED;
    }
    if (status == O_RETRY) {
        return O_APPEND_NOT_COMMITTED;
    }
    return O_APPEND_HARD_FAILED;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_read_admit(
    int mounted_status, unsigned long long index,
    unsigned long long first_index, unsigned long long capacity) {
    if (oracle_journal_capacity_valid(capacity) == 0U) {
        return 0U;
    }
    if (mounted_status != O_OK) {
        return 0U;
    }
    if (index < first_index) {
        return 0U;
    }
    if (index - first_index >= capacity) {
        return 0U;
    }
    return 1U;
}

unsigned long long cosmos_ftl_nfc_backend_oracle_journal_next_after_read(
    unsigned long long index, unsigned long long current) {
    unsigned long long candidate;
    if (index == UINT64_MAX) {
        return current;
    }
    candidate = index + 1ULL;
    if (candidate > current) {
        return candidate;
    }
    return current;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_record_valid(
    unsigned long long sequence, unsigned long long expected_sequence,
    unsigned int magic, unsigned int crc, unsigned int expected_crc) {
    if (sequence != expected_sequence) {
        return 0U;
    }
    if (magic != O_FTL_MAGIC) {
        return 0U;
    }
    if (crc != expected_crc) {
        return 0U;
    }
    return 1U;
}

unsigned int cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(
    unsigned long long capacity, unsigned long long next_index,
    unsigned int block, unsigned long long first_live) {
    unsigned long long candidate;
    if (oracle_journal_capacity_valid(capacity) == 0U) {
        return 0U;
    }
    candidate = (next_index & ~(capacity - 1ULL)) +
        (unsigned long long)block * O_PAGES_PER_BLOCK;
    if (candidate >= next_index) {
        if (candidate < capacity) {
            return 0U;
        }
        candidate -= capacity;
    }
    if (candidate > UINT64_MAX - O_PAGES_PER_BLOCK) {
        return 0U;
    }
    if (candidate + O_PAGES_PER_BLOCK > first_live) {
        return 0U;
    }
    return 1U;
}

int cosmos_ftl_nfc_backend_oracle_journal_trim_status(
    int mounted_status, unsigned int checkpoint_valid_mask,
    unsigned long long first_live, unsigned long long first_index,
    unsigned long long capacity, unsigned long long checkpoint_index_0,
    unsigned long long checkpoint_index_1) {
    unsigned long long watermark;
    if (oracle_journal_capacity_valid(capacity) == 0U) {
        return O_UNAVAILABLE;
    }
    if (mounted_status != O_OK || (checkpoint_valid_mask & 3U) != 3U) {
        return O_UNAVAILABLE;
    }
    if (first_live < first_index) {
        return O_UNAVAILABLE;
    }
    if (first_live - first_index > capacity) {
        return O_UNAVAILABLE;
    }
    watermark = checkpoint_index_0;
    if (checkpoint_index_1 < watermark) {
        watermark = checkpoint_index_1;
    }
    if (first_live > watermark) {
        return O_INVALID;
    }
    return O_OK;
}
