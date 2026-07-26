#include <stdio.h>
#include <string.h>

#include "cosmos_ftl.h"

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define TEST_L2P_COUNT 16U
#define TEST_JOURNAL_COUNT 64U

struct mock_media {
    struct cosmos_ftl_journal_record journal[TEST_JOURNAL_COUNT];
    struct cosmos_ftl_checkpoint checkpoint[2];
    unsigned int checkpoint_l2p[2][TEST_L2P_COUNT];
    struct cosmos_ftl_block checkpoint_blocks[2][COSMOS_FTL_BLOCK_COUNT];
    unsigned long long journal_count;
    unsigned long long journal_first_index;
    unsigned int trim_calls;
    unsigned int checkpoint_valid[2];
    unsigned int program_calls;
    unsigned int fail_program;
    unsigned long long fail_journal_index;
    enum cosmos_ftl_append_result fail_journal_result;
    unsigned int fail_journal_once;
    unsigned long long torn_journal_index;
    unsigned int erase_calls;
    unsigned int fail_erase;
    struct {
        unsigned int ppa;
        unsigned int lpn;
        unsigned long long generation;
        unsigned int valid;
    } page[TEST_JOURNAL_COUNT];
};

static struct cosmos_ftl_block blocks_a[COSMOS_FTL_BLOCK_COUNT];
static struct cosmos_ftl_block blocks_b[COSMOS_FTL_BLOCK_COUNT];
static unsigned int l2p_a[TEST_L2P_COUNT];
static unsigned int l2p_b[TEST_L2P_COUNT];
static struct mock_media media;

static int read_page_tag(void *context, unsigned int ppa,
                         unsigned int *lpn,
                         unsigned long long *generation,
                         unsigned int *needs_refresh);

static int program_data(void *context, unsigned int ppa, unsigned int lpn,
                        unsigned long long generation) {
    struct mock_media *mock = context;
    unsigned int index = mock->program_calls;

    ++mock->program_calls;
    if (index < TEST_JOURNAL_COUNT) {
        mock->page[index].ppa = ppa;
        mock->page[index].lpn = lpn;
        mock->page[index].generation = generation;
        mock->page[index].valid = 1U;
    }
    return mock->fail_program != 0U ? COSMOS_HW_ERROR : COSMOS_OK;
}

static int copy_data(void *context, unsigned int source_ppa,
                     unsigned int destination_ppa, unsigned int lpn,
                     unsigned long long generation) {
    struct mock_media *mock = context;
    unsigned int source_lpn;
    unsigned int needs_refresh;
    unsigned long long source_generation;

    if (read_page_tag(
            context, source_ppa, &source_lpn, &source_generation,
            &needs_refresh) !=
            COSMOS_OK ||
        source_lpn != lpn) {
        return COSMOS_HW_ERROR;
    }
    (void)needs_refresh;
    (void)source_generation;
    return program_data(
        mock, destination_ppa, lpn, generation);
}

static int read_page_tag(void *context, unsigned int ppa,
                         unsigned int *lpn,
                         unsigned long long *generation,
                         unsigned int *needs_refresh) {
    struct mock_media *mock = context;
    unsigned int index;

    for (index = 0U; index < TEST_JOURNAL_COUNT; ++index) {
        if (mock->page[index].valid != 0U &&
            mock->page[index].ppa == ppa) {
            *lpn = mock->page[index].lpn;
            *generation = mock->page[index].generation;
            *needs_refresh = 0U;
            return COSMOS_OK;
        }
    }
    return COSMOS_UNAVAILABLE;
}

static int erase_block(void *context, unsigned int block_index) {
    struct mock_media *mock = context;

    (void)block_index;
    ++mock->erase_calls;
    return mock->fail_erase != 0U ? COSMOS_HW_ERROR : COSMOS_OK;
}

static enum cosmos_ftl_append_result append_journal(
    void *context, unsigned long long index,
    const struct cosmos_ftl_journal_record *record) {
    struct mock_media *mock = context;

    if (index >= TEST_JOURNAL_COUNT) {
        return COSMOS_FTL_APPEND_HARD_FAILED;
    }
    if (index == mock->fail_journal_index) {
        if (mock->fail_journal_once != 0U) {
            mock->fail_journal_index = ~0ULL;
        }
        return mock->fail_journal_result;
    }
    mock->journal[index] = *record;
    if (mock->journal_count <= index) {
        mock->journal_count = index + 1U;
    }
    return COSMOS_FTL_APPEND_COMMITTED;
}

static int read_journal(
    void *context, unsigned long long index,
    struct cosmos_ftl_journal_record *record) {
    struct mock_media *mock = context;

    if (index < mock->journal_first_index ||
        index >= mock->journal_count) {
        return COSMOS_UNAVAILABLE;
    }
    if (index == mock->torn_journal_index) {
        return COSMOS_INVALID;
    }
    *record = mock->journal[index];
    return COSMOS_OK;
}

static int trim_journal(
    void *context, unsigned long long first_live_index) {
    struct mock_media *mock = context;

    if (first_live_index < mock->journal_first_index ||
        first_live_index > mock->journal_count) {
        return COSMOS_INVALID;
    }
    mock->journal_first_index = first_live_index;
    ++mock->trim_calls;
    return COSMOS_OK;
}

static int read_checkpoint_header(
    void *context, unsigned int slot,
    struct cosmos_ftl_checkpoint *checkpoint) {
    struct mock_media *mock = context;

    if (slot >= 2U || mock->checkpoint_valid[slot] == 0U) {
        return COSMOS_UNAVAILABLE;
    }
    *checkpoint = mock->checkpoint[slot];
    return COSMOS_OK;
}

static int read_checkpoint_data(
    void *context, unsigned int slot, unsigned int *l2p,
    unsigned int l2p_count, struct cosmos_ftl_block *blocks,
    unsigned int block_count) {
    struct mock_media *mock = context;

    memcpy(l2p, mock->checkpoint_l2p[slot],
           l2p_count * sizeof(*l2p));
    memcpy(blocks, mock->checkpoint_blocks[slot],
           block_count * sizeof(*blocks));
    return COSMOS_OK;
}

static int write_checkpoint(
    void *context, unsigned int slot, const unsigned int *l2p,
    unsigned int l2p_count, const struct cosmos_ftl_block *blocks,
    unsigned int block_count,
    const struct cosmos_ftl_checkpoint *checkpoint) {
    struct mock_media *mock = context;

    memcpy(mock->checkpoint_l2p[slot], l2p,
           l2p_count * sizeof(*l2p));
    memcpy(mock->checkpoint_blocks[slot], blocks,
           block_count * sizeof(*blocks));
    mock->checkpoint[slot] = *checkpoint;
    mock->checkpoint_valid[slot] = 1U;
    return COSMOS_OK;
}

static struct cosmos_ftl_backend backend(void) {
    const struct cosmos_ftl_backend value = {
        .context = &media,
        .program_data = program_data,
        .copy_data = copy_data,
        .read_page_tag = read_page_tag,
        .erase_block = erase_block,
        .append_journal = append_journal,
        .read_journal = read_journal,
        .trim_journal = trim_journal,
        .journal_capacity = TEST_JOURNAL_COUNT,
        .read_checkpoint_header = read_checkpoint_header,
        .read_checkpoint_data = read_checkpoint_data,
        .write_checkpoint = write_checkpoint
    };
    return value;
}

static void reset_media(void) {
    memset(&media, 0, sizeof(media));
    media.fail_journal_index = ~0ULL;
    media.fail_journal_result = COSMOS_FTL_APPEND_HARD_FAILED;
    media.torn_journal_index = ~0ULL;
}

static int init_ftl(struct cosmos_ftl *ftl, unsigned int *l2p,
                    struct cosmos_ftl_block *blocks) {
    struct cosmos_ftl_backend value = backend();

    return cosmos_ftl_init(
        ftl, &value, l2p, TEST_L2P_COUNT, blocks,
        COSMOS_FTL_BLOCK_COUNT);
}

static int init_ftl_with_journal_capacity(
    struct cosmos_ftl *ftl, unsigned int *l2p,
    struct cosmos_ftl_block *blocks, unsigned long long capacity) {
    struct cosmos_ftl_backend value = backend();

    value.journal_capacity = capacity;
    return cosmos_ftl_init(
        ftl, &value, l2p, TEST_L2P_COUNT, blocks,
        COSMOS_FTL_BLOCK_COUNT);
}

static int test_ppa_codec_and_crc(void) {
    unsigned int ppa;
    unsigned int die;
    unsigned int lun;
    unsigned int block;
    unsigned int page;
    unsigned int channel;
    unsigned int way;
    unsigned int row;

    CHECK(cosmos_ftl_crc32("123456789", 9U) == 0xCBF43926U);
    CHECK(cosmos_ftl_ppa_encode(63U, 1U, 4183U, 127U, &ppa) ==
          COSMOS_OK);
    CHECK(cosmos_ftl_ppa_decode(
              ppa, &die, &lun, &block, &page) == COSMOS_OK);
    CHECK(die == 63U && lun == 1U && block == 4183U && page == 127U);
    CHECK(cosmos_ftl_ppa_encode(9U, 1U, 32U, 2U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_ppa_row(ppa, &channel, &way, &row) == COSMOS_OK);
    CHECK(channel == 1U && way == 1U && row == 0x00202003U);
    CHECK(cosmos_ftl_ppa_decode(
              COSMOS_FTL_PPA_NONE, &die, &lun, &block, &page) ==
          COSMOS_INVALID);
    return 0;
}

static int test_data_before_map_and_journal_recovery(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 3U, &ppa) == COSMOS_OK);
    CHECK(media.program_calls == 1U);
    CHECK(media.journal[0].type == COSMOS_FTL_RECORD_ALLOCATE);
    CHECK(media.journal[1].type == COSMOS_FTL_RECORD_MAP);
    CHECK(cosmos_ftl_lookup(&first, 3U, &ppa) == COSMOS_OK);

    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&recovered, 3U, &ppa) == COSMOS_OK);
    return 0;
}

static int test_program_and_torn_map_leave_no_mapping(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    media.fail_program = 1U;
    CHECK(cosmos_ftl_commit_page(&first, 4U, &ppa) == COSMOS_HW_ERROR);
    CHECK(media.journal_count == 2U);
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&recovered, 4U, &ppa) == COSMOS_UNAVAILABLE);

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    media.fail_journal_index = 1U;
    media.fail_journal_result = COSMOS_FTL_APPEND_NOT_COMMITTED;
    media.fail_journal_once = 1U;
    CHECK(cosmos_ftl_commit_page(&first, 5U, &ppa) == COSMOS_RETRY);
    CHECK(media.program_calls == 1U);
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&recovered, 5U, &ppa) == COSMOS_UNAVAILABLE);
    return 0;
}

static int test_checkpoint_fallback_and_retirement(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int first_ppa;
    unsigned int second_ppa;
    unsigned int index;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 1U, &first_ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 1U, &second_ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&first) == COSMOS_OK);
    media.checkpoint[0].header_crc ^= 1U;
    media.journal_count = media.checkpoint[1].journal_index;

    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&recovered, 1U, &second_ppa) == COSMOS_OK);
    CHECK(second_ppa == first_ppa);

    CHECK(cosmos_ftl_retire_block(&recovered, first_ppa) == COSMOS_RETRY);
    CHECK(cosmos_ftl_ppa_encode(0U, 0U, 33U, 0U, &second_ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_retire_block(&recovered, second_ppa) == COSMOS_OK);
    index = 33U;
    CHECK(recovered.blocks[index].bad == 1U);
    return 0;
}

static int test_corrupt_journal_fails_and_torn_tail_is_consumed(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 6U, &ppa) == COSMOS_OK);
    media.journal[1].crc ^= 1U;
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_HW_ERROR);

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    media.torn_journal_index = 0U;
    media.journal_count = 1U;
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(recovered.journal_index == 1U);
    return 0;
}

static int test_ambiguous_append_is_fail_sticky(void) {
    struct cosmos_ftl ftl;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&ftl, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    media.fail_journal_index = 0U;
    media.fail_journal_result = COSMOS_FTL_APPEND_AMBIGUOUS;
    CHECK(cosmos_ftl_commit_page(&ftl, 7U, &ppa) ==
          COSMOS_COMPLETION_UNCERTAIN);
    CHECK(ftl.fail_sticky == 1U);
    CHECK(cosmos_ftl_commit_page(&ftl, 7U, &ppa) == COSMOS_INVALID);
    return 0;
}

static int test_failed_abandon_is_fail_sticky(void) {
    struct cosmos_ftl ftl;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&ftl, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    media.fail_journal_index = 1U;
    media.fail_journal_result = COSMOS_FTL_APPEND_NOT_COMMITTED;
    CHECK(cosmos_ftl_commit_page(&ftl, 7U, &ppa) == COSMOS_RETRY);
    CHECK(ftl.fail_sticky == 1U);
    CHECK(cosmos_ftl_commit_page(&ftl, 7U, &ppa) == COSMOS_INVALID);
    return 0;
}

static int test_recovery_rejects_nonsequential_allocation(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 7U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_ppa_encode(
              0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN, 1U,
              &media.journal[0].new_ppa) == COSMOS_OK);
    media.journal[0].crc = 0U;
    media.journal[0].crc =
        cosmos_ftl_journal_record_crc(&media.journal[0]);
    media.journal[1].previous_crc = media.journal[0].crc;
    media.journal[1].new_ppa = media.journal[0].new_ppa;
    media.journal[1].crc = 0U;
    media.journal[1].crc =
        cosmos_ftl_journal_record_crc(&media.journal[1]);
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_HW_ERROR);
    return 0;
}

static int test_allocator_preserves_gc_reserve(void) {
    struct cosmos_ftl ftl;
    unsigned int block;
    unsigned int index;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&ftl, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    for (index = 0U; index < COSMOS_FTL_BLOCK_COUNT; ++index) {
        if (ftl.blocks[index].state == COSMOS_FTL_BLOCK_FREE) {
            ftl.blocks[index].state = COSMOS_FTL_BLOCK_RESERVED;
        }
    }
    for (block = COSMOS_FTL_METADATA_BLOCKS_PER_LUN;
         block < COSMOS_FTL_METADATA_BLOCKS_PER_LUN +
             COSMOS_FTL_GC_RESERVE_BLOCKS_PER_LANE; ++block) {
        blocks_a[block].state = COSMOS_FTL_BLOCK_FREE;
    }
    CHECK(cosmos_ftl_commit_page(&ftl, 9U, &ppa) == COSMOS_UNAVAILABLE);
    return 0;
}

static int test_gc_relocates_before_erase(void) {
    struct cosmos_ftl ftl;
    unsigned int destination;
    unsigned int source;
    unsigned int victim = COSMOS_FTL_METADATA_BLOCKS_PER_LUN;

    reset_media();
    CHECK(init_ftl(&ftl, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    CHECK(cosmos_ftl_ppa_encode(
              0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN, 0U,
              &source) == COSMOS_OK);
    blocks_a[victim].state = COSMOS_FTL_BLOCK_CLOSED;
    blocks_a[victim].next_page = 2U;
    blocks_a[victim].valid_pages = 1U;
    l2p_a[2] = source;
    media.page[0].ppa = source;
    media.page[0].lpn = 2U;
    media.page[0].generation = 1U;
    media.page[0].valid = 1U;
    media.program_calls = 1U;

    CHECK(cosmos_ftl_gc_step(&ftl, 1U) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&ftl, 2U, &destination) == COSMOS_OK);
    CHECK(destination != source);
    CHECK(blocks_a[victim].valid_pages == 0U);
    CHECK(media.erase_calls == 0U);

    CHECK(cosmos_ftl_gc_step(&ftl, 1U) == COSMOS_OK);
    CHECK(media.erase_calls == 1U);
    CHECK(blocks_a[victim].state == COSMOS_FTL_BLOCK_FREE);
    CHECK(blocks_a[victim].erase_count == 1U);
    CHECK(media.journal[0].type == COSMOS_FTL_RECORD_ALLOCATE);
    CHECK(media.journal[1].type == COSMOS_FTL_RECORD_MAP);
    CHECK(media.journal[2].type == COSMOS_FTL_RECORD_ERASE_BEGIN);
    CHECK(media.journal[3].type == COSMOS_FTL_RECORD_ERASE_DONE);
    return 0;
}

static int test_erase_failure_retires_and_recovers(void) {
    struct cosmos_ftl ftl;
    struct cosmos_ftl recovered;
    unsigned int victim = COSMOS_FTL_METADATA_BLOCKS_PER_LUN;

    reset_media();
    CHECK(init_ftl(&ftl, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    blocks_a[victim].state = COSMOS_FTL_BLOCK_CLOSED;
    blocks_a[victim].next_page = 1U;
    ftl.generation = 1U;
    CHECK(cosmos_ftl_flush(&ftl) == COSMOS_OK);
    media.fail_erase = 1U;
    CHECK(cosmos_ftl_gc_step(&ftl, 1U) == COSMOS_HW_ERROR);
    CHECK(ftl.fail_sticky == 0U);
    CHECK(blocks_a[victim].state == COSMOS_FTL_BLOCK_RETIRED);
    CHECK(blocks_a[victim].bad == 1U);

    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(blocks_b[victim].state == COSMOS_FTL_BLOCK_RETIRED);
    CHECK(blocks_b[victim].bad == 1U);
    return 0;
}

static int test_journal_reclaims_only_checkpointed_records(void) {
    struct cosmos_ftl ftl;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl_with_journal_capacity(
              &ftl, l2p_a, blocks_a, 6ULL) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&ftl, 0U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&ftl) == COSMOS_OK);
    CHECK(media.journal_first_index == 0ULL);
    CHECK(cosmos_ftl_commit_page(&ftl, 1U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&ftl) == COSMOS_OK);
    CHECK(media.journal_first_index == 2ULL);
    CHECK(cosmos_ftl_commit_page(&ftl, 2U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&ftl) == COSMOS_OK);
    CHECK(media.journal_first_index == 4ULL);
    CHECK(media.trim_calls == 3U);

    reset_media();
    CHECK(init_ftl_with_journal_capacity(
              &ftl, l2p_a, blocks_a, 3ULL) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&ftl, 0U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&ftl, 1U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&ftl, 2U, &ppa) ==
          COSMOS_UNAVAILABLE);
    return 0;
}

static int test_transaction_reservation_and_torn_hole_recovery(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl_with_journal_capacity(
              &first, l2p_a, blocks_a, 2ULL) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 0U, &ppa) ==
          COSMOS_UNAVAILABLE);
    CHECK(media.journal_count == 0ULL);
    CHECK(media.program_calls == 0U);

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 0U, &ppa) == COSMOS_OK);
    media.journal_count = 1ULL;
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(media.journal[1].type == COSMOS_FTL_RECORD_ABANDON);
    CHECK(recovered.journal_index == 2ULL);
    CHECK(cosmos_ftl_commit_page(&recovered, 1U, &ppa) == COSMOS_OK);

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 0U, &ppa) == COSMOS_OK);
    media.torn_journal_index = 2ULL;
    media.journal_count = 3ULL;
    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(recovered.journal_index == 3ULL);
    CHECK(cosmos_ftl_commit_page(&recovered, 1U, &ppa) == COSMOS_OK);
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&first, 1U, &ppa) == COSMOS_OK);
    return 0;
}

static int test_discard_is_durable(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int block_index;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 3U, &ppa) == COSMOS_OK);
    block_index = (ppa >> 7U) & 0x1FFFU;
    CHECK(blocks_a[block_index].valid_pages == 1U);
    CHECK(cosmos_ftl_discard_page(&first, 3U) == COSMOS_OK);
    CHECK(blocks_a[block_index].valid_pages == 0U);
    CHECK(cosmos_ftl_lookup(&first, 3U, &ppa) == COSMOS_UNAVAILABLE);
    CHECK(cosmos_ftl_flush(&first) == COSMOS_OK);

    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&recovered, 3U, &ppa) == COSMOS_UNAVAILABLE);
    CHECK(cosmos_ftl_discard_page(&recovered, 3U) == COSMOS_OK);
    return 0;
}

static int test_recovery_rebuilds_checkpoint_trim_state(void) {
    struct cosmos_ftl first;
    struct cosmos_ftl recovered;
    unsigned int ppa;

    reset_media();
    CHECK(init_ftl(&first, l2p_a, blocks_a) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 0U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&first) == COSMOS_OK);
    CHECK(cosmos_ftl_commit_page(&first, 1U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&first) == COSMOS_OK);
    CHECK(media.journal_first_index == 2ULL);
    media.checkpoint[0].header_crc ^= 1U;

    CHECK(init_ftl(&recovered, l2p_b, blocks_b) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&recovered) == COSMOS_OK);
    CHECK(media.journal_first_index == 2ULL);
    CHECK(cosmos_ftl_commit_page(&recovered, 2U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_flush(&recovered) == COSMOS_OK);
    CHECK(media.journal_first_index == 4ULL);
    return 0;
}

int main(void) {
    CHECK(sizeof(struct cosmos_ftl_block) == 8U);
    CHECK(COSMOS_FTL_L2P_ENTRY_COUNT == 66584576U);
    CHECK(COSMOS_FTL_NAMESPACE_PAGE_COUNT == 59865600U);
    CHECK(COSMOS_FTL_NAMESPACE_BLOCK_COUNT == 239462400U);
#ifdef COSMOS_FTL_GC_ONLY
    CHECK(test_gc_relocates_before_erase() == 0);
    puts("cosmos FTL GC contract: PASS");
#elif defined(COSMOS_FTL_ERASE_FAILURE_ONLY)
    CHECK(test_erase_failure_retires_and_recovers() == 0);
    puts("cosmos FTL erase-failure contract: PASS");
#elif defined(COSMOS_FTL_JOURNAL_RECLAIM_ONLY)
    CHECK(test_journal_reclaims_only_checkpointed_records() == 0);
    puts("cosmos FTL journal reclaim contract: PASS");
#elif defined(COSMOS_FTL_DISCARD_ONLY)
    CHECK(test_discard_is_durable() == 0);
    puts("cosmos FTL discard contract: PASS");
#elif defined(COSMOS_FTL_RECOVERY_TRIM_ONLY)
    CHECK(test_recovery_rebuilds_checkpoint_trim_state() == 0);
    puts("cosmos FTL recovery trim contract: PASS");
#elif defined(COSMOS_FTL_TRANSACTION_RECOVERY_ONLY)
    CHECK(test_transaction_reservation_and_torn_hole_recovery() == 0);
    puts("cosmos FTL transaction recovery contract: PASS");
#else
    CHECK(test_ppa_codec_and_crc() == 0);
    CHECK(test_data_before_map_and_journal_recovery() == 0);
    CHECK(test_program_and_torn_map_leave_no_mapping() == 0);
    CHECK(test_checkpoint_fallback_and_retirement() == 0);
    CHECK(test_corrupt_journal_fails_and_torn_tail_is_consumed() == 0);
    CHECK(test_ambiguous_append_is_fail_sticky() == 0);
    CHECK(test_failed_abandon_is_fail_sticky() == 0);
    CHECK(test_recovery_rejects_nonsequential_allocation() == 0);
    CHECK(test_allocator_preserves_gc_reserve() == 0);
    puts("cosmos FTL contract: PASS");
#endif
    return 0;
}
