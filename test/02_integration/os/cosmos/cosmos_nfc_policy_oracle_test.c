/* Independent frozen-C oracle for the pre-migration Cosmos NFC policy.
 * This file intentionally does not include cosmos_nfc_regs.h. */
#include <stdio.h>
#include <stdlib.h>

#include "cosmos_nfc_policy.h"

#define ORACLE_OK 0
#define ORACLE_UNAVAILABLE 1
#define ORACLE_INVALID 2
#define ORACLE_TIMEOUT 3
#define ORACLE_HW_ERROR 4
#define ORACLE_RETRY 5

#define ORACLE_CHANNEL0_BASE 0x43C00000U
#define ORACLE_CHANNEL_STRIDE 0x00010000U
#define ORACLE_CHANNEL_COUNT 8U
#define ORACLE_WAY_COUNT 8U
#define ORACLE_MAX_OWNED_RANGES 5U
#define ORACLE_ROWS_PER_BLOCK 256U
#define ORACLE_LUN1_BASE_ROW 0x00200000U
#define ORACLE_ROWS_PER_LUN 0x00105800U

#define ORACLE_PAGE_DATA_BYTES 16384U
#define ORACLE_PAGE_SPARE_BYTES 256U
#define ORACLE_RAW_ROW_BYTES 18048U
#define ORACLE_ERROR_INFO_BYTES 44U
#define ORACLE_DATA_POOL_BASE 0x10000000U
#define ORACLE_DATA_POOL_END 0x110FFFFFU
#define ORACLE_SPARE_POOL_BASE 0x11100000U
#define ORACLE_SPARE_POOL_END 0x11143FFFU
#define ORACLE_COMPLETION_POOL_BASE 0x17000000U
#define ORACLE_COMPLETION_POOL_END 0x170000FFU
#define ORACLE_STATUS_POOL_BASE 0x17000100U
#define ORACLE_STATUS_POOL_END 0x170001FFU
#define ORACLE_ERROR_POOL_BASE 0x17000200U
#define ORACLE_ERROR_POOL_END 0x17000CFFU
#define ORACLE_TOGGLE_POOL_BASE 0x17000D00U
#define ORACLE_TOGGLE_POOL_END 0x17001CFFU

#define ORACLE_STATUS_REPORT_DONE 0x1U
#define ORACLE_STATUS_COMPLETE_MASK 0x60U
#define ORACLE_STATUS_FAIL_MASK 0x03U
#define ORACLE_TRANSFER_COMPLETE 0xA5000001U

static unsigned long oracle_cases;

static void check_int(const char *name, int expected, int actual) {
    oracle_cases++;
    if (expected != actual) {
        (void)fprintf(stderr, "%s: expected %d, got %d\n",
                      name, expected, actual);
        exit(1);
    }
}

static void check_uint(const char *name, unsigned int expected,
                       unsigned int actual) {
    oracle_cases++;
    if (expected != actual) {
        (void)fprintf(stderr, "%s: expected 0x%08x, got 0x%08x\n",
                      name, expected, actual);
        exit(1);
    }
}

static unsigned int oracle_channel_base(unsigned int channel) {
    return ORACLE_CHANNEL0_BASE + channel * ORACLE_CHANNEL_STRIDE;
}

static int oracle_row_valid(unsigned int row_address) {
    return row_address < ORACLE_ROWS_PER_LUN ||
        (row_address >= ORACLE_LUN1_BASE_ROW &&
         row_address < ORACLE_LUN1_BASE_ROW + ORACLE_ROWS_PER_LUN);
}

static int oracle_target_valid(unsigned int channel, unsigned int way,
                               unsigned int row_address) {
    return channel < ORACLE_CHANNEL_COUNT && way < ORACLE_WAY_COUNT &&
        oracle_row_valid(row_address);
}

static int oracle_erase_row_valid(unsigned int row_address) {
    unsigned int lun_row;
    if (!oracle_row_valid(row_address)) {
        return 0;
    }
    lun_row = row_address >= ORACLE_LUN1_BASE_ROW ?
        row_address - ORACLE_LUN1_BASE_ROW : row_address;
    return (lun_row % ORACLE_ROWS_PER_BLOCK) == 0U;
}

static int oracle_range_valid(unsigned int address, unsigned int size,
                              unsigned int base, unsigned int end,
                              unsigned int stride,
                              unsigned int contract_bound) {
    if (!contract_bound || size == 0U || stride == 0U || address < base ||
        address > end || ((address - base) % stride) != 0U) {
        return 0;
    }
    return size - 1U <= end - address;
}

static int oracle_data_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, ORACLE_PAGE_DATA_BYTES,
                              ORACLE_DATA_POOL_BASE, ORACLE_DATA_POOL_END,
                              ORACLE_PAGE_DATA_BYTES, bound);
}

static int oracle_raw_data_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, ORACLE_RAW_ROW_BYTES,
                              ORACLE_DATA_POOL_BASE, ORACLE_DATA_POOL_END,
                              ORACLE_PAGE_DATA_BYTES, bound);
}

static int oracle_spare_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, ORACLE_PAGE_SPARE_BYTES,
                              ORACLE_SPARE_POOL_BASE, ORACLE_SPARE_POOL_END,
                              ORACLE_PAGE_SPARE_BYTES, bound);
}

static int oracle_completion_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, 4U, ORACLE_COMPLETION_POOL_BASE,
                              ORACLE_COMPLETION_POOL_END, 4U, bound);
}

static int oracle_status_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, 4U, ORACLE_STATUS_POOL_BASE,
                              ORACLE_STATUS_POOL_END, 4U, bound);
}

static int oracle_error_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, ORACLE_ERROR_INFO_BYTES,
                              ORACLE_ERROR_POOL_BASE, ORACLE_ERROR_POOL_END,
                              ORACLE_ERROR_INFO_BYTES, bound);
}

static int oracle_toggle_valid(unsigned int address, unsigned int bound) {
    return oracle_range_valid(address, 12U, ORACLE_TOGGLE_POOL_BASE,
                              ORACLE_TOGGLE_POOL_END, 4U, bound);
}

static int oracle_overlap(unsigned int first, unsigned int first_size,
                          unsigned int second, unsigned int second_size) {
    return first < second ? second - first < first_size :
        first - second < second_size;
}

static int oracle_reserve_args(unsigned int channel,
                               unsigned int ranges_present,
                               unsigned int count) {
    return channel < ORACLE_CHANNEL_COUNT && ranges_present != 0U &&
        count != 0U && count <= ORACLE_MAX_OWNED_RANGES;
}

static int oracle_decode_status(unsigned int raw_report) {
    unsigned int status;
    if ((raw_report & ORACLE_STATUS_REPORT_DONE) == 0U) {
        return ORACLE_INVALID;
    }
    status = raw_report >> 1U;
    if ((status & ORACLE_STATUS_COMPLETE_MASK) !=
        ORACLE_STATUS_COMPLETE_MASK) {
        return ORACLE_UNAVAILABLE;
    }
    return (status & ORACLE_STATUS_FAIL_MASK) == 0U ?
        ORACLE_OK : ORACLE_HW_ERROR;
}

static int oracle_io_valid(int target_valid, int data_valid, int spare_valid,
                           int status_valid, int read, int error_valid,
                           int completion_valid) {
    if (!target_valid || !data_valid || !spare_valid || !status_valid) {
        return 0;
    }
    return !read || (error_valid && completion_valid);
}

static int oracle_raw_io_valid(int target_valid, int data_valid,
                               int completion_valid, int status_valid) {
    return target_valid && data_valid && completion_valid && status_valid;
}

static int oracle_raw_completion(unsigned int completion_word) {
    if (completion_word == ORACLE_TRANSFER_COMPLETE) {
        return ORACLE_OK;
    }
    return completion_word == 0U ? ORACLE_TIMEOUT : ORACLE_HW_ERROR;
}

static unsigned int oracle_toggle_payload(unsigned int index) {
    static const unsigned int payload[3] = {6U, 8U, 32U};
    return index < 3U ? payload[index] : 0U;
}

static void check_address_and_target_policy(void) {
    static const unsigned int rows[] = {
        0U, 1U, 255U, 256U, 0x00105700U, 0x001057FFU,
        0x00105800U, 0x001FFFFFU, 0x00200000U, 0x00200001U,
        0x00305700U, 0x003057FFU, 0x00305800U, 0xFFFFFFFFU
    };
    unsigned int channel;
    unsigned int way;
    unsigned int row_index;
    for (channel = 0U; channel < 10U; channel++) {
        check_uint("channel-base", oracle_channel_base(channel),
                   cosmos_nfc_policy_channel_base(channel));
    }
    for (row_index = 0U; row_index < sizeof(rows) / sizeof(rows[0]);
         row_index++) {
        check_int("row-valid", oracle_row_valid(rows[row_index]),
                  cosmos_nfc_policy_row_valid(rows[row_index]));
        check_int("erase-row-valid", oracle_erase_row_valid(rows[row_index]),
                  cosmos_nfc_policy_erase_row_valid(rows[row_index]));
    }
    for (channel = 0U; channel < 10U; channel++) {
        for (way = 0U; way < 10U; way++) {
            for (row_index = 0U;
                 row_index < sizeof(rows) / sizeof(rows[0]); row_index++) {
                check_int("target-valid",
                          oracle_target_valid(channel, way, rows[row_index]),
                          cosmos_nfc_policy_target_valid(
                              channel, way, rows[row_index]));
            }
        }
    }
}

static void check_dma_policy(void) {
    static const unsigned int addresses[] = {
        0U, 0x0FFCU, 0x1000U, 0x1001U, 0x1004U,
        0x10F8U, 0x10FCU, 0x10FFU, 0x1100U, 0xFFFFFFFFU
    };
    static const unsigned int sizes[] = {0U, 1U, 4U, 5U, 16U, 256U};
    static const unsigned int strides[] = {0U, 1U, 4U, 16U, 256U};
    static const unsigned int pool_addresses[] = {
        ORACLE_DATA_POOL_BASE, ORACLE_DATA_POOL_BASE + 4U,
        ORACLE_DATA_POOL_END - ORACLE_PAGE_DATA_BYTES + 1U,
        ORACLE_DATA_POOL_END,
        ORACLE_SPARE_POOL_BASE, ORACLE_SPARE_POOL_BASE + 4U,
        ORACLE_SPARE_POOL_END - ORACLE_PAGE_SPARE_BYTES + 1U,
        ORACLE_COMPLETION_POOL_BASE, ORACLE_COMPLETION_POOL_END - 3U,
        ORACLE_STATUS_POOL_BASE, ORACLE_STATUS_POOL_END - 3U,
        ORACLE_ERROR_POOL_BASE, ORACLE_ERROR_POOL_BASE + 4U,
        ORACLE_ERROR_POOL_END - ORACLE_ERROR_INFO_BYTES + 1U,
        ORACLE_TOGGLE_POOL_BASE, ORACLE_TOGGLE_POOL_BASE + 4U,
        ORACLE_TOGGLE_POOL_END - 11U, 0xFFFFFFFFU
    };
    unsigned int address_index;
    unsigned int size_index;
    unsigned int stride_index;
    unsigned int bound;
    for (bound = 0U; bound < 2U; bound++) {
        for (address_index = 0U;
             address_index < sizeof(addresses) / sizeof(addresses[0]);
             address_index++) {
            for (size_index = 0U;
                 size_index < sizeof(sizes) / sizeof(sizes[0]); size_index++) {
                for (stride_index = 0U;
                     stride_index < sizeof(strides) / sizeof(strides[0]);
                     stride_index++) {
                    check_int("range-valid",
                              oracle_range_valid(
                                  addresses[address_index], sizes[size_index],
                                  0x1000U, 0x10FFU,
                                  strides[stride_index], bound),
                              cosmos_nfc_policy_dma_range_valid(
                                  addresses[address_index], sizes[size_index],
                                  0x1000U, 0x10FFU,
                                  strides[stride_index], bound));
                }
            }
        }
        for (address_index = 0U;
             address_index <
                sizeof(pool_addresses) / sizeof(pool_addresses[0]);
             address_index++) {
            unsigned int address = pool_addresses[address_index];
            check_int("data-valid", oracle_data_valid(address, bound),
                      cosmos_nfc_policy_data_valid(address, bound));
            check_int("raw-data-valid", oracle_raw_data_valid(address, bound),
                      cosmos_nfc_policy_raw_data_valid(address, bound));
            check_int("spare-valid", oracle_spare_valid(address, bound),
                      cosmos_nfc_policy_spare_valid(address, bound));
            check_int("completion-valid",
                      oracle_completion_valid(address, bound),
                      cosmos_nfc_policy_completion_valid(address, bound));
            check_int("status-valid", oracle_status_valid(address, bound),
                      cosmos_nfc_policy_status_report_valid(address, bound));
            check_int("error-valid", oracle_error_valid(address, bound),
                      cosmos_nfc_policy_error_info_valid(address, bound));
            check_int("toggle-valid", oracle_toggle_valid(address, bound),
                      cosmos_nfc_policy_toggle_valid(address, bound));
        }
    }
}

static void check_ownership_policy(void) {
    static const unsigned int points[] = {0U, 1U, 3U, 4U, 7U, 8U, 16U};
    static const unsigned int sizes[] = {0U, 1U, 4U, 8U, 16U};
    unsigned int first;
    unsigned int second;
    unsigned int first_size;
    unsigned int second_size;
    unsigned int channel;
    unsigned int present;
    unsigned int count;
    int status;
    for (first = 0U; first < sizeof(points) / sizeof(points[0]); first++) {
        for (second = 0U; second < sizeof(points) / sizeof(points[0]);
             second++) {
            for (first_size = 0U;
                 first_size < sizeof(sizes) / sizeof(sizes[0]); first_size++) {
                for (second_size = 0U;
                     second_size < sizeof(sizes) / sizeof(sizes[0]);
                     second_size++) {
                    check_int("range-overlap",
                              oracle_overlap(
                                  points[first], sizes[first_size],
                                  points[second], sizes[second_size]),
                              cosmos_nfc_policy_ranges_overlap(
                                  points[first], sizes[first_size],
                                  points[second], sizes[second_size]));
                }
            }
        }
    }
    for (channel = 0U; channel < 10U; channel++) {
        for (present = 0U; present < 3U; present++) {
            for (count = 0U; count < 8U; count++) {
                check_int("reserve-args",
                          oracle_reserve_args(channel, present, count),
                          cosmos_nfc_policy_dma_reserve_args_valid(
                              channel, present, count));
            }
        }
    }
    for (status = -1; status <= 7; status++) {
        check_int("finish-release", status == ORACLE_TIMEOUT ? 0 : 1,
                  cosmos_nfc_policy_dma_finish_releases(status));
        check_int("result-fault", status == ORACLE_TIMEOUT ? 1 : 0,
                  cosmos_nfc_policy_channel_result_faults(status));
    }
}

static void check_status_and_io_policy(void) {
    unsigned int raw_report;
    unsigned int bits;
    for (raw_report = 0U; raw_report < 512U; raw_report++) {
        check_uint("nand-status", raw_report >> 1U,
                   cosmos_nfc_policy_nand_status(raw_report));
        check_int("decode-status", oracle_decode_status(raw_report),
                  cosmos_nfc_policy_decode_status(raw_report));
    }
    for (bits = 0U; bits < 128U; bits++) {
        int target = (int)((bits >> 0U) & 1U);
        int data = (int)((bits >> 1U) & 1U);
        int spare = (int)((bits >> 2U) & 1U);
        int status = (int)((bits >> 3U) & 1U);
        int read = (int)((bits >> 4U) & 1U);
        int error = (int)((bits >> 5U) & 1U);
        int completion = (int)((bits >> 6U) & 1U);
        check_int("io-valid",
                  oracle_io_valid(target, data, spare, status, read,
                                  error, completion),
                  cosmos_nfc_policy_io_valid(target, data, spare, status,
                                             read, error, completion));
    }
    for (bits = 0U; bits < 16U; bits++) {
        int target = (int)((bits >> 0U) & 1U);
        int data = (int)((bits >> 1U) & 1U);
        int completion = (int)((bits >> 2U) & 1U);
        int status = (int)((bits >> 3U) & 1U);
        check_int("raw-io-valid",
                  oracle_raw_io_valid(target, data, completion, status),
                  cosmos_nfc_policy_raw_io_valid(
                      target, data, completion, status));
    }
}

static void check_operation_state_policy(void) {
    static const unsigned int completion_words[] = {
        0U, 1U, 2U, ORACLE_TRANSFER_COMPLETE, 0xFFFFFFFFU
    };
    unsigned int initialized;
    unsigned int failed;
    unsigned int faulted;
    unsigned int index;
    int status;
    for (initialized = 0U; initialized < 3U; initialized++) {
        check_int("initialized-status",
                  initialized != 0U ? ORACLE_OK : ORACLE_UNAVAILABLE,
                  cosmos_nfc_policy_initialized_status(initialized));
    }
    for (status = 0; status <= 6; status++) {
        check_int("contract-status",
                  status == ORACLE_OK ? ORACLE_OK : ORACLE_UNAVAILABLE,
                  cosmos_nfc_policy_contract_status(status));
        check_int("init-selftest-status",
                  status == ORACLE_OK ? ORACLE_OK : ORACLE_INVALID,
                  cosmos_nfc_policy_init_selftest_status(status));
        check_int("init-contract-status", status,
                  cosmos_nfc_policy_init_contract_status(status));
        for (faulted = 0U; faulted < 3U; faulted++) {
            check_int("locked-status",
                      faulted != 0U || status != ORACLE_OK ?
                          ORACLE_HW_ERROR : ORACLE_OK,
                      cosmos_nfc_policy_locked_channel_status(
                          faulted, status));
        }
    }
    for (initialized = 0U; initialized < 3U; initialized++) {
        for (failed = 0U; failed < 3U; failed++) {
            int expected = initialized != 0U ? ORACLE_OK :
                (failed != 0U ? ORACLE_HW_ERROR : ORACLE_RETRY);
            check_int("init-state-status", expected,
                      cosmos_nfc_policy_init_state_status(
                          initialized, failed));
        }
    }
    for (index = 0U;
         index < sizeof(completion_words) / sizeof(completion_words[0]);
         index++) {
        check_int("raw-completion",
                  oracle_raw_completion(completion_words[index]),
                  cosmos_nfc_policy_raw_completion_status(
                      completion_words[index]));
    }
    for (index = 0U; index < 5U; index++) {
        check_uint("toggle-payload", oracle_toggle_payload(index),
                   cosmos_nfc_policy_toggle_payload_word(index));
    }
}

int main(void) {
    check_address_and_target_policy();
    check_dma_policy();
    check_ownership_policy();
    check_status_and_io_policy();
    check_operation_state_policy();
    (void)printf("COSMOS_NFC_POLICY_C_ORACLE_CASES %lu\n", oracle_cases);
    return 0;
}
