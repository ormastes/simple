#include <stdint.h>
#include <stdio.h>

#include "cosmos_pcie_residual_policy.h"
#include "cosmos_pcie_residual_policy_oracle.h"

#define CHECK_EQ(actual, expected)                                           \
    do {                                                                     \
        unsigned long long actual_value = (unsigned long long)(actual);      \
        unsigned long long expected_value = (unsigned long long)(expected);  \
        if (actual_value != expected_value) {                                \
            fprintf(stderr, "%s:%d: got %llu expected %llu\n",             \
                    __FILE__, __LINE__, actual_value, expected_value);       \
            return 1;                                                        \
        }                                                                    \
    } while (0)

static int check_snapshot_vectors(void) {
    static const unsigned int vectors[][4] = {
        {0x116U, 0x33U, 0U, 0U},
        {0x80000116U, 0x33U, 0U, 0U},
        {0U, 0x33U, 0U, 0U},
        {0x116U, 0x37U, 0U, 0U},
        {0x116U, 0x43U, 0U, 0U},
        {0x116U, 0x33U, 1U, 2U},
        {0x116U, 0x33U, 1U, 4U},
        {0x116U, 0x33U, 0U, 3U},
        {0x116U, 0x33U, 0x11U, 7U},
        {0x116U, 0x33U, 0x11U, 0U}
    };
    unsigned int index;

    for (index = 0U; index < sizeof(vectors) / sizeof(vectors[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_snapshot_status(
                     vectors[index][0], vectors[index][1],
                     vectors[index][2], vectors[index][3]),
                 cosmos_pcie_residual_oracle_snapshot_status(
                     vectors[index][0], vectors[index][1],
                     vectors[index][2], vectors[index][3]));
    }
    CHECK_EQ(cosmos_pcie_residual_policy_snapshots_equal(
                 1U, 2U, 3U, 4U, 1U, 2U, 3U, 4U),
             cosmos_pcie_residual_oracle_snapshots_equal(
                 1U, 2U, 3U, 4U, 1U, 2U, 3U, 4U));
    CHECK_EQ(cosmos_pcie_residual_policy_snapshots_equal(
                 1U, 2U, 3U, 4U, 1U, 2U, 3U, 5U),
             cosmos_pcie_residual_oracle_snapshots_equal(
                 1U, 2U, 3U, 4U, 1U, 2U, 3U, 5U));
    return 0;
}

static int check_command_and_completion_vectors(void) {
    static const unsigned int commands[] = {
        0U, 0x80000010U, 0x80000000U, 0x80000008U,
        0x80000009U, 0x80FF7F08U
    };
    static const unsigned int completions[][5] = {
        {0U, 0U, 0U, 0U, 0U}, {8U, 127U, 255U, 65535U, 0x8E00U},
        {9U, 0U, 0U, 0U, 0U}, {0U, 128U, 0U, 0U, 0U},
        {0U, 0U, 256U, 0U, 0U}, {0U, 0U, 0U, 65536U, 0U},
        {0U, 0U, 0U, 0U, 65536U}, {0U, 0U, 0U, 0U, 1U}
    };
    unsigned int index;

    for (index = 0U; index < sizeof(commands) / sizeof(commands[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_nvme_cmd_word_status(
                     commands[index]),
                 cosmos_pcie_residual_oracle_nvme_cmd_word_status(
                     commands[index]));
    }
    for (index = 0U;
         index < sizeof(completions) / sizeof(completions[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_nvme_completion_fields_valid(
                     completions[index][0], completions[index][1],
                     completions[index][2], completions[index][3],
                     completions[index][4]),
                 cosmos_pcie_residual_oracle_nvme_completion_fields_valid(
                     completions[index][0], completions[index][1],
                     completions[index][2], completions[index][3],
                     completions[index][4]));
    }
    return 0;
}

static int check_dma_vectors(void) {
    static const unsigned int buffers[][2] = {
        {0x10000000U, 4U}, {0x110FFFFCU, 4U}, {0x10000001U, 4U},
        {0x10000000U, 0U}, {0x10000000U, 0x1004U},
        {0x10000000U, 2U}, {0x0FFFFFFCU, 4U},
        {0x11100000U, 4U}, {0x110FFFFCU, 8U}
    };
    static const unsigned int directs[][4] = {
        {0x10000000U, 0U, 0U, 4U},
        {0x10000000U, 0U, 1U, 4U},
        {0x10000000U, 16U, 0U, 4U},
        {0x10000000U, 15U, 0xFFFFFFF0U, 16U},
        {0x10000000U, 14U, 0xFFFFFFF0U, 16U},
        {0x0FFFFFFCU, 0U, 0U, 4U}
    };
    static const unsigned int autos[][3] = {
        {0U, 0U, 0x10000000U}, {127U, 255U, 0x10000000U},
        {128U, 0U, 0x10000000U}, {0U, 256U, 0x10000000U},
        {0U, 0U, 0x0FFFFFFCU}
    };
    unsigned int direct;
    unsigned int direction;
    unsigned int index;

    for (index = 0U; index < sizeof(buffers) / sizeof(buffers[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_host_dma_device_buffer_status(
                     buffers[index][0], buffers[index][1]),
                 cosmos_pcie_residual_oracle_host_dma_device_buffer_status(
                     buffers[index][0], buffers[index][1]));
    }
    for (index = 0U; index < sizeof(directs) / sizeof(directs[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_host_dma_direct_status(
                     directs[index][0], directs[index][1],
                     directs[index][2], directs[index][3]),
                 cosmos_pcie_residual_oracle_host_dma_direct_status(
                     directs[index][0], directs[index][1],
                     directs[index][2], directs[index][3]));
    }
    for (direct = 0U; direct < 3U; ++direct) {
        for (direction = 0U; direction < 3U; ++direction) {
            CHECK_EQ(cosmos_pcie_residual_policy_host_dma_counter_shift(
                         direct, direction),
                     cosmos_pcie_residual_oracle_host_dma_counter_shift(
                         direct, direction));
            CHECK_EQ(cosmos_pcie_residual_policy_host_dma_counter_index(
                         direct, direction),
                     cosmos_pcie_residual_oracle_host_dma_counter_index(
                         direct, direction));
            CHECK_EQ(cosmos_pcie_residual_policy_host_dma_direct_word3(
                         direction, 0x1000U),
                     cosmos_pcie_residual_oracle_host_dma_direct_word3(
                         direction, 0x1000U));
            CHECK_EQ(cosmos_pcie_residual_policy_host_dma_auto_word3(
                         direction, 127U, 255U),
                     cosmos_pcie_residual_oracle_host_dma_auto_word3(
                         direction, 127U, 255U));
        }
    }
    for (index = 0U; index < sizeof(autos) / sizeof(autos[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_host_dma_auto_status(
                     autos[index][0], autos[index][1], autos[index][2]),
                 cosmos_pcie_residual_oracle_host_dma_auto_status(
                     autos[index][0], autos[index][1], autos[index][2]));
    }
    return 0;
}

static int check_completion_words(void) {
    static const unsigned int vectors[][2] = {
        {0U, 0U}, {127U, 0x8E00U}, {255U, 0x12345U}
    };
    unsigned int index;

    for (index = 0U; index < sizeof(vectors) / sizeof(vectors[0]); ++index) {
        CHECK_EQ(cosmos_pcie_residual_policy_nvme_completion_word2(
                     vectors[index][0], vectors[index][1]),
                 cosmos_pcie_residual_oracle_nvme_completion_word2(
                     vectors[index][0], vectors[index][1]));
    }
    return 0;
}

int main(void) {
    unsigned int mask_low;
    unsigned int mask_high;
    unsigned int required_low;
    unsigned int required_high;

    cosmos_pcie_residual_policy_coverage_reset();
    CHECK_EQ(check_snapshot_vectors(), 0);
    CHECK_EQ(check_command_and_completion_vectors(), 0);
    CHECK_EQ(check_dma_vectors(), 0);
    CHECK_EQ(check_completion_words(), 0);

    mask_low = cosmos_pcie_residual_policy_coverage_mask(0U);
    mask_high = cosmos_pcie_residual_policy_coverage_mask(1U);
    required_low = cosmos_pcie_residual_policy_coverage_required(0U);
    required_high = cosmos_pcie_residual_policy_coverage_required(1U);
    CHECK_EQ(cosmos_pcie_residual_policy_function_count(), 12U);
    CHECK_EQ(cosmos_pcie_residual_policy_coverage_decisions(), 19U);
    CHECK_EQ(mask_low, required_low);
    CHECK_EQ(mask_high, required_high);
    CHECK_EQ(required_low, UINT32_C(0xFFFFFFFF));
    CHECK_EQ(required_high, UINT32_C(0x0000003F));

    printf("COSMOS_PCIE_RESIDUAL_ORACLE_FUNCTIONS 12/12\n");
    printf("COSMOS_PCIE_RESIDUAL_SIMPLE_DECISIONS 19/19\n");
    printf("COSMOS_PCIE_RESIDUAL_SIMPLE_OUTCOMES 38/38\n");
    return 0;
}
